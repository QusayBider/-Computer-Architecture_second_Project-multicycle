`define  IF 3'b000  //Fetch 
`define  ID 3'b001	//Decode  
`define  EX 3'b010	//Execute
`define  MEM 3'b011	//Memory
`define  WB 3'b100	//WriteBack	


module MultiCycleProcessor_tb;

    // Declare inputs as reg
    reg clk;
    reg reset;

    // Declare outputs as wire
    wire zeroFlag;
    wire overflowFlag;
    wire negativeFlag;
    wire signed [15:0] ALUOut;
    wire signed [15:0] dataOut;
    wire signed [15:0] Bus_W;
    wire Total_number_of_executed_instructions,Total_number_of_load_instructions,Total_number_of_store_instructions,Total_number_of_ALU_instructions,Total_number_of_control_instructions;
    // Instantiate the MultiCycleProcessor module
    MultiCycleProcessor uut (
        .clk(clk),
        .reset(reset),
        .zeroFlag(zeroFlag),
        .overflowFlag(overflowFlag),
        .negativeFlag(negativeFlag),
        .ALUOut(ALUOut),
        .dataOut(dataOut),
        .Bus_W(Bus_W)
    );

    // Clock generation
    always begin
        #5 clk = ~clk;  // Toggle clock every 5 time units
    end

    // Initial block for test stimulus
    initial begin
        // Initialize clock and reset
        clk = 0;
        reset = 0;

        // Apply reset to initialize the processor
        reset = 1;
        #10;
        reset = 0;		

        // Test 1: Load a program and check the fetch-decode-execute process
        // Provide instructions through memory or predefined values (can modify input.dat for testing)
        
        // Example of initializing a load instruction (e.g., LW) and checking ALU behavior
        uut.instruction_Memory[0] = 16'h4D47;  // Some example instruction (load from memory)
        uut.instruction_Memory[1] = 16'h0F99;  
		uut.instruction_Memory[2] = 16'h0FD2;  
		uut.instruction_Memory[3] = 16'h8A80;  
		uut.instruction_Memory[4] = 16'h5E44;  
		uut.instruction_Memory[5] = 16'h4C44;  
		uut.instruction_Memory[6] = 16'h6DFA; 
        uut.Datamem[12]=16'h0101;
		 #10 clk = ~clk;

        // Finish the simulation
        #1150 $finish;
    end

    // Monitor the outputs to see the behavior during simulation
    initial begin
        $monitor("Time=%0t | ALUOut=%b | DataOut=%b | ZeroFlag=%b | OverflowFlag=%b | NegativeFlag=%b", 
		$time, ALUOut, dataOut, zeroFlag, overflowFlag, negativeFlag);	
		$monitor("Total number of executed instructions=%d\nTotal number of load instructions=%d\nTotal number of store instructions=%d\nTotal number of ALU instructions=%d\nTotal number of control instructions\n",Total_number_of_executed_instructions,Total_number_of_load_instructions,Total_number_of_store_instructions,Total_number_of_ALU_instructions,Total_number_of_control_instructions);
    end

endmodule


///Multi-Cycle Processor
module MultiCycleProcessor (clk, reset, zeroFlag, overflowFlag, negativeFlag, ALUOut, dataOut, Bus_W,Total_number_of_executed_instructions,Total_number_of_load_instructions,Total_number_of_store_instructions,Total_number_of_ALU_instructions,Total_number_of_control_instructions);  
	// input to our processor (just we need clock and reset to reintiate the values)
	input clk, reset;
	
	// output from our processor which used for waveform
	output reg zeroFlag, overflowFlag, negativeFlag; // output flags from ALU (which needed to check branch taken or not taken)	
	output reg Total_number_of_executed_instructions,Total_number_of_load_instructions,Total_number_of_store_instructions,Total_number_of_ALU_instructions,Total_number_of_control_instructions;
    output reg signed [15:0] ALUOut,Bus_W;// ALU output
	
	// all needed signals for main control unit
	reg IRWrite,RegDstB,RegDstC,RegWr,ALUSrcB,ALUSrcA,ExtOP,MemRd,MemWr,WBData,pcwriteUNcond;	
	reg [15:0] extendedImm ,ForReg,Alu_Result_Reg;
	reg [2:0] Rs,Rt,Rd,ALUCtrl,state,ALUOp,PCSource;
	reg [15:0] Temp;
	// define the Memories

	reg [15:0] Datamem [0:65535];  // 64k memory, with 16-bit words
	reg [15:0] instruction_Memory [0: 16'hFFFF];  // 16-bit wide memory, indexed by word

	//define the special purpose registers --> PC 
    reg [15:0] PC,RR;
		
	reg [2:0] PState, NState;
	reg [15:0] BusA,BusB,AluMuxA,AluMuxB;
    wire[15:0]outA,outB,outA_Reg,outB_Reg,Extend,Adder_Result,nextPC,jumpTarget,DtaMemory_Mux_out,DataMemory_Reg;
	 
    reg [15:0] IR; // instruction register used to save the readed instruction obtained from instruction memory

	// Define the Register File
    reg signed [15:0] Registers[0:7]; // 8 16-bit general purpose registers 
		
	// variable to save address used in memory, data in and data out from memory	
  reg signed [15:0] Memaddress;
  reg signed [15:0] dataIn;
  output reg signed [15:0] dataOut;
	

	integer i; // used to reinitiate the values saved in registers when there is reset input
	initial 
	begin
	PC = 16'b0; // the first address for PC starting from address zero 
	NState = `IF; // the first cycle for program is fetch of course 	
	Registers[0] = 16'd0;    // R0 = 0
    Registers[1] = 16'd1;    // R1 = 1
    Registers[2] = 16'd2;    // R2 = 2
    Registers[3] = 16'd3;    // R3 = 3
    Registers[4] = 16'd4;    // R4 = 4
    Registers[5] = 16'd5;    // R5 = 5
    Registers[6] = 16'd6;    // R6 = 6
    Registers[7] = 16'd0;    // R7 = 7
  	Total_number_of_executed_instructions=0;
	Total_number_of_load_instructions=0;
	Total_number_of_store_instructions=0;
	Total_number_of_ALU_instructions=0;
	Total_number_of_control_instructions=0;
	
		$display("\n*Welcome to our processor*\n");
	end
	
	
	always @(posedge clk, posedge reset) begin
		
		if (reset)	
			begin //empty all register values and make state to IF stage  
				$display("\n------------------Reset Program------------------\n");
				NState = `IF; ///Initialize the next state
				PC = 16'h0000;
				Rs = 3'd0;
				Rt = 3'd0;
				Rd = 3'd0;				

			end	
		else
			begin
				PState = NState;
				
				case(PState)
	//------------------------------------IF-----------------------------------------
					`IF: 
						begin
							$display("\n------------------Fetch Cycle------------------\n");
							$display("PC=%b\t", PC);
			  				InstructionMemory(PC,IR); // get instruction from instruction memory
			  				NState=`ID; // change the state instruction
							 Total_number_of_executed_instructions=Total_number_of_executed_instructions+1;
						end
						
	//------------------------------------ID-----------------------------------------
					`ID:
						begin
						  	$display("\n------------------Decode Cycle------------------\n");
							// Generate Main Control signals
							MainControl(IR[15:12],IR[2:0]);
							 $display("Time: %0t | Opcode: %b | Function: %b | State: %b | IRWrite: %b | RegDstB: %b | pcwriteUNcond: %b | RegDstC: %b | ExtOP:%b | RegWr: %b | ALUSrcA: %b | ALUSrcB: %b | ALUOp: %b | MemRd: %b | MemWr: %b | WBData: %b ", 
                     $time, IR[15:12],IR[2:0] , state, IRWrite, RegDstB, pcwriteUNcond, RegDstC,ExtOP, RegWr, ALUSrcA, ALUSrcB, ALUOp, MemRd, MemWr, WBData);
					 
					        Rs=IR[8:6];
							mux2x13bit (IR[5:3],IR[11:9],RegDstB,Rt);	 
							mux2x13bit (Rt,IR[11:9],RegDstC,Rd);								
							
							// Extend Imm	
							Extender(IR[5:0], ExtOP, extendedImm);
							
							// Read from Register File
							reg_file(0,Rd, Rs, Rt,Bus_W,BusA, BusB);
							$display("\nReggDst: %b, outA: %b, outB: %b", Rd, BusA, BusB);	
							// ******* Instruction dont need to go to execute stage (J-type)
							if(IR[15:12] == 4'b0001 )begin // JMP instruction need 2 cycles
								Total_number_of_control_instructions=Total_number_of_control_instructions+1;
								case(IR[2:0])
									3'b000:begin
									PC = {PC[15:9], IR[11:3]}; //Jmp then to fetch stage
									end	
									3'b001:begin
									 RR=PC+1;
									 PC = {PC[15:9], IR[11:3]}; 
									end	  
									3'b010:begin
									 PC = RR;      //Jmp then to fetch stage
									end
									endcase
									NState=`IF;
							
								end
							else if(IR[15:12] == 4'b1000)begin 
								 Total_number_of_control_instructions=Total_number_of_control_instructions+1;
								NState = `EX;
								end
							else // other instrucations need to go to Execute stage
								NState = `EX;		
						end
	//------------------------------------EX-----------------------------------------			
					`EX:
						begin			
							$display("\n------------------Execute Cycle------------------\n");
							$display("Extended immediate=%2d, BusA=%2d, BusB=%2d\n", extendedImm, BusA, BusB);
							mux2x1 (16'b1111111111111111,BusA,ALUSrcA,AluMuxA);
							mux2x1 (BusB,extendedImm,ALUSrcB,AluMuxB);	
							
							Total_number_of_ALU_instructions=Total_number_of_ALU_instructions+1;
							 ALU( ALUOp, AluMuxA, AluMuxB, ALUOut, zeroFlag, negativeFlag);
							 Alu_Result_Reg=ALUOut;
							if (IR[15:12] == 4'b0100 || IR[15:12] == 4'b0101 ) begin // LW, SW instructions 
								NState = `MEM;
							end
						    else if(IR[15:12] == 4'b0000 || IR[15:12] == 4'b0010 || IR[15:12] == 4'b0011)begin	
								NState = `WB;	 // R-Type, ADDI, ANDI instructions
							end
							else begin
							   NState=`IF;
							 end
							
							// check conditoins for branch instructions
							// BEQ instruction
							if (IR[15:12] == 4'b0110) 
								
								begin
									Total_number_of_control_instructions=Total_number_of_control_instructions+1;
									if (zeroFlag == 1'b1) 
										PC = PC + extendedImm; //branch taken --> PC = BTA
									else
										PC = PC + 1;
								end	  
							// BNE instruciton
							else if (IR[15:12] == 4'b0111) 
								begin 
									Total_number_of_control_instructions=Total_number_of_control_instructions+1;
									if (zeroFlag == 1'b0) 
										PC = PC + extendedImm;  //branch taken --> PC = BTA
									else
										PC = PC + 1; //branch not taken --> PC = PC + 1
								end
							
							// For instruction
							else if (IR[15:12] == 4'b1000) 
								begin
									if (negativeFlag == 1) 
										PC = PC + 1;
									else
										 
										NState = `WB;
								end

						end // end EX
//------------------------------------MEM-----------------------------------------				
					`MEM: 
						begin
							$display("\n------------------Memory Cycle------------------\n");
							Total_number_of_store_instructions=Total_number_of_store_instructions+1;
							Memaddress = Alu_Result_Reg;
						    dataIn = BusB;
							
							dataMemory(MemWr,MemRd,Memaddress,dataIn,dataOut);	
							
							if(IR[15:12] == 4'b0101) begin // SW instructin next state --> Fetch
								NState = `IF;
								PC=PC+1;
							   end
							else begin   //LW --> WB
								NState = `WB;
								Total_number_of_load_instructions=Total_number_of_load_instructions+1;
							end
						end
//------------------------------------WB-----------------------------------------
				
					`WB: 
						begin
							$display("\n------------------Write Back Cycle------------------\n");
							
							mux2x1 (Alu_Result_Reg, dataOut,WBData ,Bus_W );
							reg_file(RegWr,Rd, Rs, Rt,Bus_W,BusA, BusB);
							if (IR[15:12] == 4'b1000)begin
							PC=ForReg;	
							end
							else begin
							PC = PC + 1;
							end
							NState = `IF;
																			  	
						end	// end WB 
				endcase
			end // end else
		end // end always

// -------------------- InstructionMemory --------------------------
task InstructionMemory(input [15:0] instAdd, output reg [15:0] instout);

 // Initial instructions in memory (Loading the file into memory)
	
       //$readmemh("input.dat", instruction_Memory,  0, 150);  // Load 150 words from file into memory

 
	instout = instruction_Memory[instAdd];
	
	$display("Instruction = %b\n", instout);
endtask


// -------------------- Data Memory --------------------------	
task dataMemory( memWrite,memRead,input [15:0] address,input [15:0] dataIn,output reg [15:0] dataout);
	//Memory write is sensetive to the clock
		// Only the store instruction will write to memory and it writes a word (2 bytes)
		if (memWrite) begin
			Datamem[address] = dataIn[15:0];
			$display("Memeory=%b\n", Datamem[address]);
			end	
	//Memory read
		if (memRead) begin
		  dataout = Datamem[address] ;	//Load
		end
		$display("dataIn: %d, dataOut: %d, address: %d", dataIn, dataout, address);
        $display("MemR: %b, MemW: %b, Memory[%0d]: %d\n", memRead, memWrite, address, Datamem[address]);

endtask  


// -------------------- Register File --------------------------

// 8 16-bit Registers where R0 is always 0
task reg_file(input regWrite,input [2:0] reggDst, reggSrc1, reggSrc2,input [15:0] bus_w,output [15:0] outAA, outBB);

if(regWrite==0)	begin 
	$display("RegSucre%d=%b\n",reggSrc1,Registers[reggSrc1]);
	outAA = Registers[reggSrc1];
	outBB = Registers[reggSrc2];
	ForReg=outAA;
	end
	if (regWrite) begin
		if(reggDst != 3'b000)begin	 //Ignore writes to R0
			Registers[reggDst] = bus_w;
			$display("Registers%d=%b\n",reggDst,Registers[reggDst]); 
			end
	end

		
endtask


// -------------------- Main Control --------------------------
task MainControl(input [3:0] opcode,input [2:0] Function);
 case (opcode)
            // R_type
            4'b0000: begin
                state = 4'b0100;
                pcwriteUNcond = 1;
                IRWrite = 1;
                RegDstB = 0;
                RegDstC = 1;
                RegWr = 1;
                ALUSrcA = 1;
                ALUSrcB = 0;
                
                MemRd = 0;
                MemWr = 0;
                WBData = 0;
				ExtOP =1'bx;
                case (Function)
                    3'b000: ALUOp = 3'b000;
                    3'b001: ALUOp = 3'b001;
                    3'b010: ALUOp = 3'b010;
                    3'b011: ALUOp = 3'b011;
                    3'b100: ALUOp = 3'b100;
                    default: ALUOp = 3'bxxx;
                endcase
            end
            // J_type
            4'b0001: begin
                state = 4'b0010;
                pcwriteUNcond = 0;
                IRWrite = 1;
                RegDstB = 1'bx;
                RegDstC = 1'bx;
                
                RegWr = 0;
                ALUSrcA = 1'bx;
                ALUSrcB = 1'bx;
                ALUOp = 3'bxxx;
                MemRd = 0;
                MemWr = 0;
                WBData = 1'bx;	
				ExtOP =1'bx;
            end
            // ANDI_type
            4'b0010: begin
                state = 4'b0100;
                pcwriteUNcond = 1;
                IRWrite = 1;
                RegDstB = 1;
                RegDstC = 0;
				ExtOP =1'b1;
                RegWr = 1;
                ALUSrcA = 1;
                ALUSrcB = 1;
                ALUOp = 3'b000;
                MemRd = 0;
                MemWr = 0;
                WBData = 0;
            end
            // ADDI_type
            4'b0011: begin
                state = 4'b0100;
                pcwriteUNcond = 1;
                IRWrite = 1;
                RegDstB = 1;
                RegDstC = 0; 
				ExtOP =1'b0;
                RegWr = 1;
                ALUSrcA = 1;
                ALUSrcB = 1;
                ALUOp = 3'b001;
                MemRd = 0;
                MemWr = 0;
                WBData = 0;
            end	
			//LW_type
           4'b0100:begin
           state =101;
           pcwriteUNcond =1;
           IRWrite =1;
       	   RegDstB =1;
           RegDstC =0;
		   ExtOP =1'b0;
           RegWr =1;
           ALUSrcA =1;
           ALUSrcB =1;
           ALUOp =3'b001;
           MemRd =1;
           MemWr =0;
           WBData =1;      
      end
         //SW_type
           4'b0101:begin
           state =100;
           pcwriteUNcond =1;
           IRWrite =1;
       	   RegDstB =1;
           RegDstC =1'bx;
		   ExtOP =0;
           RegWr =0;
           ALUSrcA =1;
           ALUSrcB =1;
           ALUOp =3'b001;
           MemRd =0;
           MemWr =1;
           WBData =1'bx;      
      end
         //BEQ_type
           4'b0110:begin
           state =011;
           pcwriteUNcond =0;
           IRWrite =1;
       	   RegDstB =1;
           RegDstC =1'bx; 
		   ExtOP  =1;
           RegWr=0;
           ALUSrcA=1;
           ALUSrcB=0;
           ALUOp=3'b010;
           MemRd=0;
           MemWr=0;
           WBData=1'bx;      
      end
        //BNE_type
           4'b0111:begin
           state=011;
           pcwriteUNcond=0;
           IRWrite=1;
       	   RegDstB=1;
           RegDstC=1'bx;
		   ExtOP =1;
           RegWr=0;
           ALUSrcA=1;
           ALUSrcB=1;
           ALUOp=3'b010;
           MemRd=0;
           MemWr=0;
           WBData=1'bx;      
      end
           //For_type
           4'b1000:begin
           state=100;
           pcwriteUNcond=0;
           IRWrite=1;
       	   RegDstB=1;
           RegDstC=0;
		   ExtOP =1'bx;
           RegWr=1;
           ALUSrcA=0;
           ALUSrcB=0;
           ALUOp=3'b001;
           MemRd=0;
           MemWr=0;
           WBData=0;      
      end
            default: begin
                state = 4'bxxxx;
                pcwriteUNcond = 1'bx;
                IRWrite = 1'bx;
                RegDstB = 1'bx;
                RegDstC = 1'bx;
				ExtOP =1'bx;
                RegWr = 1'bx;
                ALUSrcA = 1'bx;
                ALUSrcB = 1'bx;
                MemRd = 1'bx;
                MemWr = 1'bx;
                WBData = 1'bx;
                ALUOp = 3'bxxx;
            end
        endcase
endtask	


// -------------------- ALU --------------------------
task ALU (input [2:0] ALUCtrl, input signed [15:0] a, input signed [15:0] b, output reg signed [15:0]result, output reg z, n);

	   $display("Alusurce = %b\n",ALUCtrl);
	// compute result
	 case (ALUCtrl)
            3'b000: result = a & b;        // AND operation
            3'b001: result = a + b;        // ADD operation
            3'b010: result = a - b;        // SUB operation
            3'b011: result = a << b;      // Arithmetic right shift
            3'b100: result = a >> b;       // Logical right shift
            default: result = 16'bx;       // Default case, result should be 0
        endcase

	
	// set flags
	z = result == 16'd0;
	n = result[15];

	$display("a= %b, b=%b\n", a, b);
	$display("ALU result= %b, z=%b, n=%b", result, z, n);
endtask	

///---------------------EXTENDER--------------- This task to extend the 16-bit immediate to be 32-bit as signed or unsigned extension
task Extender (
    input [5:0] in,          // 6-bit input
    input sign_ext,          // Sign extension control (0: zero extend, 1: sign extend)
    output reg [15:0] out    // 16-bit extended output
);
    integer i;               // Loop variable
    reg sign;                // Sign bit for sign extension

        // Zero extend
        if (sign_ext == 0) begin
            out[5:0] = in;   // Copy input to the lower bits
            for (i = 6; i < 16; i = i + 1)
                out[i] = 0;  // Set remaining bits to 0
        end 
        // Sign extend
        else begin
            out[5:0] = in;   // Copy input to the lower bits
            sign = in[5];    // Extract sign bit
            for (i = 6; i < 16; i = i + 1)
                out[i] = sign; // Extend sign bit
        end

endtask

task mux2x1 	 
(
	input [15:0] a0, b1,     
    input select,  
    output [15:0] out    
);

	assign out = select ? b1 : a0;

endtask
task mux2x13bit 	 
(
	input [2:0] a0, b1,     
    input select,  
    output [2:0] out    
);

	assign out = select ? b1 : a0;

endtask



endmodule