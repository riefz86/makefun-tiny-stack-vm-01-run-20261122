// Tiny stack VM for make.fun's ISA v1: 32-bit wrapping values, a 256-value data
// stack, a 64-deep call stack, 256 words of memory, 1M steps, 64K output bytes.
// Ten traps, each with its own exit code; a trap keeps earlier output.
import{mkdirSync,readdirSync,readFileSync,writeFileSync}from'node:fs';
import{join}from'node:path';
// Per opcode: [immediate bytes, values popped, values pushed], keys in decimal.
const T={0:[0,0,0],1:[1,0,1],2:[4,0,1],3:[0,1,0],4:[0,1,2],5:[0,2,2],6:[0,2,3],7:[0,3,3],16:[0,2,1],17:[0,2,1],18:[0,2,1],19:[0,2,1],20:[0,2,1],21:[0,2,1],22:[0,2,1],23:[0,1,1],24:[0,2,1],25:[0,2,1],26:[0,2,1],27:[0,1,1],28:[0,2,1],29:[0,2,1],30:[0,2,1],32:[0,2,1],33:[0,2,1],34:[0,2,1],48:[2,0,0],49:[2,1,0],50:[2,1,0],51:[2,0,0],52:[0,0,0],64:[0,1,1],65:[0,2,0],80:[0,1,0],81:[0,1,0],82:[0,0,1],83:[0,1,0]};
function run(p,q){
 const n=p.length,S=new Int32Array(256),C=new Int32Array(64),M=new Int32Array(256),o=[];
 let s=0,c=0,pc=0,k=0,i=0;
 for(;;){
  if(k===1e6)return[o,10]; // step limit, checked before anything else
  if(pc<0||pc>=n)return[o,9];
  const op=p[pc],t=T[op];
  if(!t)return[o,5];
  const m=t[0],u=t[1],w=t[2];
  if(pc+m>=n)return[o,9]; // immediate cut off by the end of the program
  k++;
  const nx=pc+1+m; // address of the next instruction
  if(s<u)return[o,2];
  if(s-u+w>256)return[o,3];
  pc=nx;
  switch(op){
   case 0:return[o,0]; // HALT
   case 1:S[s++]=(p[nx-1]<<24)>>24;break; // PUSH8, sign-extended
   case 2:S[s++]=p[nx-4]|p[nx-3]<<8|p[nx-2]<<16|p[nx-1]<<24;break; // PUSH32, little-endian
   case 3:s--;break; // POP
   case 4:S[s]=S[s-1];s++;break; // DUP
   case 5:{const a=S[s-1];S[s-1]=S[s-2];S[s-2]=a;break;} // SWAP
   case 6:S[s]=S[s-2];s++;break; // OVER
   case 7:{const a=S[s-3];S[s-3]=S[s-2];S[s-2]=S[s-1];S[s-1]=a;break;} // ROT
   case 23:S[s-1]=-S[s-1]|0;break; // NEG, wraps
   case 27:S[s-1]=~S[s-1];break; // NOT
   case 48:pc=nx+((p[nx-2]|p[nx-1]<<8)<<16>>16);break; // JMP, signed offset from nx
   case 49:case 50:{const v=S[--s];if(op===49?v===0:v!==0)pc=nx+((p[nx-2]|p[nx-1]<<8)<<16>>16);break;} // JZ/JNZ
   case 51:if(c===64)return[o,7];C[c++]=nx;pc=p[nx-2]|p[nx-1]<<8;break; // CALL, unsigned target
   case 52:if(!c)return[o,8];pc=C[--c];break; // RET
   case 64:{const a=S[s-1];if(a<0||a>255)return[o,6];S[s-1]=M[a];break;} // LOAD
   case 65:{const a=S[s-1],v=S[s-2];if(a<0||a>255)return[o,6];s-=2;M[a]=v;break;} // STORE, top is the address
   case 80:{const d=String(S[s-1]);if(o.length+d.length>65536)return[o,11];s--;for(let j=0;j<d.length;j++)o.push(d.charCodeAt(j));break;} // PRINT, decimal ASCII
   case 81:if(o.length+1>65536)return[o,11];o.push(S[--s]&255);break; // PUTC, low 8 bits
   case 82:S[s++]=i<q.length?q[i++]:-1;break; // IN, -1 once the input is used up
   case 83:return[o,S[--s]&255]; // EXIT, low byte of the value
   default:{ // two-operand arithmetic, comparison and shift
    const b=S[s-1],a=S[s-2];let r;
    switch(op){
     case 16:r=a+b|0;break; // ADD
     case 17:r=a-b|0;break; // SUB
     case 18:r=Math.imul(a,b);break; // MUL, low 32 bits exactly
     case 19:if(!b)return[o,4];r=a===-2147483648&&b===-1?a:a/b|0;break; // DIV, toward zero
     case 20:if(!b)return[o,4];r=b===-1?0:a%b;break; // MOD, sign of a
     case 21:if(!b)return[o,4];r=Math.floor((a>>>0)/(b>>>0))|0;break; // DIVU, unsigned
     case 22:if(!b)return[o,4];r=(a>>>0)%(b>>>0)|0;break; // MODU, unsigned
     case 24:r=a&b;break; // AND
     case 25:r=a|b;break; // OR
     case 26:r=a^b;break; // XOR
     case 28:r=a<<(b&31);break; // SHL, low 5 bits of the count
     case 29:r=a>>(b&31);break; // SHR, arithmetic
     case 30:r=a>>>(b&31);break; // SHRU, logical
     case 32:r=a===b?1:0;break; // EQ
     case 33:r=a<b?1:0;break; // LT, signed
     default:r=(a>>>0)<(b>>>0)?1:0; // LTU, unsigned
    }
    s-=2;S[s++]=r;
   }
  }
 }
}
// Driver: answer every instance in the input directory, in one run.
const I=process.env.MAKEFUN_INPUT_DIR??'/input',O=process.env.MAKEFUN_OUTPUT_DIR??'/output';
for(const id of readdirSync(I).sort()){
 const g=readFileSync(join(I,id,'program.bin'));
 let q=Buffer.alloc(0);
 try{q=readFileSync(join(I,id,'input.bin'))}catch{}
 const[o,e]=run(g,q);
 mkdirSync(join(O,id),{recursive:true});
 writeFileSync(join(O,id,'stdout.bin'),Buffer.from(o));
 writeFileSync(join(O,id,'exit.txt'),e+'\n');
}
