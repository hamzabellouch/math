import Mathlib
import OAI.Analysis.MatrixSigning.Machines.FixedStackPortLift
import OAI.Analysis.MatrixSigning.Arithmetic.GCDMachine

namespace OAI

section

namespace KS.W30.RationalMagnitudeMachine
open KS.W01.FixedStack KS.W29.FixedSequential
open KS.W19

def corePorts : Fin 10 ↪ Fin 13 :=
  ⟨fun i => ⟨i.val, by omega⟩, by intro i j h; exact Fin.ext (congrArg (fun x : Fin 13 => x.val) h)⟩
def numeratorCopyPorts : Fin 3 ↪ Fin 13 := ⟨![10,1,9], by decide⟩
def denominatorCopyPorts : Fin 3 ↪ Fin 13 := ⟨![11,2,9], by decide⟩
def numeratorTrimPorts : Fin 3 ↪ Fin 13 := ⟨![0,10,8], by decide⟩
def denominatorTrimPorts : Fin 3 ↪ Fin 13 := ⟨![0,11,8], by decide⟩

def copyNumerator : Program 13 := KS.W01.FixedCopy.program numeratorCopyPorts
def reverseNumeratorCopy : Program 13 := KS.W04.BinaryStackMoves.moveProgram 1 3
def copyDenominator : Program 13 := KS.W01.FixedCopy.program denominatorCopyPorts
def gcd : Program 13 := KS.W29.FixedSequential.liftPorts GCDMachine.program corePorts
def reverseGCD : Program 13 := KS.W04.BinaryStackMoves.moveProgram 5 8
def placeGCD : Program 13 := KS.W04.BinaryStackMoves.moveProgram 8 2
def takeNumerator : Program 13 := KS.W04.BinaryStackMoves.moveProgram 10 3
def takeDenominator : Program 13 := KS.W04.BinaryStackMoves.moveProgram 11 3
def divide : Program 13 := KS.W29.FixedSequential.liftPorts DivisionMachine.loop corePorts
def reverseQuotient : Program 13 := KS.W04.BinaryStackMoves.moveProgram 5 8
def trimNumerator : Program 13 := ofMachine (lift3 BinaryTrimMachine.machine numeratorTrimPorts)
def trimDenominator : Program 13 := ofMachine (lift3 BinaryTrimMachine.machine denominatorTrimPorts)
def clearRemainder : Program 13 := KS.W04.BinaryStackMoves.clearProgram 4
def clearGCD : Program 13 := KS.W04.BinaryStackMoves.clearProgram 2

def signDispatch (s : Fin 2) (heads : Fin 13 → Fin 3) (_coin : Bool) : Instruction 13 2 :=
  if s = 0 then
    if (heads 10).val = 0 then
      ⟨some 1, Vector.ofFn (fun j => if j = 12 then .pop else .stay)⟩
    else Instruction.halt 13 2
  else ⟨none, Vector.ofFn (fun j => if j = 12 then .push false else .stay)⟩
def normalizeSign : Program 13 := ofMachine (compile 0 10 10 signDispatch)

def oneDispatch (_s : Fin 1) (_heads : Fin 13 → Fin 3) (_coin : Bool) : Instruction 13 1 :=
  ⟨none, Vector.ofFn (fun j => if j = 11 then .push true else .stay)⟩
def insertOne : Program 13 := ofMachine (compile 0 10 10 oneDispatch)
def zeroBranch : Program 13 := compose (KS.W04.BinaryStackMoves.clearProgram 10)
  (compose insertOne normalizeSign)

def prepare : Program 13 := compose copyNumerator (compose reverseNumeratorCopy copyDenominator)
def computeGCD : Program 13 := compose prepare (compose gcd (compose reverseGCD placeGCD))
def reduceNumerator : Program 13 := compose takeNumerator
  (compose divide (compose reverseQuotient (compose trimNumerator clearRemainder)))
def reduceDenominator : Program 13 := compose takeDenominator
  (compose divide (compose reverseQuotient (compose trimDenominator clearRemainder)))
def positiveBranch : Program 13 := compose computeGCD
  (compose reduceNumerator (compose reduceDenominator (compose clearGCD normalizeSign)))

def selector (heads : Fin 13 → Fin 3) (_coin : Bool) : KS.W29.FixedBranch.SelectInstruction 13 :=
  ⟨if (heads 11).val = 0 then .left else .right, Vector.ofFn (fun _ => .stay)⟩
def program : Program 13 := KS.W29.FixedBranch.branch zeroBranch positiveBranch 10 selector

def «stacks» (work : Fin 10 → List Bool) (num den : List Bool) (negative : Bool) :
    Fin 13 → List Bool :=
  ![work 0,work 1,work 2,work 3,work 4,work 5,work 6,work 7,work 8,work 9,num,den,[negative]]
def state (num den : List Bool) (negative : Bool) : Fin 13 → List Bool :=
  «stacks» (fun _ => []) num den negative

theorem branch_table_length {k : ℕ} (P Q : Program k) (out : Fin k)
    (select : (Fin k→Fin 3)→Bool→KS.W29.FixedBranch.SelectInstruction k) :
    (KS.W29.FixedBranch.branch P Q out select).table.length=
      (P.states+Q.states+1)*(3^k*2) := by
  exact KS.W01.FixedStack.compile_table_length
    (KS.W29.FixedBranch.start P Q) P.input out (KS.W29.FixedBranch.dispatch P Q select)

theorem program_table_length : program.table.length =
    (zeroBranch.states + positiveBranch.states + 1) * (3 ^ 13 * 2) :=
  branch_table_length zeroBranch positiveBranch 10 selector

end KS.W30.RationalMagnitudeMachine

end

end OAI
