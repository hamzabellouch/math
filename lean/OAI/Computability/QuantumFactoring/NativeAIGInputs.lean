import Mathlib
import OAI.Computability.QuantumFactoring.AIGInputs
import OAI.Computability.QuantumFactoring.BitStackTabulate
import OAI.Computability.QuantumFactoring.NativeAIGProcedures

namespace OAI



section

namespace ExactQuantumFactoring.NativeAIG
open Std.Sat
def rawInputs (n : ℕ) : Graph := ⟨.zero::(List.range n).map Decl.atom,[]⟩
lemma rawInputs_succ (n : ℕ) : rawInputs (n+1)=(atom (rawInputs n) n).1 := by
  simp [rawInputs,atom,List.range_succ]
lemma inputsPrefix_rel (n k : ℕ) (h : k≤n) : Rel (rawInputs k) (AIGCompiler.inputsPrefix n k h).1 := by
  induction k with
  | zero=>exact empty_rel n
  | succ k ih=>
    rw [rawInputs_succ]
    exact (atom_rel (ih (by omega)) ⟨k,by omega⟩).1
lemma inputs_rel (n : ℕ) : Rel (rawInputs n) (AIGCompiler.inputs n).1 := inputsPrefix_rel n n le_rfl
lemma inputsPrefix_ref (n k : ℕ) (h : k≤n) (i : Fin k) :
    (((AIGCompiler.inputsPrefix n k h).2 i).gate,
      ((AIGCompiler.inputsPrefix n k h).2 i).invert)=(i.val+1,false) := by
  induction k with
  | zero=>exact Fin.elim0 i
  | succ k ih=>
    refine Fin.lastCases ?_ (fun j=>?_) i
    · simp only [AIGCompiler.inputsPrefix,Fin.snoc_last,AIG.mkAtom,AIGCompiler.inputsPrefix_size]
      rfl
    · simp only [AIGCompiler.inputsPrefix,Fin.snoc_castSucc]
      exact ih (by omega) j
lemma inputs_ref (n : ℕ) (i : Fin n) :
    (((AIGCompiler.inputs n).2 i).gate,((AIGCompiler.inputs n).2 i).invert)=(i.val+1,false) :=
  inputsPrefix_ref n n le_rfl i

namespace Emission
open BitStackProgram BitStackProgram.Procedure
noncomputable def inputsP : Procedure unaryCode graphCode rawInputs := by
  let p : Procedure (prodCode unaryCode emptyCode) declCode (fun x=>Decl.atom x.1):=
    atomDecl.comp (unaryToBits.comp (first unaryCode emptyCode))
  let ds:=(tabulate (f:=fun (_ : Unit) i=>Decl.atom i) Decl.zero p).comp ((identity unaryCode).pair (Procedure.constant _ emptyCode ()))
  exact (packGraph.comp (((listCons declCode).comp
    ((Procedure.constant _ declCode Decl.zero).pair ds)).pair
      (Procedure.constant _ (listCode entryCode) []))).congrFun (by intro n;rfl)
noncomputable def inputRefP : Procedure unaryCode refCode (fun n=>(n+1,false)) :=
  ((successor.comp unaryToBits).pair (Procedure.constant _ boolCode false))
end Emission
end ExactQuantumFactoring.NativeAIG

end



end OAI
