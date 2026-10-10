import Mathlib
import OAI.Computability.QuantumFactoring.BitStackListFold
import OAI.Computability.QuantumFactoring.BitStackNaturals

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram
variable {α : Type}
lemma fold_count (xs : List α) (n : ℕ) : xs.foldl (fun n _=>n+1) n=n+xs.length := by
  induction xs generalizing n with
  | nil=>simp
  | cons a as ih=>simp only [List.foldl_cons,ih,List.length_cons];omega
namespace Procedure
noncomputable def listLength (ea : α→List Bool) (d : α) :
    Procedure (listCode ea) Nat.bits List.length := by
  let step:=unarySuccessor.comp (second ea unaryCode)
  let rep:=foldList d step Polynomial.X (by
    intro xs n i
    change (unaryCode ((xs.take i).foldl (fun n _=>n+1) n)).length≤_
    rw [fold_count]
    simp only [unaryCode,List.length_replicate,Polynomial.eval_X,List.length_take]
    have hh:=list_length_le_code ea xs
    omega)
  let start:=(identity (listCode ea)).pair (constant (listCode ea) unaryCode 0)
  exact (unaryToBits.comp (rep.comp start)).congrFun (by intro xs;simpa only [Function.comp_apply,id_eq,Nat.zero_add] using fold_count xs 0)
end Procedure
end ExactQuantumFactoring.BitStackProgram

end



end OAI
