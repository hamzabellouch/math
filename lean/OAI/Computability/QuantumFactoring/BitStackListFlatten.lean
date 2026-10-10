import Mathlib
import OAI.Computability.QuantumFactoring.BitStackListOps

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram
variable {α : Type}
lemma fold_append_flatten (xss : List (List α)) (xs : List α) :
    xss.foldl (fun xs ys=>xs++ys) xs=xs++xss.flatten:=by
  induction xss generalizing xs with
  | nil=>simp
  | cons ys yss ih=>simp [ih,List.append_assoc]
lemma listCode_length_flatten_le (ea : α→List Bool) (xss : List (List α)) :
    (listCode ea xss.flatten).length≤(listCode (listCode ea) xss).length:=by
  induction xss with
  | nil=>simp [listCode]
  | cons xs xss ih=>
    simp only [List.flatten_cons,listCode_length_cons]
    have hh:=listCode_length_append ea xs xss.flatten
    omega
namespace Procedure
noncomputable def listFlatten (ea : α→List Bool) (d : α) :
    Procedure (listCode (listCode ea)) (listCode ea) List.flatten:=by
  let step:=(listAppend ea d).comp ((second (listCode ea) (listCode ea)).pair
    (first (listCode ea) (listCode ea)))
  let p:=foldList [] step Polynomial.X (by
    intro xss xs i
    change (listCode ea ((xss.take i).foldl (fun xs ys=>xs++ys) xs)).length≤_
    rw [fold_append_flatten]
    have hh:=listCode_length_append ea xs (xss.take i).flatten
    have hl:=listCode_length_flatten_le ea (xss.take i)
    have ht:=listCode_length_take_le (listCode ea) i xss
    simp only [Polynomial.eval_X];omega)
  exact (p.comp ((identity (listCode (listCode ea))).pair (constant _ (listCode ea) []))).congrFun (by
    intro xss;exact fold_append_flatten xss [])
end Procedure
end ExactQuantumFactoring.BitStackProgram

end



end OAI
