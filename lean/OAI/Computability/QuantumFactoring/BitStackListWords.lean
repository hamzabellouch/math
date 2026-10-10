import Mathlib
import OAI.Computability.QuantumFactoring.BitStackListOps

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram
lemma flatten_length_le_code (xs : List (List Bool)) :
    xs.flatten.length ≤ (listCode (id : List Bool→List Bool) xs).length := by
  induction xs with
  | nil=>simp [listCode]
  | cons x xs ih=>
    simp only [List.flatten_cons,List.length_append,listCode_length_cons,id_eq]
    omega
lemma fold_append_words (xs : List (List Bool)) (ys : List Bool) :
    xs.foldl (fun ys x=>ys++x) ys=ys++xs.flatten := by
  induction xs generalizing ys with
  | nil=>simp
  | cons x xs ih=>simp [ih,List.append_assoc]
namespace Procedure
noncomputable def listJoinWords : Procedure (listCode (id : List Bool→List Bool)) id List.flatten := by
  let step:=(append.comp (swap (id : List Bool→List Bool) id))
  let rep:=foldList [] step Polynomial.X (by
    intro xs ys i
    change ((xs.take i).foldl (fun ys x=>ys++x) ys).length ≤ _
    rw [fold_append_words,List.length_append]
    have hh:=flatten_length_le_code (xs.take i)
    have ht:=listCode_length_take_le (id : List Bool→List Bool) i xs
    simp only [Polynomial.eval_X,id_eq]
    omega)
  exact (rep.comp ((identity (listCode (id : List Bool→List Bool))).pair
    (constant (listCode (id : List Bool→List Bool)) id []))).congrFun (by
      intro xs;change xs.foldl (fun ys x=>ys++x) []=xs.flatten
      simpa only [List.nil_append] using fold_append_words xs [])
noncomputable def listFlatMapWords {α : Type} {ea : α→List Bool} {f : α→List Bool}
    (d : α) (p : Procedure ea id f) : Procedure (listCode ea) id (fun xs=>xs.flatMap f) :=
  (listJoinWords.comp (listMap d [] p)).congrFun (by intro xs;rfl)
end Procedure
end ExactQuantumFactoring.BitStackProgram

end



end OAI
