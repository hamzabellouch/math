import Mathlib
import OAI.Computability.QuantumFactoring.BitStackListFold
import OAI.Computability.QuantumFactoring.BitStackDivision

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram
variable {α : Type}
def dropStep : ℕ×List α→ℕ×List α
  | (n,xs)=>if n=0 then (n,xs) else (n-1,xs.tail)
lemma dropStep_iterate (i n : ℕ) (xs : List α) :
    dropStep^[i] (n,xs)=(n-i,xs.drop (min i n)) := by
  induction i generalizing n xs with
  | zero=>simp
  | succ i ih=>
    rw [Function.iterate_succ_apply]
    by_cases hn : n=0
    · subst n;simp [dropStep,ih]
    · obtain ⟨n,rfl⟩:=Nat.exists_eq_succ_of_ne_zero hn
      simp only [dropStep,Nat.succ_ne_zero,ite_false,Nat.succ_sub_one,ih]
      rw [←List.drop_one,List.drop_drop]
      congr 1
      · omega
      · congr 1; omega

namespace Procedure
variable (ea : α→List Bool)
noncomputable def listDrop : Procedure (prodCode Nat.bits (listCode ea)) (listCode ea)
    (fun x=>x.2.drop x.1) := by
  let en:=prodCode Nat.bits (listCode ea)
  let n:=first Nat.bits (listCode ea)
  let xs:=second Nat.bits (listCode ea)
  let pred:=binarySub.comp (n.pair (constant en Nat.bits 1))
  let step:=(conditional (binaryZero.comp n) (identity en)
    (pred.pair ((listTail ea).comp xs))).congrFun (by intro x;rfl)
  have stepType : Procedure en en (dropStep (α:=α)):=
    step.congrFun (by intro x;simp only [Function.comp_apply,decide_eq_true_eq,id_eq,dropStep])
  let rep:=stepType.iterate Polynomial.X (by
    intro k x i _
    rw [dropStep_iterate]
    simp only [en,prodCode,pairBits_length,Polynomial.eval_X]
    have hn:=bits_length_mono (Nat.sub_le x.1 i)
    have hl:=listCode_length_drop_le ea (min i x.1) x.2
    omega)
  let times:=(length.precompose (listCode ea)).comp xs
  exact (xs.comp (rep.comp (times.pair (identity en)))).congrFun (by
    intro x
    change (dropStep^[(listCode ea x.2).length] x).2=x.2.drop x.1
    rw [dropStep_iterate]
    by_cases h:x.1≤(listCode ea x.2).length
    · rw [Nat.min_eq_right h]
    · have hlen:=list_length_le_code ea x.2
      rw [Nat.min_eq_left (by omega),List.drop_eq_nil_of_le (by omega),List.drop_eq_nil_of_le (by omega)])
noncomputable def listGet (d : α) : Procedure (prodCode Nat.bits (listCode ea)) ea
    (fun x=>(x.2.drop x.1).headD d) := (listHead ea d).comp (listDrop ea)
end Procedure
end ExactQuantumFactoring.BitStackProgram

end



end OAI
