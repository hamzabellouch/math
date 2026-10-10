import Mathlib
import OAI.Combinatorics.ThinTrees.Flow.RootedOrientation

namespace OAI

/-! Rooted flow. -/

section

namespace AlgorithmicThinTrees.Orientations
noncomputable section
open Finset StrongThinTree StrongThinTree.MultiGraph
open scoped Classical
variable {n m : ℕ}

def Rooted.leftFlow {G : MultiGraph n m} {T : Finset (Fin m)} {root : Fin n}
    (R : Rooted G T root) (e : Fin m) : ℝ :=
  if he : e ∈ T then if (R.tail ⟨e,he⟩).val=G.left e then 1 else 0 else 0

def Rooted.rightFlow {G : MultiGraph n m} {T : Finset (Fin m)} {root : Fin n}
    (R : Rooted G T root) (e : Fin m) : ℝ :=
  if he : e ∈ T then if (R.tail ⟨e,he⟩).val=G.right e then 1 else 0 else 0

lemma Rooted.leftFlow_nonneg {G : MultiGraph n m} {T : Finset (Fin m)} {root : Fin n}
    (R : Rooted G T root) (e : Fin m) : 0 ≤ R.leftFlow e := by
  unfold Rooted.leftFlow
  split_ifs <;> norm_num

lemma Rooted.rightFlow_nonneg {G : MultiGraph n m} {T : Finset (Fin m)} {root : Fin n}
    (R : Rooted G T root) (e : Fin m) : 0 ≤ R.rightFlow e := by
  unfold Rooted.rightFlow
  split_ifs <;> norm_num

lemma Rooted.edgeFlow {G : MultiGraph n m} {T : Finset (Fin m)} {root : Fin n}
    (R : Rooted G T root) (e : Fin m) :
    R.leftFlow e+R.rightFlow e=if e ∈ T then 1 else 0 := by
  by_cases he : e ∈ T
  · obtain hl|hr := R.endpoint ⟨e,he⟩
    · have hnot : (R.tail ⟨e,he⟩).val ≠ G.right e := by rw [hl]; exact G.loopless e
      simp [Rooted.leftFlow,Rooted.rightFlow,he,hl,G.loopless e]
    · have hnot : (R.tail ⟨e,he⟩).val ≠ G.left e := by rw [hr]; exact (G.loopless e).symm
      simp [Rooted.leftFlow,Rooted.rightFlow,he,hr,(G.loopless e).symm]
  · simp [Rooted.leftFlow,Rooted.rightFlow,he]

def out (G : MultiGraph n m) (a b : Fin m → ℝ) (v : Fin n) : ℝ :=
  ∑e, ((if G.left e=v then a e else 0)+(if G.right e=v then b e else 0))

lemma Rooted.arc_at {G : MultiGraph n m} {T : Finset (Fin m)} {root : Fin n}
    (R : Rooted G T root) (e : Fin m) (v : Fin n) :
    (if G.left e=v then R.leftFlow e else 0)+(if G.right e=v then R.rightFlow e else 0)=
      if he : e ∈ T then if (R.tail ⟨e,he⟩).val=v then 1 else 0 else 0 := by
  by_cases he : e ∈ T
  · obtain hl|hr := R.endpoint ⟨e,he⟩
    · have hnot : (R.tail ⟨e,he⟩).val ≠ G.right e := by rw [hl]; exact G.loopless e
      simp [Rooted.leftFlow,Rooted.rightFlow,he,hl,G.loopless e]
    · have hnot : (R.tail ⟨e,he⟩).val ≠ G.left e := by rw [hr]; exact (G.loopless e).symm
      simp [Rooted.leftFlow,Rooted.rightFlow,he,hr,(G.loopless e).symm]
  · simp [Rooted.leftFlow,Rooted.rightFlow,he]

lemma Rooted.out_eq {G : MultiGraph n m} {T : Finset (Fin m)} {root : Fin n}
    (R : Rooted G T root) (v : Fin n) :
    out G R.leftFlow R.rightFlow v=if v=root then 0 else 1 := by
  simp only [out,R.arc_at]
  by_cases hv : v=root
  · subst v
    simp only [ite_true]
    apply sum_eq_zero
    intro e he
    by_cases h : e ∈ T
    · simp only [dite_eq_left h,ite_eq_right (R.tail ⟨e,h⟩).property]
    · simp [h]
  · rw [ite_eq_right hv]
    let f : T := R.tail.symm ⟨v,hv⟩
    have hf : (R.tail f).val=v := congrArg Subtype.val (R.tail.apply_symm_apply ⟨v,hv⟩)
    rw [sum_eq_single f.val]
    · simp only [dite_eq_left f.property,hf,ite_true]
    · intro e he hef
      by_cases h : e ∈ T
      · rw [dite_eq_left h]
        apply ite_eq_right
        intro hv'
        apply hef
        exact congrArg Subtype.val (R.tail.injective (Subtype.ext (hv'.trans hf.symm)))
      · simp [h]
    · simp

lemma out_nonneg (G : MultiGraph n m) {a b : Fin m → ℝ}
    (ha : ∀e, 0 ≤ a e) (hb : ∀e, 0 ≤ b e) (v : Fin n) : 0 ≤ out G a b v := by
  unfold out
  apply sum_nonneg
  intro e he
  exact add_nonneg (by split_ifs; exact ha e; exact le_rfl)
    (by split_ifs; exact hb e; exact le_rfl)

lemma internal_le_out (G : MultiGraph n m) {x a b : Fin m → ℝ}
    (ha : ∀e, 0 ≤ a e) (hb : ∀e, 0 ≤ b e) (he : ∀e, x e ≤ a e+b e)
    (S : Finset (Fin n)) :
    (∑e ∈ univ.filter (fun e => G.left e ∈ S ∧ G.right e ∈ S), x e) ≤ ∑v ∈ S, out G a b v := by
  rw [sum_filter]
  simp only [out]
  rw [sum_comm]
  apply sum_le_sum
  intro e he'
  have hsum : (∑v ∈ S, ((if G.left e=v then a e else 0)+(if G.right e=v then b e else 0)))=
      (if G.left e ∈ S then a e else 0)+(if G.right e ∈ S then b e else 0) := by
    rw [sum_add_distrib]
    simp only [sum_ite_eq]
  rw [hsum]
  by_cases hl : G.left e ∈ S <;> by_cases hr : G.right e ∈ S
  · simpa only [hl,hr,and_self,ite_true] using he e
  · simpa only [hl,hr,and_false,ite_false,ite_true,add_zero] using ha e
  · simpa only [hl,hr,false_and,ite_false,ite_true,zero_add] using hb e
  · simp [hl,hr]

end
end AlgorithmicThinTrees.Orientations
end

end OAI
