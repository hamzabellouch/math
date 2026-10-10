import Mathlib
import OAI.Analysis.LaughlinGap.RationalRows

namespace OAI

/-! Rational Row Computable. -/

noncomputable section


namespace LaughlinGap.RealOccupation
open scoped BigOperators
open Spin

lemma sum_row_fiber {S : Type*} [AddCommMonoid S] (t : Fin 8) (i : Fin 9)
    (f : Fin 8 → Fin 9 → S) :
    (∑ a : RowEntry t, if a.output=i then f a.val.1 a.val.2 else 0) =
      ∑ p : Fin 8, ∑ j : Fin 9, if p.val+j.val=t.val+i.val then f p j else 0 := by
  classical
  rw [← Fintype.sum_prod_type (fun a : Fin 8 × Fin 9 =>
    if a.1.val+a.2.val=t.val+i.val then f a.1 a.2 else 0)]
  symm
  apply Finset.sum_congr_set (s := {a : Fin 8 × Fin 9 | t.val ≤ a.1.val+a.2.val ∧
      a.1.val+a.2.val ≤ t.val+8})
  · intro a ha
    change t.val ≤ a.1.val+a.2.val ∧ a.1.val+a.2.val ≤ t.val+8 at ha
    have he : a.1.val+a.2.val=t.val+i.val ↔ RowEntry.output (⟨a,ha⟩ : RowEntry t)=i := by
      simp only [RowEntry.output,Fin.ext_iff]
      omega
    simp only [he]
  · intro a ha
    change ¬ (t.val ≤ a.1.val+a.2.val ∧ a.1.val+a.2.val ≤ t.val+8) at ha
    have hi := i.isLt
    have hn : a.1.val+a.2.val ≠ t.val+i.val := by omega
    simp only [ite_eq_right hn]

lemma sum_fixed_pair {S : Type*} [AddCommMonoid S] (T : ℕ) (p : Fin 8)
    (f : Fin 9 → S) :
    (∑ j : Fin 9, if p.val+j.val=T then f j else 0) =
      if h : p.val ≤ T ∧ T-p.val < 9 then f ⟨T-p.val,h.2⟩ else 0 := by
  classical
  by_cases h : p.val ≤ T ∧ T-p.val < 9
  · rw [dite_eq_left h]
    rw [Finset.sum_eq_single (⟨T-p.val,h.2⟩ : Fin 9)]
    · simp only [Nat.add_sub_of_le h.1,ite_true]
    · intro j hj hn
      have he : p.val+j.val ≠ T := by
        intro he
        apply hn
        apply Fin.ext
        dsimp
        omega
      simp only [ite_eq_right he]
    · simp
  · rw [dite_eq_right h]
    apply Finset.sum_eq_zero
    intro j hj
    have he : p.val+j.val ≠ T := by have := j.isLt; omega
    simp only [ite_eq_right he]

def RationalRow.threeSumFast (r : RationalRow) (z : ℕ) (i : Fin 9) : ℚ :=
  ∑ p : Fin 8, if h : p.val ≤ r.t.val+i.val ∧ r.t.val+i.val-p.val < 9 then
    r.alpha p ⟨r.t.val+i.val-p.val,h.2⟩ * uCoefficient 2 z (r.t.val+i.val) p.val else 0

lemma RationalRow.threeSum_eq_fast (r : RationalRow) (z : ℕ) (i : Fin 9) :
    r.threeSum z i = r.threeSumFast z i := by
  rw [RationalRow.threeSum,sum_row_fiber r.t i (fun p j =>
    r.alpha p j * uCoefficient 2 z (r.t.val+i.val) p.val)]
  simp only [sum_fixed_pair,RationalRow.threeSumFast]

end LaughlinGap.RealOccupation

end

end OAI
