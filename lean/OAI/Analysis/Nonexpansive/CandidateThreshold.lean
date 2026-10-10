import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace OAI

/-!
# Candidate thresholds chosen before maps

A single integer simultaneously supplies the detector defect scale and
all already fixed ancestor displacement bounds.
-/

open scoped BigOperators

namespace ReflexiveFixedPoints

/-- The threshold depends only on the current positive budget, detector scale,
and the sum of the displacement constants of the fixed ancestors. -/
theorem exists_candidate_threshold {C δ e : ℝ}
    (hδ : 0 < δ) (he : 0 < e) :
    ∃ m : ℕ, 1 ≤ m ∧ 1 / (m : ℝ) < δ ∧ C / (m : ℝ) ≤ e := by
  obtain ⟨m, hm⟩ := exists_nat_gt (max (1 / δ) (C / e))
  have hδm : 1 / δ < (m : ℝ) := (le_max_left _ _).trans_lt hm
  have hCm : C / e < (m : ℝ) := (le_max_right _ _).trans_lt hm
  have hmpos : (0 : ℝ) < m := (one_div_pos.mpr hδ).trans hδm
  have hmnat : 0 < m := Nat.cast_pos.mp hmpos
  refine ⟨m, hmnat, ?_, ?_⟩
  · apply (div_lt_iff₀ hmpos).2
    have h := (div_lt_iff₀ hδ).1 hδm
    simpa only [mul_comm] using h
  · apply le_of_lt
    apply (div_lt_iff₀ hmpos).2
    have h := (div_lt_iff₀ he).1 hCm
    simpa only [mul_comm] using h

/-- Summing the actual fixed-ancestor displacement estimates preserves their
common approximate-fixed-point defect factor. -/
theorem candidate_ancestor_displacement {A X : Type*} [Fintype A]
    [NormedAddCommGroup X] (G : A → X) (c : A → ℝ) (y : X)
    {defect e : ℝ} {m : ℕ}
    (hc : ∀ a, 0 ≤ c a)
    (hG : ∀ a, ‖G a - y‖ ≤ c a * defect)
    (hdefect : defect ≤ 1 / (m : ℝ))
    (hscale : (∑ a, c a) / (m : ℝ) ≤ e) :
    (∑ a, ‖G a - y‖) ≤ e := by
  calc
    (∑ a, ‖G a - y‖) ≤ ∑ a, c a * defect :=
      Finset.sum_le_sum fun a _ => hG a
    _ = (∑ a, c a) * defect := (Finset.sum_mul _ _ _).symm
    _ ≤ (∑ a, c a) * (1 / (m : ℝ)) :=
      mul_le_mul_of_nonneg_left hdefect (Finset.sum_nonneg fun a _ => hc a)
    _ = (∑ a, c a) / (m : ℝ) := by simp only [div_eq_mul_inv, one_mul]
    _ ≤ e := hscale

end ReflexiveFixedPoints

end OAI
