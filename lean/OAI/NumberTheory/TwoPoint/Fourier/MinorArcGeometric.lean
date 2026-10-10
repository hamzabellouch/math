import OAI.NumberTheory.TwoPoint.Bounds.ShortSumSampling
import Mathlib.Algebra.Field.GeomSum

namespace OAI

/-! Literal interval exponential sums used in the minor-arc fourth moment. -/

namespace TwoPointCorrelations

open Finset Complex

lemma additiveCharacter_pow (α : ℝ) (n : ℕ) :
    additiveCharacter α n = additiveCharacter α 1 ^ n := by
  induction n with
  | zero => simp [additiveCharacter]
  | succ n ih => rw [additiveCharacter_nat_add, ih, pow_succ]

lemma minor_arc_unit_geometric {z : ℂ} (hz : ‖z‖ = 1) (hz1 : z ≠ 1) (a b : ℕ) :
    ‖∑ n ∈ Ico a b, z ^ n‖ ≤ 2 / ‖z - 1‖ := by
  by_cases hab : a ≤ b
  · have he := congrArg norm (geom_sum_Ico_mul z hab)
    rw [norm_mul] at he
    have hnorm : ‖z ^ b - z ^ a‖ ≤ 2 := by
      simpa only [norm_pow, hz, one_pow, one_add_one_eq_two] using norm_sub_le (z ^ b) (z ^ a)
    exact (le_div_iff₀ (norm_pos_iff.mpr (sub_ne_zero.mpr hz1))).mpr (he.trans_le hnorm)
  · simp [Ico_eq_empty_of_le (le_of_not_ge hab)]
    positivity

/-- The resonant case is kept explicit, rather than assigning an infinite
value to a reciprocal at zero. -/
noncomputable def minorArcGeometricBound (L α : ℝ) : ℝ :=
  if additiveCharacter α 1 = 1 then L
  else min L (2 / ‖additiveCharacter α 1 - 1‖)

lemma minor_arc_geometric_bound (α : ℝ) (a b : ℕ) :
    ‖∑ n ∈ Ico a b, additiveCharacter α n‖ ≤
      minorArcGeometricBound ((b - a : ℕ) : ℝ) α := by
  have htriv : ‖∑ n ∈ Ico a b, additiveCharacter α n‖ ≤ ((b - a : ℕ) : ℝ) := by
    apply (norm_sum_le _ _).trans
    simp only [norm_additiveCharacter, sum_const, Nat.card_Ico, nsmul_eq_mul, mul_one]
    exact le_rfl
  unfold minorArcGeometricBound
  split_ifs with hz
  · exact htriv
  · apply le_min htriv
    have h := minor_arc_unit_geometric (norm_additiveCharacter α 1) hz a b
    have he : (∑ n ∈ Ico a b, additiveCharacter α n) =
        ∑ n ∈ Ico a b, additiveCharacter α 1 ^ n :=
      sum_congr rfl (fun n _ => additiveCharacter_pow α n)
    rw [← he] at h
    exact h

end TwoPointCorrelations

end OAI
