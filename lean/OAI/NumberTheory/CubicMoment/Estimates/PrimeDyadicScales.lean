import OAI.NumberTheory.CubicMoment.Estimates.PrimeSmoothingScale

namespace OAI

/-! A finite contracting-dyad partition stopping at the square-root scale. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma primeDyadic_scale_sum (X : ℝ) (N : ℕ) :
    (∑ j ∈ Finset.range N, X/(2:ℝ)^(j+1)) = X-X/(2:ℝ)^N := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ,ih]
    rw [pow_succ]
    field_simp
    ring

lemma primeDyadic_scale_sum_le {X : ℝ} (hX : 0 ≤ X) (N : ℕ) :
    (∑ j ∈ Finset.range N, X/(2:ℝ)^(j+1)) ≤ X := by
  rw [primeDyadic_scale_sum]
  linarith [div_nonneg hX (show (0:ℝ) ≤ 2^N by positivity)]

lemma exists_primeDyadic_sqrt_split {X : ℝ} (hX : 1 ≤ X) :
    ∃ N : ℕ, Real.sqrt X ≤ X/(2:ℝ)^N ∧ X/(2:ℝ)^N ≤ 2*Real.sqrt X ∧
      X/(2:ℝ)^N ≤ X ∧
      ∀ j < N, Real.sqrt X ≤ X/(2:ℝ)^(j+1) ∧ X/(2:ℝ)^(j+1) ≤ X := by
  have hX0 : 0 ≤ X := by linarith
  have hs1 : 1 ≤ Real.sqrt X := (Real.le_sqrt (by norm_num) hX0).mpr (by simpa using hX)
  obtain ⟨N,hN,hN'⟩ := exists_nat_pow_near hs1 (by norm_num : (1:ℝ) < 2)
  have hlow : Real.sqrt X ≤ X/(2:ℝ)^N := by
    apply (le_div_iff₀ (by positivity : (0:ℝ) < 2^N)).mpr
    have hh := mul_le_mul_of_nonneg_left hN (Real.sqrt_nonneg X)
    nlinarith [Real.sq_sqrt hX0]
  have hhigh : X/(2:ℝ)^N ≤ 2*Real.sqrt X := by
    apply (div_le_iff₀ (by positivity : (0:ℝ) < 2^N)).mpr
    rw [pow_succ] at hN'
    have hh := mul_le_mul_of_nonneg_left hN'.le (Real.sqrt_nonneg X)
    nlinarith [Real.sq_sqrt hX0]
  refine ⟨N,hlow,hhigh,div_le_self hX0 (one_le_pow₀ (by norm_num)),?_⟩
  intro j hj
  constructor
  · apply hlow.trans
    exact div_le_div_of_nonneg_left hX0 (by positivity)
      (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) (by omega))
  · exact div_le_self hX0 (one_le_pow₀ (by norm_num))

end CubicFirstMoment

end

end OAI
