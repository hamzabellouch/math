import OAI.NumberTheory.CubicMoment.Estimates.PrimeIndicatorPowers

namespace OAI

/-! Explicit error exponents, independent of the coefficient-bound constants. -/
noncomputable section
open Filter
namespace CubicFirstMoment

lemma absorb_prime_coordinate_error_explicit {e d C : ℝ} (he : 0 < e) (hd : 0 < d)
    (hC : 0 ≤ C) :
    ∃ T : ℝ, 1 ≤ T ∧ ∀ Y : ℝ, T ≤ Y →
      2*Y^(7/3-e)+2*C*(2*Y)^(7/3-d) ≤ Y^(7/3-min e d/2) := by
  let δ := min e d
  let K := 2+2*C*2^(7/3-d)
  have hδ : 0 < δ := lt_min he hd
  obtain ⟨T,hT⟩ := eventually_atTop.mp
    ((tendsto_rpow_atTop (show 0 < δ/2 by positivity)).eventually_ge_atTop K)
  refine ⟨max 1 T,le_max_left _ _,?_⟩
  intro Y hY
  have hY1 : 1 ≤ Y := (le_max_left _ _).trans hY
  have hYp : 0 < Y := zero_lt_one.trans_le hY1
  have h₁ : Y^(7/3-e) ≤ Y^(7/3-δ) :=
    Real.rpow_le_rpow_of_exponent_le hY1 (by dsimp [δ]; linarith [min_le_left e d])
  have h₂ : Y^(7/3-d) ≤ Y^(7/3-δ) :=
    Real.rpow_le_rpow_of_exponent_le hY1 (by dsimp [δ]; linarith [min_le_right e d])
  calc
    _ = 2*Y^(7/3-e)+(2*C*2^(7/3-d))*Y^(7/3-d) := by
      rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hYp.le]
      ring
    _ ≤ 2*Y^(7/3-δ)+(2*C*2^(7/3-d))*Y^(7/3-δ) := by gcongr
    _ = K*Y^(7/3-δ) := by dsimp [K]; ring
    _ ≤ Y^(δ/2)*Y^(7/3-δ) := mul_le_mul_of_nonneg_right
      (hT Y ((le_max_right _ _).trans hY)) (Real.rpow_nonneg hYp.le _)
    _ = _ := by rw [← Real.rpow_add hYp]; congr 1; ring

end CubicFirstMoment

end

end OAI
