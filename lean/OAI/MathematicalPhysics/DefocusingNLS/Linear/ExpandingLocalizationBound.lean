import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingPhysicalLocalization
import OAI.MathematicalPhysics.DefocusingNLS.Linear.LocalizationFourierEnergy
import OAI.MathematicalPhysics.DefocusingNLS.Linear.LocalizationFatou

namespace OAI

/-! # Uniform localization on the actual expanding-torus space

The finite-cutoff estimate passes to the continuous periodic Fourier series.
The coefficient normalization is exactly the Y_L normalization already used
for the expanding flow, and every constant is independent of L ≥ 1.
-/

open Filter MeasureTheory Topology
open scoped SchwartzMap ENNReal

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

private theorem exists_localizedFourierSeries_energy_bound (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (χ : 𝓢(E, ℂ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (L : ℝ), 1 ≤ L → ∀ (v : frequencyLattice → ℂ),
      Summable (fun n => ‖v n‖) →
      Summable (fun n => expandingSobolevWeightSq a k L n * ‖v n‖ ^ 2) →
      Integrable (fun ξ => ‖ξ‖ ^ (2 * (6 - a)) *
        ‖radianFourierIntegral (localizedFourierSeries L χ v) ξ‖ ^ 2) ∧
      Integrable (fun ξ => ‖ξ‖ ^ (2 * k) *
        ‖radianFourierIntegral (localizedFourierSeries L χ v) ξ‖ ^ 2) ∧
      homogeneousFourierEnergy (6 - a) (localizedFourierSeries L χ v) +
        homogeneousFourierEnergy k (localizedFourierSeries L χ v) ≤
          C * ∑' n, expandingSobolevWeightSq a k L n * ‖v n‖ ^ 2 := by
  obtain ⟨C, hC, hfinite⟩ := exists_localizedFourierPolynomial_energy_bound a k ha ha1 hk χ
  refine ⟨2 * C, by positivity, ?_⟩
  intro L hL v hv hW
  have hLp : 0 < L := by linarith
  let B : ℝ := C * ∑' n, expandingSobolevWeightSq a k L n * ‖v n‖ ^ 2
  have hB : 0 ≤ B := mul_nonneg hC (tsum_nonneg (fun n =>
    mul_nonneg (expandingSobolevWeightSq_pos a k L hL n).le (sq_nonneg _)))
  have hfiniteB (S : Finset frequencyLattice) :
      homogeneousFourierEnergy (6 - a) (localizedFourierPolynomial L χ S v) +
        homogeneousFourierEnergy k (localizedFourierPolynomial L χ S v) ≤ B := by
    exact (hfinite L hL S v).trans (mul_le_mul_of_nonneg_left
      (hW.sum_le_tsum S (fun n _ =>
        mul_nonneg (expandingSobolevWeightSq_pos a k L hL n).le (sq_nonneg _))) hC)
  have horder (s : ℝ) (hs : s = 6 - a ∨ s = k) :
      Integrable (fun ξ => ‖ξ‖ ^ (2 * s) *
        ‖radianFourierIntegral (localizedFourierSeries L χ v) ξ‖ ^ 2) ∧
      homogeneousFourierEnergy s (localizedFourierSeries L χ v) ≤ B := by
    have hsp : 0 ≤ s := by rcases hs with rfl | rfl <;> linarith
    have hb (S : Finset frequencyLattice) :
        homogeneousFourierEnergy s (localizedFourierPolynomial L χ S v) ≤ B := by
      rcases hs with rfl | rfl
      · exact (le_add_of_nonneg_right (integral_nonneg (fun ξ => by positivity))).trans (hfiniteB S)
      · exact (le_add_of_nonneg_left (integral_nonneg (fun ξ => by positivity))).trans (hfiniteB S)
    have hlim (ξ : E) := tendsto_localizedFourierPolynomial_transform L hLp χ v hv ξ
    have hpass := localization_integral_limit
      (fun S ξ => ‖ξ‖ ^ (2 * s) *
        ‖radianFourierIntegral (localizedFourierPolynomial L χ S v) ξ‖ ^ 2)
      (fun ξ => ‖ξ‖ ^ (2 * s) *
        ‖radianFourierIntegral (localizedFourierSeries L χ v) ξ‖ ^ 2)
      B hB (fun S => integrable_localizedFourierPolynomial_energy s L hsp hLp χ S v)
      (fun _ _ => by positivity) (fun _ => by positivity)
      (fun ξ => ((hlim ξ).norm.pow 2).const_mul _) hb
    exact hpass
  have hlow := horder (6 - a) (Or.inl rfl)
  have hhigh := horder k (Or.inr rfl)
  refine ⟨hlow.1, hhigh.1, ?_⟩
  have hlo := hlow.2
  have hhi := hhigh.2
  dsimp [B] at hlo hhi
  nlinarith

private theorem expanding_coefficient_localization_energy (a k L : ℝ) (hL : 1 ≤ L)
    (f : FourierL2) (n : frequencyLattice) :
    expandingSobolevWeightSq a k L n * ‖expandingFourierCoefficient a k L f n‖ ^ 2 =
      ((2 * Real.pi) ^ (12 : ℕ))⁻¹ * ‖f n‖ ^ 2 := by
  unfold expandingFourierCoefficient
  rw [norm_mul, mul_pow, expanding_observation_weight_sq a k L hL]
  calc
    _ = ((2 * Real.pi) ^ (12 : ℕ))⁻¹ *
        (expandingSobolevWeightSq a k L n * (expandingSobolevWeightSq a k L n)⁻¹) *
          ‖f n‖ ^ 2 := by ring
    _ = _ := by rw [mul_inv_cancel₀ (expandingSobolevWeightSq_pos a k L hL n).ne']; ring

/-- The actual physical cutoff has a uniform two-order homogeneous Fourier bound.
This is the squared version of (lin:J-bound), with fixed Fourier normalization absorbed in C. -/
theorem exists_expandingPhysicalLocalization_bound (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (χ : 𝓢(E, ℂ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (L : ℝ), 1 ≤ L → ∀ (f : FourierL2),
      Integrable (fun ξ => ‖ξ‖ ^ (2 * (6 - a)) *
        ‖radianFourierIntegral (expandingPhysicalLocalization a k L χ f) ξ‖ ^ 2) ∧
      Integrable (fun ξ => ‖ξ‖ ^ (2 * k) *
        ‖radianFourierIntegral (expandingPhysicalLocalization a k L χ f) ξ‖ ^ 2) ∧
      homogeneousFourierEnergy (6 - a) (expandingPhysicalLocalization a k L χ f) +
        homogeneousFourierEnergy k (expandingPhysicalLocalization a k L χ f) ≤ C * ‖f‖ ^ 2 := by
  obtain ⟨C, hC, hbound⟩ := exists_localizedFourierSeries_energy_bound a k ha ha1 hk χ
  refine ⟨C * ((2 * Real.pi) ^ (12 : ℕ))⁻¹, by positivity, ?_⟩
  intro L hL f
  have hs : Summable (fun n : frequencyLattice => ‖f n‖ ^ 2) := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
      (lp.memℓp f).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
  have hW : Summable (fun n => expandingSobolevWeightSq a k L n *
      ‖expandingFourierCoefficient a k L f n‖ ^ 2) := by
    simp only [expanding_coefficient_localization_energy a k L hL]
    exact hs.mul_left _
  have heq : (∑' n, expandingSobolevWeightSq a k L n *
      ‖expandingFourierCoefficient a k L f n‖ ^ 2) =
        ((2 * Real.pi) ^ (12 : ℕ))⁻¹ * ‖f‖ ^ 2 := by
    simp_rw [expanding_coefficient_localization_energy a k L hL]
    rw [tsum_mul_left]
    congr 1
    have he := lp.norm_rpow_eq_tsum (p := 2) (by norm_num) f
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using he.symm
  rw [expandingPhysicalLocalization_eq_series a k L ha ha1 hk hL]
  have h := hbound L hL (expandingFourierCoefficient a k L f)
    (summable_norm_expandingFourierCoefficient a k L ha ha1 hk hL f) hW
  refine ⟨h.1, h.2.1, ?_⟩
  have hb := h.2.2
  rw [heq] at hb
  simpa only [mul_assoc] using hb

end DefocusingNLS

end OAI
