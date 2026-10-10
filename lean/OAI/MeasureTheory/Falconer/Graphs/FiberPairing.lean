import OAI.MeasureTheory.Falconer.Fourier.FourierEnergy
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.MeasureTheory.Integral.MeanInequalities

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal NNReal FourierTransform SchwartzMap

theorem weighted_power_cancel {x : ℝ} (hx : 0 < x) (A B a : ℝ) :
    (A*x^a)*(B*x^(-a)) = A*B := by
  calc
    _ = (A*B)*(x^a*x^(-a)) := by ring
    _ = _ := by rw [← Real.rpow_add hx,add_neg_cancel,Real.rpow_zero,mul_one]

theorem weighted_power_square {x : ℝ} (hx : 0 ≤ x) (A a : ℝ) :
    (A*x^(a/2))^2 = A^2*x^a := by
  rw [mul_pow, ← Real.rpow_mul_natCast hx]
  congr 2
  ring

theorem line_weighted_cauchy (F G : ℝ → ℝ) (hF : Measurable F) (hG : Measurable G)
    (hFn : ∀ x, 0 ≤ F x) (hGn : ∀ x, 0 ≤ G x) (u : ℝ) :
    (∫⁻ x : ℝ, ENNReal.ofReal (F x*G x)) ≤
      (∫⁻ x : ℝ, ENNReal.ofReal ((F x)^2*|x|^(1-u)))^(1/2 : ℝ) *
      (∫⁻ x : ℝ, ENNReal.ofReal ((G x)^2*|x|^(u-1)))^(1/2 : ℝ) := by
  let A : ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal (F x * |x|^((1-u)/2))
  let B : ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal (G x * |x|^((u-1)/2))
  have hA : Measurable A := by dsimp [A]; fun_prop
  have hB : Measurable B := by dsimp [B]; fun_prop
  have hprod : (∫⁻ x : ℝ, ENNReal.ofReal (F x*G x)) = ∫⁻ x : ℝ, (A*B) x := by
    apply lintegral_congr_ae
    have hne : ∀ᵐ x : ℝ ∂volume, x ≠ 0 := by rw [ae_iff]; simp
    filter_upwards [hne] with x hx
    dsimp [A,B]
    rw [← ENNReal.ofReal_mul (mul_nonneg (hFn x) (Real.rpow_nonneg (abs_nonneg x) _)),
      show (u-1)/2 = -((1-u)/2) by ring,
      weighted_power_cancel (abs_pos.mpr hx)]
  have hsqA : (∫⁻ x : ℝ, A x^(2 : ℝ)) =
      ∫⁻ x : ℝ, ENNReal.ofReal ((F x)^2*|x|^(1-u)) := by
    apply lintegral_congr
    intro x
    dsimp [A]
    rw [ENNReal.rpow_two, ← ENNReal.ofReal_pow
      (mul_nonneg (hFn x) (Real.rpow_nonneg (abs_nonneg x) _)),
      weighted_power_square (abs_nonneg x)]
  have hsqB : (∫⁻ x : ℝ, B x^(2 : ℝ)) =
      ∫⁻ x : ℝ, ENNReal.ofReal ((G x)^2*|x|^(u-1)) := by
    apply lintegral_congr
    intro x
    dsimp [B]
    rw [ENNReal.rpow_two, ← ENNReal.ofReal_pow
      (mul_nonneg (hGn x) (Real.rpow_nonneg (abs_nonneg x) _)),
      weighted_power_square (abs_nonneg x)]
  rw [hprod, ← hsqA, ← hsqB]
  exact ENNReal.lintegral_mul_le_Lp_mul_Lq volume
    (show (2 : ℝ).HolderConjugate 2 by norm_num [Real.holderConjugate_iff])
    hA.aemeasurable hB.aemeasurable

theorem schwartz_measure_pairing (μ : Measure ℝ) [IsFiniteMeasure μ] (f : 𝓢(ℝ, ℂ)) :
    (∫ x, f x ∂μ) = ∫ ξ : ℝ, (𝓕⁻ f) ξ * sourceFourier μ ξ := by
  have h := sourceFourier_integral_swap μ ((𝓕⁻ f : 𝓢(ℝ, ℂ)) : ℝ → ℂ) (𝓕⁻ f).integrable
  simpa only [← SchwartzMap.fourier_coe, FourierTransform.fourier_fourierInv_eq] using h.symm

theorem schwartz_inverse_weight (f : 𝓢(ℝ, ℂ)) (v : ℝ) :
    (∫⁻ ξ : ℝ, ENNReal.ofReal (‖(𝓕⁻ f) ξ‖^2 * |ξ|^v)) =
      ∫⁻ ξ : ℝ, ENNReal.ofReal (‖(𝓕 f) ξ‖^2 * |ξ|^v) := by
  have he (ξ : ℝ) : (𝓕⁻ f) ξ = (𝓕 f) (-ξ) := by
    rw [SchwartzMap.fourierInv_coe, Real.fourierInv_eq_fourier_neg]
    rfl
  simp_rw [he]
  simpa only [abs_neg] using lintegral_neg_eq_self (μ := volume)
    (fun ξ : ℝ => ENNReal.ofReal (‖(𝓕 f) ξ‖^2 * |ξ|^v))

theorem source_fourier_pairing (μ : Measure ℝ) [IsFiniteMeasure μ]
    (f : 𝓢(ℝ, ℂ)) {u : ℝ} (hu : 0 < u) (hu1 : u < 1) :
    (ENNReal.ofReal (sourceEnergyConstant 1 u))^(1/2 : ℝ) *
        ENNReal.ofReal (‖∫ x, f x ∂μ‖) ≤
      (rieszEnergyOn μ u)^(1/2 : ℝ) *
        (∫⁻ ξ : ℝ, ENNReal.ofReal (‖(𝓕 f) ξ‖^2 * |ξ|^(1-u)))^(1/2 : ℝ) := by
  have hnorm : ENNReal.ofReal (‖∫ x, f x ∂μ‖) ≤
      ∫⁻ ξ : ℝ, ENNReal.ofReal (‖(𝓕⁻ f) ξ‖ * ‖sourceFourier μ ξ‖) := by
    rw [schwartz_measure_pairing]
    simpa only [← ofReal_norm, norm_mul] using enorm_integral_le_lintegral_enorm
      (fun ξ : ℝ => (𝓕⁻ f) ξ * sourceFourier μ ξ)
  have hcs := line_weighted_cauchy (fun ξ => ‖(𝓕⁻ f) ξ‖)
    (fun ξ => ‖sourceFourier μ ξ‖) (by fun_prop)
    (by unfold sourceFourier; fun_prop) (fun _ => norm_nonneg _) (fun _ => norm_nonneg _) u
  rw [schwartz_inverse_weight] at hcs
  have h := mul_le_mul_right (hnorm.trans hcs)
    ((ENNReal.ofReal (sourceEnergyConstant 1 u))^(1/2 : ℝ))
  rw [line_fourier_energy_identity μ hu hu1,
    ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1/2)]
  have he : (∫⁻ ξ : ℝ, ENNReal.ofReal (‖sourceFourier μ ξ‖^2 * |ξ|^(u-1))) =
      ∫⁻ ξ : ℝ, ENNReal.ofReal (‖sourceFourier μ ξ‖^2) * ENNReal.ofReal (|ξ|^(u-1)) := by
    apply lintegral_congr
    intro ξ
    exact ENNReal.ofReal_mul (sq_nonneg _)
  rw [he] at h
  convert h using 1
  ac_rfl

end PlanarFalconer

end OAI
