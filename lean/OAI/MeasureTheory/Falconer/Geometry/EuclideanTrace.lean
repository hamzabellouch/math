import OAI.MeasureTheory.Falconer.Angular.SphereModel
import OAI.MeasureTheory.Falconer.Graphs.FiberPairing

namespace OAI

/-! The Fourier energy pairing in the dimension of a projected hyperplane. -/

namespace Falconer
open Set MeasureTheory PlanarFalconer
open scoped ENNReal FourierTransform SchwartzMap

theorem euclidean_weighted_cauchy {n : ℕ} (hn : 0 < n)
    (F G : Space n → ℝ) (hF : Measurable F) (hG : Measurable G)
    (hFn : ∀ x, 0 ≤ F x) (hGn : ∀ x, 0 ≤ G x) (a : ℝ) :
    (∫⁻ x : Space n, ENNReal.ofReal (F x*G x)) ≤
      (∫⁻ x : Space n, ENNReal.ofReal ((F x)^2*‖x‖^a))^(1/2 : ℝ) *
        (∫⁻ x : Space n, ENNReal.ofReal ((G x)^2*‖x‖^(-a)))^(1/2 : ℝ) := by
  let : Nontrivial (Space n) := Module.nontrivial_of_finrank_pos (R := ℝ)
    (by simpa [Space] using hn)
  let A : Space n → ℝ≥0∞ := fun x => ENNReal.ofReal (F x*‖x‖^(a/2))
  let B : Space n → ℝ≥0∞ := fun x => ENNReal.ofReal (G x*‖x‖^(-a/2))
  have hA : Measurable A := by dsimp [A]; fun_prop
  have hB : Measurable B := by dsimp [B]; fun_prop
  have hprod : (∫⁻ x : Space n, ENNReal.ofReal (F x*G x)) = ∫⁻ x : Space n, (A*B) x := by
    apply lintegral_congr_ae
    have hne : ∀ᵐ x : Space n ∂volume, x ≠ 0 := by rw [ae_iff]; simp
    filter_upwards [hne] with x hx
    dsimp [A,B]
    rw [← ENNReal.ofReal_mul (mul_nonneg (hFn x) (Real.rpow_nonneg (norm_nonneg x) _)),
      show -a/2 = -(a/2) by ring, weighted_power_cancel (norm_pos_iff.mpr hx)]
  have hsqA : (∫⁻ x : Space n, A x^(2 : ℝ)) =
      ∫⁻ x : Space n, ENNReal.ofReal ((F x)^2*‖x‖^a) := by
    apply lintegral_congr
    intro x
    dsimp [A]
    rw [ENNReal.rpow_two, ← ENNReal.ofReal_pow
      (mul_nonneg (hFn x) (Real.rpow_nonneg (norm_nonneg x) _)),
      weighted_power_square (norm_nonneg x)]
  have hsqB : (∫⁻ x : Space n, B x^(2 : ℝ)) =
      ∫⁻ x : Space n, ENNReal.ofReal ((G x)^2*‖x‖^(-a)) := by
    apply lintegral_congr
    intro x
    dsimp [B]
    rw [ENNReal.rpow_two, ← ENNReal.ofReal_pow
      (mul_nonneg (hGn x) (Real.rpow_nonneg (norm_nonneg x) _)),
      weighted_power_square (norm_nonneg x)]
  rw [hprod, ← hsqA, ← hsqB]
  exact ENNReal.lintegral_mul_le_Lp_mul_Lq volume
    (show (2 : ℝ).HolderConjugate 2 by norm_num [Real.holderConjugate_iff])
    hA.aemeasurable hB.aemeasurable

theorem euclidean_schwartz_measure_pairing {n : ℕ} (μ : Measure (Space n))
    [IsFiniteMeasure μ] (f : 𝓢(Space n, ℂ)) :
    (∫ x, f x ∂μ) = ∫ ξ : Space n, 𝓕⁻ f ξ * sourceFourier μ ξ := by
  have h := sourceFourier_integral_swap μ
    ((𝓕⁻ f : 𝓢(Space n, ℂ)) : Space n → ℂ) (𝓕⁻ f).integrable
  simpa only [← SchwartzMap.fourier_coe, FourierTransform.fourier_fourierInv_eq] using h.symm

theorem euclidean_schwartz_inverse_weight {n : ℕ} (f : 𝓢(Space n, ℂ)) (v : ℝ) :
    (∫⁻ ξ : Space n, ENNReal.ofReal (‖𝓕⁻ f ξ‖^2 * ‖ξ‖^v)) =
      ∫⁻ ξ : Space n, ENNReal.ofReal (‖𝓕 f ξ‖^2 * ‖ξ‖^v) := by
  have he (ξ : Space n) : 𝓕⁻ f ξ = 𝓕 f (-ξ) := by
    rw [SchwartzMap.fourierInv_coe, Real.fourierInv_eq_fourier_neg]
    rfl
  simp_rw [he]
  simpa only [norm_neg] using lintegral_neg_eq_self (μ := volume)
    (fun ξ : Space n => ENNReal.ofReal (‖𝓕 f ξ‖^2 * ‖ξ‖^v))

theorem euclidean_fourier_pairing {n : ℕ} (μ : Measure (Space n))
    [IsFiniteMeasure μ] (f : 𝓢(Space n, ℂ)) {u : ℝ} (hu : 0 < u) (hun : u < n) :
    (ENNReal.ofReal (sourceEnergyConstant n u))^(1/2 : ℝ) *
      ENNReal.ofReal (‖∫ x, f x ∂μ‖) ≤
      (rieszEnergyOn μ u)^(1/2 : ℝ) *
        (∫⁻ ξ : Space n, ENNReal.ofReal (‖𝓕 f ξ‖^2 * ‖ξ‖^((n : ℝ)-u)))^(1/2 : ℝ) := by
  have hn : 0 < n := by exact_mod_cast (hu.trans hun)
  have hnorm : ENNReal.ofReal (‖∫ x, f x ∂μ‖) ≤
      ∫⁻ ξ : Space n, ENNReal.ofReal (‖𝓕⁻ f ξ‖ * ‖sourceFourier μ ξ‖) := by
    rw [euclidean_schwartz_measure_pairing]
    simpa only [← ofReal_norm, norm_mul] using enorm_integral_le_lintegral_enorm
      (fun ξ : Space n => 𝓕⁻ f ξ * sourceFourier μ ξ)
  have hcs := euclidean_weighted_cauchy hn (fun ξ => ‖𝓕⁻ f ξ‖)
    (fun ξ => ‖sourceFourier μ ξ‖) (by fun_prop)
    (by unfold sourceFourier; fun_prop) (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
    ((n : ℝ)-u)
  rw [euclidean_schwartz_inverse_weight] at hcs
  have h := mul_le_mul_right (hnorm.trans hcs)
    ((ENNReal.ofReal (sourceEnergyConstant n u))^(1/2 : ℝ))
  have hdim : Module.finrank ℝ (Space n) = n := by simp [Space]
  have henergy := source_fourier_energy_identity μ hu (by simpa [hdim] using hun)
  rw [hdim] at henergy
  rw [henergy,
    ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1/2)]
  have he : (∫⁻ ξ : Space n, ENNReal.ofReal (‖sourceFourier μ ξ‖^2 * ‖ξ‖^(-((n : ℝ)-u)))) =
      ∫⁻ ξ : Space n, ENNReal.ofReal (‖sourceFourier μ ξ‖^2) *
        ENNReal.ofReal (‖ξ‖^(u-n)) := by
    apply lintegral_congr
    intro ξ
    rw [neg_sub, ENNReal.ofReal_mul (sq_nonneg _)]
  rw [he] at h
  convert h using 1; ac_rfl

end Falconer

end OAI
