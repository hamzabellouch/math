import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadianFourierLocalization
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.MeasureTheory.Integral.DominatedConvergence

namespace OAI

/-! # The physical localized Fourier series

Absolute summability gives the actual continuous periodic function on Euclidean
space. Its localized Fourier transform is the limit of the exact finite-cutoff
formula; domination is supplied by the integrable Schwartz cutoff.
-/

open Filter MeasureTheory Topology
open scoped SchwartzMap RealInnerProductSpace

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

noncomputable def spatialFourierCharacter (n : frequencyLattice) (y : E) : ℂ :=
  Complex.exp ((⟪y, (n : E)⟫ : ℝ) * Complex.I)

@[simp] theorem spatialFourierCharacter_norm (n : frequencyLattice) (y : E) :
    ‖spatialFourierCharacter n y‖ = 1 := Complex.norm_exp_ofReal_mul_I _

theorem continuous_spatialFourierCharacter (n : frequencyLattice) :
    Continuous (spatialFourierCharacter n) := by unfold spatialFourierCharacter; fun_prop

noncomputable def spatialFourierSeries (v : frequencyLattice → ℂ) (y : E) : ℂ :=
  ∑' n, v n * spatialFourierCharacter n y

theorem summable_spatialFourierSeries (v : frequencyLattice → ℂ)
    (hv : Summable (fun n => ‖v n‖)) (y : E) :
    Summable (fun n => v n * spatialFourierCharacter n y) := by
  apply Summable.of_norm
  simpa only [norm_mul, spatialFourierCharacter_norm, mul_one] using hv

theorem continuous_spatialFourierSeries (v : frequencyLattice → ℂ)
    (hv : Summable (fun n => ‖v n‖)) : Continuous (spatialFourierSeries v) := by
  apply continuous_tsum (u := fun n => ‖v n‖)
  · intro n
    exact continuous_const.mul (continuous_spatialFourierCharacter n)
  · exact hv
  · intro n y
    simp only [norm_mul, spatialFourierCharacter_norm, mul_one, le_refl]

theorem spatialFourierSeries_norm_le (v : frequencyLattice → ℂ)
    (hv : Summable (fun n => ‖v n‖)) (y : E) :
    ‖spatialFourierSeries v y‖ ≤ ∑' n, ‖v n‖ := by
  unfold spatialFourierSeries
  have hn : Summable (fun n => ‖v n * spatialFourierCharacter n y‖) := by
    simpa only [norm_mul, spatialFourierCharacter_norm, mul_one] using hv
  simpa only [norm_mul, spatialFourierCharacter_norm, mul_one] using norm_tsum_le_tsum_norm hn

noncomputable def localizedFourierSeries (L : ℝ) (χ : 𝓢(E, ℂ))
    (v : frequencyLattice → ℂ) (y : E) : ℂ :=
  χ (L⁻¹ • y) * spatialFourierSeries v (L⁻¹ • y)

theorem continuous_localizedFourierSeries (L : ℝ) (χ : 𝓢(E, ℂ))
    (v : frequencyLattice → ℂ) (hv : Summable (fun n => ‖v n‖)) :
    Continuous (localizedFourierSeries L χ v) := by
  exact (χ.continuous.comp (continuous_const_smul L⁻¹)).mul
    ((continuous_spatialFourierSeries v hv).comp (continuous_const_smul L⁻¹))

theorem integrable_localizedFourierSeries (L : ℝ) (hL : 0 < L) (χ : 𝓢(E, ℂ))
    (v : frequencyLattice → ℂ) (hv : Summable (fun n => ‖v n‖)) :
    Integrable (localizedFourierSeries L χ v) := by
  apply (χ.integrable.comp_smul (inv_ne_zero hL.ne')).mul_bdd
    (((continuous_spatialFourierSeries v hv).comp (continuous_const_smul L⁻¹)).aestronglyMeasurable)
  exact Eventually.of_forall (fun y => spatialFourierSeries_norm_le v hv (L⁻¹ • y))

/-- The infinite physical Fourier transform is the limit of the finite cutoff transforms. -/
theorem hasSum_localizedFourierSeries_transform (L : ℝ) (hL : 0 < L)
    (χ : 𝓢(E, ℂ)) (v : frequencyLattice → ℂ)
    (hv : Summable (fun n => ‖v n‖)) (ξ : E) :
    HasSum (fun n => (L ^ (12 : ℕ) : ℝ) •
      (v n * radianFourierKernel χ (L • ξ - n)))
      (radianFourierIntegral (localizedFourierSeries L χ v) ξ) := by
  classical
  let G : frequencyLattice → E → ℂ := fun n y =>
    Complex.exp ((-⟪y, ξ⟫ : ℝ) * Complex.I) * localizedFourierPolynomial L χ {n} v y
  have hχ : Integrable (fun y : E => χ (L⁻¹ • y)) :=
    χ.integrable.comp_smul (inv_ne_zero hL.ne')
  have hnorm (n : frequencyLattice) (y : E) : ‖G n y‖ = ‖χ (L⁻¹ • y)‖ * ‖v n‖ := by
    simp only [G, localizedFourierPolynomial, Finset.sum_singleton, norm_mul,
      Complex.norm_exp_ofReal_mul_I, one_mul, mul_one]
  have hG (n : frequencyLattice) : Integrable (G n) := by
    apply (hχ.norm.mul_const ‖v n‖).mono' (by
      have hc : Continuous (G n) := by
        have hcχ : Continuous χ := χ.continuous
        unfold G localizedFourierPolynomial
        simp only [Finset.sum_singleton]
        fun_prop
      exact hc.aestronglyMeasurable)
    exact Eventually.of_forall (fun y => (hnorm n y).le)
  have hnormI (n : frequencyLattice) : (∫ y, ‖G n y‖) = (∫ y, ‖χ (L⁻¹ • y)‖) * ‖v n‖ := by
    simp_rw [hnorm]
    exact integral_mul_const _ _
  have hGI : Summable (fun n => ∫ y, ‖G n y‖) := by
    simpa only [hnormI] using hv.mul_left (∫ y, ‖χ (L⁻¹ • y)‖)
  have hsum := hasSum_integral_of_summable_integral_norm hG hGI
  have hpoint (y : E) : (∑' n, G n y) =
      Complex.exp ((-⟪y, ξ⟫ : ℝ) * Complex.I) * localizedFourierSeries L χ v y := by
    simp only [G, localizedFourierPolynomial, Finset.sum_singleton,
      localizedFourierSeries, spatialFourierSeries, spatialFourierCharacter,
      ← tsum_mul_left]
  have hterm (n : frequencyLattice) : (∫ y, G n y) =
      (L ^ (12 : ℕ) : ℝ) • (v n * radianFourierKernel χ (L • ξ - n)) := by
    simpa only [radianFourierIntegral, G, Finset.sum_singleton] using
      localizedFourierPolynomial_transform L hL χ {n} v ξ
  simpa only [hterm, hpoint, radianFourierIntegral] using hsum

theorem tendsto_localizedFourierPolynomial_transform (L : ℝ) (hL : 0 < L)
    (χ : 𝓢(E, ℂ)) (v : frequencyLattice → ℂ)
    (hv : Summable (fun n => ‖v n‖)) (ξ : E) :
    Tendsto (fun S : Finset frequencyLattice =>
      radianFourierIntegral (localizedFourierPolynomial L χ S v) ξ) atTop
      (𝓝 (radianFourierIntegral (localizedFourierSeries L χ v) ξ)) := by
  have h := hasSum_localizedFourierSeries_transform L hL χ v hv ξ
  change Tendsto (fun S : Finset frequencyLattice => ∑ n ∈ S,
    (L ^ (12 : ℕ) : ℝ) • (v n * radianFourierKernel χ (L • ξ - n))) atTop _ at h
  simpa only [localizedFourierPolynomial_transform L hL, Finset.smul_sum] using h

end DefocusingNLS

end OAI
