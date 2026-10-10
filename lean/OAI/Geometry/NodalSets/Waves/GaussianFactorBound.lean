import Mathlib.Analysis.Normed.Module.FiniteDimension
import OAI.Geometry.NodalSets.Waves.GaussianFactor

namespace OAI

namespace Yau.Probability
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]
local notation "E" => EuclideanSpace ℝ ι

lemma covarianceFactor_norm_sq (T : F →L[ℝ] E) (v : E) :
    ‖covarianceFactor T v‖^2 = ‖T.adjoint v‖^2 := by
  simpa only [real_inner_self_eq_norm_sq] using covarianceFactor_inner T v v

lemma covarianceFactor_lower (T : F →L[ℝ] E) (a : ℝ) (ha : 0 < a)
    (h : ∀ v : E, a*‖v‖^2 ≤ ‖T.adjoint v‖^2) (v : E) :
    Real.sqrt a * ‖v‖ ≤ ‖covarianceFactor T v‖ := by
  have hs := Real.sq_sqrt ha.le
  have hb := h v
  rw [← covarianceFactor_norm_sq T v] at hb
  nlinarith [sq_nonneg (Real.sqrt a*‖v‖-‖covarianceFactor T v‖),
    norm_nonneg (covarianceFactor T v), norm_nonneg v, Real.sqrt_nonneg a]

lemma covarianceFactor_bijective (T : F →L[ℝ] E) (a : ℝ) (ha : 0 < a)
    (h : ∀ v : E, a*‖v‖^2 ≤ ‖T.adjoint v‖^2) :
    Function.Bijective (covarianceFactor T) := by
  have hi : Function.Injective (covarianceFactor T) := by
    apply (covarianceFactor T).ker_eq_bot.mp
    rw [LinearMap.ker_eq_bot']
    intro v hv
    change covarianceFactor T v = 0 at hv
    have hb := covarianceFactor_lower T a ha h v
    rw [hv,norm_zero] at hb
    have hz : ‖v‖ = 0 := by nlinarith [Real.sqrt_pos.mpr ha, norm_nonneg v]
    exact norm_eq_zero.mp hz
  exact ⟨hi, LinearMap.injective_iff_surjective.mp hi⟩

variable [MeasurableSpace F] [BorelSpace F]

lemma exists_gaussian_factor_equiv (T : F →L[ℝ] E) (a : ℝ) (ha : 0 < a)
    (h : ∀ v : E, a*‖v‖^2 ≤ ‖T.adjoint v‖^2) :
    ∃ L : E ≃L[ℝ] E,
      (stdGaussian F).map T = (stdGaussian E).map L ∧
      ‖L.symm.toContinuousLinearMap‖ ≤ (Real.sqrt a)⁻¹ := by
  let L := (LinearEquiv.ofBijective (covarianceFactor T).toLinearMap
    (covarianceFactor_bijective T a ha h)).toContinuousLinearEquiv
  refine ⟨L, gaussian_covariance_factorization T, ?_⟩
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  have hb := covarianceFactor_lower T a ha h (L.symm v)
  change Real.sqrt a*‖L.symm v‖ ≤ ‖L (L.symm v)‖ at hb
  rw [L.apply_symm_apply] at hb
  change ‖L.symm v‖ ≤ _
  rw [inv_mul_eq_div]
  exact (le_div_iff₀ (Real.sqrt_pos.mpr ha)).mpr (by simpa [mul_comm] using hb)

end
end Yau.Probability

end OAI
