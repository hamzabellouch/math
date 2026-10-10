import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralWeakFluxConstant
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

namespace OAI

/-! The continuous primitive represented by an inhomogeneous weak flux. -/

open Set MeasureTheory
open scoped ContDiff
namespace DefocusingNLS

theorem spectralCompactTest_integrationByParts (φ : ℝ → ℝ) (P G : ℝ → ℂ)
    (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hP : ∀ x, HasDerivAt P (G x) x) (hG : Continuous G) :
    (∫ x, deriv φ x • P x) = -(∫ x, φ x • G x) := by
  have hPc : Continuous P := (show Differentiable ℝ P from fun x => (hP x).differentiableAt).continuous
  have hφd : Continuous (deriv φ) := hφ.continuous_deriv (by simp)
  have hp := integral_bilinear_hasDerivAt_right_eq_neg_left_of_integrable
    (L := ContinuousLinearMap.lsmul ℝ ℝ)
    (fun x _ => (hφ.differentiable (by simp) x).hasDerivAt)
    (fun x _ => hP x)
    (hG.locallyIntegrable.integrable_smul_left_of_hasCompactSupport hφ.continuous hφc)
    (hPc.locallyIntegrable.integrable_smul_left_of_hasCompactSupport hφd hφc.deriv)
    (hPc.locallyIntegrable.integrable_smul_left_of_hasCompactSupport hφ.continuous hφc)
  simpa only [neg_neg,ContinuousLinearMap.lsmul_apply] using congrArg Neg.neg hp.symm

theorem spectralWeakFlux_primitive (a b : ℝ) (hab : a < b) (F G : ℝ → ℂ)
    (hF : LocallyIntegrable F) (hG : Continuous G)
    (hw : ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ Icc a b → (∫ x, deriv φ x • F x) = -(∫ x, φ x • G x)) :
    ∃ P : ℝ → ℂ, (∀ x, HasDerivAt P (G x) x) ∧
      ∀ᵐ x, x ∈ Ioo a b → F x=P x := by
  let P := fun t => ∫ x in a..t, G x
  have hd (x : ℝ) : HasDerivAt P (G x) x :=
    intervalIntegral.integral_hasDerivAt_right (hG.intervalIntegrable a x)
      hG.aestronglyMeasurable.stronglyMeasurableAtFilter hG.continuousAt
  have hc : Continuous P := (show Differentiable ℝ P from fun x => (hd x).differentiableAt).continuous
  obtain ⟨c,he⟩ := spectralWeakFlux_constant a b hab (fun x => F x-P x)
    (hF.sub (hc.locallyIntegrable (μ := volume))) (by
      intro φ hφ hφc hφs
      have h1 := hF.integrable_smul_left_of_hasCompactSupport
        (hφ.continuous_deriv (by simp)) hφc.deriv
      have h2 := (hc.locallyIntegrable (μ := volume)).integrable_smul_left_of_hasCompactSupport
        (hφ.continuous_deriv (by simp)) hφc.deriv
      simp only [smul_sub]
      rw [integral_sub h1 h2,hw φ hφ hφc hφs,
        spectralCompactTest_integrationByParts φ P G hφ hφc hd hG,sub_self])
  refine ⟨fun x => P x+c,fun x => (hd x).add_const c,?_⟩
  filter_upwards [he] with x hx hxab
  have heq : F x=c+P x := sub_eq_iff_eq_add.mp (hx hxab)
  simpa only [add_comm] using heq

end DefocusingNLS

end OAI
