import OAI.Analysis.KadisonKastler.ResolventCutLimit
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real

namespace OAI

/-! # Scalar vector measures of the bounded Tomita resolvent

The real continuous functional calculus, tested on one Hilbert vector,
is a positive functional. Riesz representation supplies the finite measure
needed to compare the modular phases and their spectral cuts.
-/

namespace KadisonKastler

open MeasureTheory
open scoped CompactlySupported

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def resolventVectorFunctional (R : H →L[ℂ] H) (hR : IsSelfAdjoint R) (x : H) :
    C_c(spectrum ℝ R, ℝ) →ₚ[ℝ] ℝ where
  toFun f := (inner ℂ x ((cfcHom hR f.toContinuousMap) x)).re
  map_add' f g := by
    change (inner ℂ x ((cfcHom hR (f.toContinuousMap + g.toContinuousMap)) x)).re = _
    rw [map_add, add_apply, inner_add_right, Complex.add_re]
  map_smul' a f := by
    change (inner ℂ x ((cfcHom hR (a • f.toContinuousMap)) x)).re = _
    rw [map_smul, smul_apply]
    simp only [← Complex.coe_smul, inner_smul_right, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, smul_eq_mul, RingHom.id_apply]
  monotone' f g hfg := by
    have hfgn : f.toContinuousMap ≤ g.toContinuousMap := hfg
    have hp : 0 ≤ cfcHom hR (g.toContinuousMap - f.toContinuousMap) :=
      map_nonneg (cfcHom hR) (sub_nonneg.mpr hfgn)
    have hi := (ContinuousLinearMap.nonneg_iff_isPositive.mp hp).re_inner_nonneg_right x
    rw [map_sub, sub_apply, inner_sub_right] at hi
    change 0 ≤ (inner ℂ x (((cfcHom hR) g.toContinuousMap) x) -
      inner ℂ x (((cfcHom hR) f.toContinuousMap) x)).re at hi
    rw [Complex.sub_re] at hi
    exact sub_nonneg.mp hi

def resolventVectorMeasure (R : H →L[ℂ] H) (hR : IsSelfAdjoint R) (x : H) :
    Measure (spectrum ℝ R) := RealRMK.rieszMeasure (resolventVectorFunctional R hR x)

instance resolventVectorMeasure_finite (R : H →L[ℂ] H) (hR : IsSelfAdjoint R) (x : H) :
    IsFiniteMeasure (resolventVectorMeasure R hR x) := by
  unfold resolventVectorMeasure
  infer_instance

theorem resolventVectorMeasure_integral (R : H →L[ℂ] H) (hR : IsSelfAdjoint R)
    (x : H) (f : C(spectrum ℝ R, ℝ)) :
    (∫ s, f s ∂resolventVectorMeasure R hR x) =
      (inner ℂ x ((cfcHom hR f) x)).re := by
  exact RealRMK.integral_rieszMeasure (resolventVectorFunctional R hR x)
    (CompactlySupportedContinuousMap.continuousMapEquiv f)

theorem resolventVectorMeasure_mass (R : H →L[ℂ] H) (hR : IsSelfAdjoint R) (x : H) :
    (resolventVectorMeasure R hR x).real Set.univ = ‖x‖ ^ 2 := by
  have hi := resolventVectorMeasure_integral R hR x (1 : C(spectrum ℝ R, ℝ))
  simp only [ContinuousMap.one_apply, integral_const, smul_eq_mul, mul_one,
    map_one, one_apply_eq_self] at hi
  change (resolventVectorMeasure R hR x).real Set.univ = RCLike.re (inner ℂ x x) at hi
  simpa only [inner_self_eq_norm_sq] using hi

end

end KadisonKastler

end OAI
