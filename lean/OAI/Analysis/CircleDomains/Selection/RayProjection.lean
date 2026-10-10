import OAI.Analysis.CircleDomains.Selection.TranslatedSideNesting

namespace OAI

/-! The logarithmic half-plane projection sends every integer translate
back to the original terminal arc. -/

open Set Function
open scoped Topology

noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

def diskRayProjection (z : ℂ) : ℂ :=
  (Real.exp (-z.im) : ℂ) * standardCirclePoint (z.re : UnitAddCircle)

theorem continuous_diskRayProjection : Continuous diskRayProjection := by
  apply Continuous.mul
  · exact Complex.continuous_ofReal.comp (Real.continuous_exp.comp Complex.continuous_im.neg)
  · exact continuous_subtype_val.comp
      ((AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).continuous.comp
        ((AddCircle.continuous_mk' (1 : ℝ)).comp Complex.continuous_re))

theorem diskRayProjection_norm (z : ℂ) : ‖diskRayProjection z‖ = Real.exp (-z.im) := by
  rw [diskRayProjection, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  have hn : ‖standardCirclePoint (z.re : UnitAddCircle)‖ = 1 := Circle.norm_coe _
  rw [hn, mul_one]

theorem diskRayProjection_argument (z : ℂ) :
    normalizedArgument (diskRayProjection z) = (z.re : UnitAddCircle) := by
  rw [diskRayProjection, normalizedArgument,
    Complex.arg_real_mul _ (Real.exp_pos _)]
  exact normalizedArgument_standardCirclePoint _

theorem diskRayProjection_translated (γ : C(PathTime, ℂ))
    (hγ : γ ∈ diskTerminalArcSet) (k : ℤ) (t : DiskRayTime) :
    diskRayProjection ((translatedHalfPlaneRay γ hγ k).curve t) = γ t.val := by
  apply Complex.ext_norm_arg
  · rw [diskRayProjection_norm]
    change Real.exp (-((diskRayComplex γ hγ.1 hγ.2.2.1 t + (k : ℂ)).im)) = _
    rw [Complex.add_im, Complex.intCast_im, add_zero, diskRayComplex_im,
      diskRayDepth, neg_neg, Real.exp_log (norm_pos_iff.mpr (diskRay_nonzero γ hγ.1 hγ.2.2.1 t))]
  · apply Complex.arg_coe_angle_eq_iff.mp
    apply (AddCircle.equivAddCircle (2 * Real.pi) 1 (by positivity) one_ne_zero).injective
    change normalizedArgument (diskRayProjection ((translatedHalfPlaneRay γ hγ k).curve t)) = _
    rw [diskRayProjection_argument]
    have hr : ((translatedHalfPlaneRay γ hγ k).curve t).re =
        diskRayAngle γ hγ.1 hγ.2.2.1 t + (k : ℝ) := by
      simp only [translatedHalfPlaneRay, ContinuousMap.coe_mk, Complex.add_re,
        Complex.intCast_re, diskRayComplex, Complex.ofReal_re, Complex.mul_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
    rw [hr]
    have hk : ((k : ℝ) : UnitAddCircle) = 0 :=
      (addCircle_eq_iff_exists_int 1 (k : ℝ) 0).mpr ⟨k, by simp⟩
    rw [AddCircle.coe_add, hk, add_zero]
    exact diskRayAngle_projects γ hγ.1 hγ.2.2.1 t

end CircleDomainRigidity

end

end OAI
