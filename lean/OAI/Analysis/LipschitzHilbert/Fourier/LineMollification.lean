import OAI.Analysis.LipschitzHilbert.Geometry.CompactDirectionCutoff
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic

namespace OAI

/-! Positive compact mollification on the line preserves the size and
Lipschitz bounds needed for the sampling maps. -/
noncomputable section
open MeasureTheory Function
open scoped Convolution ContDiff
namespace LipschitzHilbert.PacketRepresentation

def lineMollification (phi : ContDiffBump (0 : ℝ)) (f : ℝ → ℝ)
    (hf : Integrable f) (hcompact : HasCompactSupport f) : SchwartzMap ℝ ℝ :=
  ((phi.hasCompactSupport_normed (μ:=volume)).convolution
    (L:=ContinuousLinearMap.lsmul ℝ ℝ) hcompact).toSchwartzMap
      ((phi.hasCompactSupport_normed (μ:=volume)).contDiff_convolution_left
        (ContinuousLinearMap.lsmul ℝ ℝ) phi.contDiff_normed hf.locallyIntegrable)

theorem lineMollification_apply (phi : ContDiffBump (0 : ℝ)) (f : ℝ → ℝ)
    (hf : Integrable f) (hcompact : HasCompactSupport f) (x : ℝ) :
    lineMollification phi f hf hcompact x=∫ z, phi.normed volume z*f (x-z) := rfl

theorem lineMollification_compact (phi : ContDiffBump (0 : ℝ)) (f : ℝ → ℝ)
    (hf : Integrable f) (hcompact : HasCompactSupport f) :
    HasCompactSupport (lineMollification phi f hf hcompact : ℝ → ℝ) :=
  (phi.hasCompactSupport_normed (μ:=volume)).convolution
    (L:=ContinuousLinearMap.lsmul ℝ ℝ) hcompact

theorem lineMollification_bound (phi : ContDiffBump (0 : ℝ)) (f : ℝ → ℝ)
    (hf : Integrable f) (hcompact : HasCompactSupport f) (hb : ∀ x, |f x|≤1) (x : ℝ) :
    |lineMollification phi f hf hcompact x|≤1 := by
  rw [lineMollification_apply,←Real.norm_eq_abs]
  have hh := norm_integral_le_of_norm_le (phi.integrable_normed (μ:=volume))
    (Filter.Eventually.of_forall fun z => show ‖phi.normed volume z*f (x-z)‖≤phi.normed volume z from by
      rw [norm_mul,Real.norm_eq_abs,abs_of_nonneg (phi.nonneg_normed z),Real.norm_eq_abs]
      exact mul_le_of_le_one_right (phi.nonneg_normed z) (hb _))
  simpa only [phi.integral_normed] using hh

theorem lineMollification_lipschitz (phi : ContDiffBump (0 : ℝ)) (f : ℝ → ℝ)
    (hf : Integrable f) (hcompact : HasCompactSupport f) (hu : LipschitzWith 1 f) :
    LipschitzWith 1 (lineMollification phi f hf hcompact) := by
  have hi (x : ℝ) : Integrable (fun z => phi.normed volume z*f (x-z)) :=
    (phi.continuous_normed.mul (hu.continuous.comp (continuous_const.sub continuous_id))).integrable_of_hasCompactSupport
      ((phi.hasCompactSupport_normed (μ:=volume)).mul_right)
  apply LipschitzWith.of_dist_le_mul
  intro x y
  change |lineMollification phi f hf hcompact x-lineMollification phi f hf hcompact y|≤1*|x-y|
  rw [lineMollification_apply,lineMollification_apply,←integral_sub (hi x) (hi y),←Real.norm_eq_abs]
  have hh := norm_integral_le_of_norm_le ((phi.integrable_normed (μ:=volume)).mul_const |x-y|)
    (Filter.Eventually.of_forall fun z => show
      ‖phi.normed volume z*f (x-z)-phi.normed volume z*f (y-z)‖≤phi.normed volume z*|x-y| from by
      rw [←mul_sub,norm_mul,Real.norm_eq_abs,abs_of_nonneg (phi.nonneg_normed z),Real.norm_eq_abs]
      apply mul_le_mul_of_nonneg_left _ (phi.nonneg_normed z)
      simpa only [Real.dist_eq,NNReal.coe_one,one_mul,sub_sub_sub_cancel_right] using hu.dist_le_mul (x-z) (y-z))
  simpa only [integral_mul_const,phi.integral_normed] using hh

theorem lineMollification_approximation (phi : ContDiffBump (0 : ℝ)) (f : ℝ → ℝ)
    (hf : Integrable f) (hcompact : HasCompactSupport f) (hu : LipschitzWith 1 f) (x : ℝ) :
    |lineMollification phi f hf hcompact x-f x|≤phi.rOut := by
  apply phi.dist_normed_convolution_le hu.continuous.aestronglyMeasurable
  intro y hy
  have hh : dist (f y) (f x)≤dist y x := by
    simpa only [NNReal.coe_one,one_mul] using hu.dist_le_mul y x
  exact hh.trans hy.le

end LipschitzHilbert.PacketRepresentation

end

end OAI
