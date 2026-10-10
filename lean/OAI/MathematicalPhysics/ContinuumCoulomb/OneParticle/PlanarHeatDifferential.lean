import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.PlanarHeatLimit
import Mathlib.Analysis.Calculus.ParametricIntegral

namespace OAI

/-! Pointwise differential identities for the actual two-dimensional Gaussian
kernel. Its time derivative is its coordinate Laplacian. -/

noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace BigOperators
namespace ContinuumCoulomb

theorem planarHeatKernel_C2 (t : ℝ) : ContDiff ℝ 2 (planarHeatKernel t) := by
  unfold planarHeatKernel
  exact contDiff_const.mul (((contDiff_norm_sq ℝ).neg.div_const (4 * t)).exp)

def planarHeatTimeDerivative (t : ℝ) (r : PlanarPosition) : ℝ :=
  (‖r‖ ^ 2 / (4 * t ^ 2) - 1 / t) * planarHeatKernel t r

theorem planarHeatKernel_hasDerivAt {t : ℝ} (ht : 0 < t) (r : PlanarPosition) :
    HasDerivAt (fun s => planarHeatKernel s r) (planarHeatTimeDerivative t r) t := by
  have hi := hasDerivAt_inv ht.ne'
  have h := (hi.const_mul ((4 * Real.pi)⁻¹)).mul
    ((hi.const_mul (-‖r‖ ^ 2 / 4)).exp)
  convert h using 1
  · funext s
    change planarHeatKernel s r = (4 * Real.pi)⁻¹ * s⁻¹ * Real.exp (-‖r‖ ^ 2 / 4 * s⁻¹)
    unfold planarHeatKernel
    congr 1 <;> ring_nf
  · dsimp [planarHeatTimeDerivative, planarHeatKernel]
    have he : -‖r‖ ^ 2 / (4 * t) = -‖r‖ ^ 2 / 4 * t⁻¹ := by ring
    rw [he]
    field_simp
    ring

theorem planarHeatKernel_partial (t : ℝ) (e r : PlanarPosition) :
    planarPartial (planarHeatKernel t) e r =
      (-inner ℝ e r / (2 * t)) * planarHeatKernel t r := by
  have hd := ((((hasStrictFDerivAt_norm_sq r).hasFDerivAt.neg).mul_const (4 * t)⁻¹).exp).const_mul
    ((4 * Real.pi * t)⁻¹)
  change fderiv ℝ (planarHeatKernel t) r e = _
  rw [show fderiv ℝ (planarHeatKernel t) r = _ from hd.fderiv]
  simp only [smul_apply, smul_eq_mul, neg_apply, Pi.neg_apply,
    innerSL_apply_apply, planarHeatKernel]
  rw [real_inner_comm r e]
  ring_nf

theorem planarHeatKernel_partial_partial (t : ℝ) (e r : PlanarPosition) :
    planarPartial (planarPartial (planarHeatKernel t) e) e r =
      ((inner ℝ e r) ^ 2 / (4 * t ^ 2) - ‖e‖ ^ 2 / (2 * t)) * planarHeatKernel t r := by
  have hlin : ContDiff ℝ 1 (fun s : PlanarPosition => -inner ℝ e s / (2 * t)) :=
    ((innerSL ℝ e).contDiff.neg).div_const _
  have heq : planarPartial (planarHeatKernel t) e =
      fun s => (-inner ℝ e s / (2 * t)) * planarHeatKernel t s :=
    funext (planarHeatKernel_partial t e)
  rw [heq, planarPartial_mul _ _ hlin ((planarHeatKernel_C2 t).of_le (by norm_num)),
    planarHeatKernel_partial]
  have hpart : planarPartial (fun s : PlanarPosition => -inner ℝ e s / (2 * t)) e r =
      -‖e‖ ^ 2 / (2 * t) := by
    have hd := ((innerSL ℝ e).hasFDerivAt (x := r)).neg.mul_const (2 * t)⁻¹
    have hd' : HasFDerivAt (fun s : PlanarPosition => -inner ℝ e s / (2 * t))
        ((2 * t)⁻¹ • -(innerSL ℝ e)) r := by
      simpa only [Pi.neg_apply, innerSL_apply_apply, div_eq_mul_inv] using hd
    change fderiv ℝ (fun s : PlanarPosition => -inner ℝ e s / (2 * t)) r e = _
    rw [hd'.fderiv]
    simp only [smul_apply, smul_eq_mul, neg_apply,
      innerSL_apply_apply, real_inner_self_eq_norm_sq]
    ring
  rw [hpart]
  ring

theorem planarHeatKernel_laplacian (t : ℝ) (r : PlanarPosition) :
    planarLaplacian (planarHeatKernel t) r = planarHeatTimeDerivative t r := by
  have hn : ‖r‖ ^ 2 = ∑ a : Fin 2, (r a) ^ 2 := by
    simpa only [Real.norm_eq_abs, sq_abs] using EuclideanSpace.norm_sq_eq r
  have ha (a : Fin 2) : inner ℝ (planarAxis a) r = r a := by
    simp [planarAxis, EuclideanSpace.inner_single_left]
  have he (a : Fin 2) : ‖planarAxis a‖ ^ 2 = 1 := by simp [planarAxis]
  simp only [planarLaplacian, planarHeatKernel_partial_partial, ha, he,
    planarHeatTimeDerivative, hn, Fin.sum_univ_two]
  ring

end ContinuumCoulomb

end

end OAI
