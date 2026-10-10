import OAI.Geometry.SurfaceImmersion.Geometry.NonzeroGermDiffeomorphism
import Mathlib.Analysis.Calculus.Deriv.Slope

namespace OAI

/-! The explicit corner parameters run forward along the original path
at each joining endpoint. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing

lemma smooth_homeomorph_inverse_deriv_ne (e : ℝ ≃ₜ ℝ)
    (he : ContDiff ℝ ∞ e) (hei : ContDiff ℝ ∞ e.symm) (x : ℝ) :
    deriv e.symm x ≠ 0 := by
  have hd := ((he.differentiable (by simp) (e.symm x)).hasDerivAt).comp x
    ((hei.differentiable (by simp) x).hasDerivAt)
  have hd' : HasDerivAt (fun x : ℝ => x)
      (deriv e (e.symm x)*deriv e.symm x) x := by simpa only [Function.comp_def,e.apply_symm_apply] using hd
  have hh := hd'.unique (hasDerivAt_id x)
  intro hz
  rw [hz,mul_zero] at hh
  norm_num at hh

lemma smooth_homeomorph_inverse_deriv_pos (e : ℝ ≃ₜ ℝ)
    (he : ContDiff ℝ ∞ e) (hei : ContDiff ℝ ∞ e.symm)
    (hm : StrictMono e) (x : ℝ) : 0 < deriv e.symm x := by
  have hmi : StrictMono e.symm := by
    intro x y hxy
    apply hm.lt_iff_lt.mp
    simpa only [e.apply_symm_apply] using hxy
  exact lt_of_le_of_ne hmi.monotone.deriv_nonneg
    (smooth_homeomorph_inverse_deriv_ne e he hei x).symm

lemma smooth_homeomorph_inverse_deriv_neg (e : ℝ ≃ₜ ℝ)
    (he : ContDiff ℝ ∞ e) (hei : ContDiff ℝ ∞ e.symm)
    (hm : StrictAnti e) (x : ℝ) : deriv e.symm x < 0 := by
  have hmi : StrictAnti e.symm := by
    intro x y hxy
    apply lt_of_not_ge
    intro hyx
    have h := hm.antitone hyx
    simp only [e.apply_symm_apply] at h
    exact (not_le_of_gt hxy) h
  exact lt_of_le_of_ne hmi.antitone.deriv_nonpos
    (smooth_homeomorph_inverse_deriv_ne e he hei x)

lemma returning_left_parameter_deriv_pos (e : ℝ ≃ₜ ℝ)
    (he : ContDiff ℝ ∞ e) (hei : ContDiff ℝ ∞ e.symm) (hm : StrictAnti e)
    (a : ℝ) {b : ℝ} (hb : 0 < b) :
    0 < deriv (fun s : ℝ => e.symm (a+b*s^2)) (-2) := by
  have hx : HasDerivAt (fun s : ℝ => a+b*s^2) (2*b*(-2)) (-2) := by
    convert (((hasDerivAt_id (-2:ℝ)).pow 2).const_mul b).const_add a using 1
    · rfl
    · dsimp only [id_eq]; ring
  have hd := ((hei.differentiable (by simp) (a+b*(-2:ℝ)^2)).hasDerivAt).comp (-2) hx
  have hdv := hd.deriv
  dsimp only [Function.comp_def] at hdv
  rw [hdv]
  exact mul_pos_of_neg_of_neg (smooth_homeomorph_inverse_deriv_neg e he hei hm _) (by linarith)

lemma returning_right_parameter_deriv_pos (e : ℝ ≃ₜ ℝ)
    (he : ContDiff ℝ ∞ e) (hei : ContDiff ℝ ∞ e.symm) (hm : StrictMono e)
    (a : ℝ) {b : ℝ} (hb : 0 < b) :
    0 < deriv (fun s : ℝ => e.symm (a+b*s^2)) 2 := by
  have hx : HasDerivAt (fun s : ℝ => a+b*s^2) (2*b*2) 2 := by
    convert (((hasDerivAt_id (2:ℝ)).pow 2).const_mul b).const_add a using 1
    · rfl
    · dsimp only [id_eq]; ring
  have hd := ((hei.differentiable (by simp) (a+b*(2:ℝ)^2)).hasDerivAt).comp 2 hx
  have hdv := hd.deriv
  dsimp only [Function.comp_def] at hdv
  rw [hdv]
  exact mul_pos (smooth_homeomorph_inverse_deriv_pos e he hei hm _) (by linarith)

lemma advancing_parameter_deriv_pos (e : ℝ ≃ₜ ℝ)
    (he : ContDiff ℝ ∞ e) (hei : ContDiff ℝ ∞ e.symm) (hm : StrictMono e)
    (a : ℝ) {b : ℝ} (hb : 0 < b) (t : ℝ) :
    0 < deriv (fun s : ℝ => e.symm (a+b*s)) t := by
  have hx : HasDerivAt (fun s : ℝ => a+b*s) b t := by
    simpa only [id_eq,mul_one] using ((hasDerivAt_id t).const_mul b).const_add a
  have hd := ((hei.differentiable (by simp) (a+b*t)).hasDerivAt).comp t hx
  have hdv := hd.deriv
  dsimp only [Function.comp_def] at hdv
  rw [hdv]
  exact mul_pos (smooth_homeomorph_inverse_deriv_pos e he hei hm _) hb

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
