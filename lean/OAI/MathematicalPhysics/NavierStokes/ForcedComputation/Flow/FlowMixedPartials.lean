import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod

namespace OAI

/-! Commutation of a time derivative and an initial-point derivative.
These lemmas turn joint smoothness of an actual flow into its variational
equations, without an additional smooth-dependence input. -/

noncomputable section
namespace ForcedComputation.Flow
open scoped ContDiff

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem spaceDerivative_eq {G : ℝ × E → F} (hG : ContDiff ℝ ∞ G)
    (t : ℝ) (x v : E) :
    fderiv ℝ (fun y => G (t, y)) x v = fderiv ℝ G (t, x) (0, v) := by
  have hd := ((hG.differentiable (by simp) (t, x)).hasFDerivAt.comp x
    (hasFDerivAt_prodMk_right t x)).fderiv
  exact congrArg (fun A : E →L[ℝ] F => A v) hd

theorem timeDerivative_eq {G : ℝ × E → F} (hG : ContDiff ℝ ∞ G)
    (t : ℝ) (x : E) :
    deriv (fun s => G (s, x)) t = fderiv ℝ G (t, x) (1, 0) := by
  exact ((hG.differentiable (by simp) (t, x)).hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_id t).prodMk (hasDerivAt_const t x))).deriv

theorem spaceDerivative_smooth {G : ℝ × E → F} (hG : ContDiff ℝ ∞ G) (v : E) :
    ContDiff ℝ ∞ (fun p : ℝ × E => fderiv ℝ (fun y => G (p.1, y)) p.2 v) := by
  have he : (fun p : ℝ × E => fderiv ℝ (fun y => G (p.1, y)) p.2 v) =
      fun p => fderiv ℝ G p (0, v) := by
    funext p
    exact spaceDerivative_eq hG p.1 p.2 v
  rw [he]
  exact (hG.fderiv_right (by simp)).clm_apply contDiff_const

theorem time_space_commute {G : ℝ × E → F} (hG : ContDiff ℝ ∞ G)
    (t : ℝ) (x v : E) :
    HasDerivAt (fun s => fderiv ℝ (fun y => G (s, y)) x v)
      (fderiv ℝ (fun y => deriv (fun s => G (s, y)) t) x v) t := by
  have hD : ContDiff ℝ ∞ (fderiv ℝ G) := hG.fderiv_right (by simp)
  have ht := (hD.differentiable (by simp) (t, x)).hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_id t).prodMk (hasDerivAt_const t x))
  have htv := ht.clm_apply (hasDerivAt_const t (0, v))
  simp only [map_zero, add_zero, Function.comp_def, id_eq] at htv
  have he : (fun s => fderiv ℝ (fun y => G (s, y)) x v) =
      fun s => fderiv ℝ G (s, x) (0, v) := by
    funext s
    exact spaceDerivative_eq hG s x v
  rw [he]
  have htime : (fun y => deriv (fun s => G (s, y)) t) =
      fun y => fderiv ℝ G (t, y) (1, 0) := by
    funext y
    exact timeDerivative_eq hG t y
  rw [htime]
  have hx := (hD.differentiable (by simp) (t, x)).hasFDerivAt.comp x
    (hasFDerivAt_prodMk_right t x)
  have hxv := congrArg (fun A : E →L[ℝ] F => A v)
    (hx.clm_apply (hasFDerivAt_const (1, 0) x)).fderiv
  simp only [add_apply, ContinuousLinearMap.comp_apply,
    zero_apply, map_zero, zero_add, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.inr_apply, Function.comp_def] at hxv
  rw [hxv]
  have hs := (hG.contDiffAt (x := (t, x))).isSymmSndFDerivAt (by simp) (1, 0) (0, v)
  rw [← hs]
  exact htv

end ForcedComputation.Flow

end

end OAI
