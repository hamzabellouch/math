import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.AffineMap
import Mathlib.Tactic

namespace OAI

noncomputable section
open Set

namespace LeanBlast.KLS

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem convexOn_of_second_fderiv_nonneg {f : E → ℝ} {s : Set E}
    (hf : ContDiff ℝ 2 f) (hs : Convex ℝ s)
    (hH : ∀ x ∈ s, ∀ v : E, 0 ≤ fderiv ℝ (fderiv ℝ f) x v v) :
    ConvexOn ℝ s f := by
  refine ⟨hs, ?_⟩
  intro x hx y hy a b ha hb hab
  let γ : ℝ → E := AffineMap.lineMap x y
  let F : ℝ → ℝ := fun t => f (γ t)
  let F' : ℝ → ℝ := fun t => fderiv ℝ f (γ t) (y - x)
  let F'' : ℝ → ℝ := fun t => fderiv ℝ (fderiv ℝ f) (γ t) (y - x) (y - x)
  have hγ (t : ℝ) : HasDerivAt γ (y - x) t := AffineMap.hasDerivAt_lineMap
  have hF (t : ℝ) : HasDerivAt F (F' t) t :=
    (hf.differentiable (by norm_num) (γ t)).hasFDerivAt.comp_hasDerivAt t (hγ t)
  have hD : Differentiable ℝ (fderiv ℝ f) :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hF' (t : ℝ) : HasDerivAt F' (F'' t) t := by
    have h := ((hD (γ t)).hasFDerivAt.clm_apply
      (hasFDerivAt_const (y - x) (γ t))).comp_hasDerivAt t (hγ t)
    simpa only [F', F'', Function.comp_def, add_apply,
      ContinuousLinearMap.comp_apply, zero_apply,
      ContinuousLinearMap.flip_apply, map_zero, zero_add] using h
  have hc : ConvexOn ℝ (Icc (0 : ℝ) 1) F :=
    convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc _ _)
      (fun t _ => (hF t).continuousAt.continuousWithinAt)
      (fun t _ => (hF t).hasDerivWithinAt)
      (fun t _ => (hF' t).hasDerivWithinAt)
      (fun t ht => hH (γ t) (hs.lineMap_mem hx hy (interior_subset ht)) (y - x))
  have h := hc.2 (show (0 : ℝ) ∈ Icc (0 : ℝ) 1 by constructor <;> norm_num)
    (show (1 : ℝ) ∈ Icc (0 : ℝ) 1 by constructor <;> norm_num) ha hb hab
  have hab' : 1 - b = a := by linarith
  simpa [F, γ, AffineMap.lineMap_apply_module, smul_eq_mul, hab'] using h

end LeanBlast.KLS

end

end OAI
