import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Flow.FlowMixedPartials

namespace OAI

/-! The first and second variational equations follow by differentiating
the actual ODE after joint smoothness has been proved. -/

noncomputable section
namespace ForcedComputation.Flow
open scoped ContDiff

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem first_variation {V Ω : ℝ → E → E}
    (hΩ : ContDiff ℝ ∞ (Function.uncurry Ω))
    (hV : ∀ t, ContDiff ℝ ∞ (V t))
    (hode : ∀ t x, HasDerivAt (fun s => Ω s x) (V t (Ω t x)) t)
    (t : ℝ) (x v : E) :
    HasDerivAt (fun s => fderiv ℝ (Ω s) x v)
      (fderiv ℝ (V t) (Ω t x) (fderiv ℝ (Ω t) x v)) t := by
  have h := time_space_commute hΩ t x v
  have he : (fun y => deriv (fun s => Ω s y) t) = fun y => V t (Ω t y) :=
    funext fun y => (hode t y).deriv
  change HasDerivAt (fun s => fderiv ℝ (Ω s) x v)
    (fderiv ℝ (fun y => deriv (fun s => Ω s y) t) x v) t at h
  rw [he] at h
  have hx : ContDiff ℝ ∞ (Ω t) :=
    hΩ.comp (contDiff_const.prodMk contDiff_id)
  have hd := (hV t).differentiable (by simp) (Ω t x)
  have hg := hx.differentiable (by simp) x
  have hchain : fderiv ℝ (fun y => V t (Ω t y)) x =
      (fderiv ℝ (V t) (Ω t x)).comp (fderiv ℝ (Ω t) x) :=
    (hd.hasFDerivAt.comp x hg.hasFDerivAt).fderiv
  rw [hchain] at h
  exact h

theorem second_variation {V Ω : ℝ → E → E}
    (hΩ : ContDiff ℝ ∞ (Function.uncurry Ω))
    (hV : ∀ t, ContDiff ℝ ∞ (V t))
    (hode : ∀ t x, HasDerivAt (fun s => Ω s x) (V t (Ω t x)) t)
    (t : ℝ) (x v w : E) :
    HasDerivAt (fun s => fderiv ℝ (fderiv ℝ (Ω s)) x v w)
      (fderiv ℝ (V t) (Ω t x) (fderiv ℝ (fderiv ℝ (Ω t)) x v w) +
        fderiv ℝ (fderiv ℝ (V t)) (Ω t x)
          (fderiv ℝ (Ω t) x v) (fderiv ℝ (Ω t) x w)) t := by
  let G : ℝ × E → E := fun p => fderiv ℝ (Ω p.1) p.2 w
  have hG : ContDiff ℝ ∞ G := spaceDerivative_smooth hΩ w
  have h := time_space_commute hG t x v
  have he : (fun y => deriv (fun s => G (s, y)) t) =
      fun y => fderiv ℝ (V t) (Ω t y) (fderiv ℝ (Ω t) y w) := by
    funext y
    exact (first_variation hΩ hV hode t y w).deriv
  rw [he] at h
  have hx : ContDiff ℝ ∞ (Ω t) :=
    hΩ.comp (contDiff_const.prodMk contDiff_id)
  have hDx : ContDiff ℝ ∞ (fderiv ℝ (Ω t)) := hx.fderiv_right (by simp)
  have hDV : ContDiff ℝ ∞ (fderiv ℝ (V t)) := (hV t).fderiv_right (by simp)
  have ha := (hDV.differentiable (by simp) (Ω t x)).hasFDerivAt.comp x
    ((hx.differentiable (by simp) x).hasFDerivAt)
  have hb := ((hDx.differentiable (by simp) x).hasFDerivAt).clm_apply
    (hasFDerivAt_const w x)
  have hab := congrArg (fun A : E →L[ℝ] E => A v) (ha.clm_apply hb).fderiv
  simp only [add_apply, ContinuousLinearMap.comp_apply,
    zero_apply, map_zero, zero_add, ContinuousLinearMap.flip_apply, Function.comp_def] at hab
  rw [hab] at h
  have hleft (s : ℝ) :
      fderiv ℝ (fun y => G (s, y)) x v = fderiv ℝ (fderiv ℝ (Ω s)) x v w := by
    have hs : ContDiff ℝ ∞ (Ω s) := hΩ.comp (contDiff_const.prodMk contDiff_id)
    have hds : DifferentiableAt ℝ (fderiv ℝ (Ω s)) x :=
      (hs.fderiv_right (m := ∞) (by simp)).differentiable (by simp) x
    have hh := congrArg (fun A : E →L[ℝ] E => A v)
      (hds.hasFDerivAt.clm_apply (hasFDerivAt_const w x)).fderiv
    simpa only [G, add_apply, ContinuousLinearMap.comp_apply,
      zero_apply, map_zero, zero_add, ContinuousLinearMap.flip_apply, Function.comp_def] using hh
  simpa only [hleft] using h

end ForcedComputation.Flow

end

end OAI
