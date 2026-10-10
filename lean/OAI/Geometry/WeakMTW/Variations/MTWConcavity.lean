import Mathlib
import OAI.Geometry.WeakMTW.Coordinates.InteriorCost

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold

namespace ParameterCalculus
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
 theorem slice_deriv_smooth {f : E → ℝ → ℝ} {x : E} {t : ℝ}
    (hf : ContDiffAt ℝ ∞ (Function.uncurry f) (x,t)) :
    ContDiffAt ℝ ∞ (fun q : E × ℝ => deriv (f q.1) q.2) (x,t) := by
  have hh : ContDiffAt ℝ ∞ (fun z : (E × ℝ) × ℝ => f z.1.1 z.2) ((x,t),t) :=
    hf.comp ((x,t),t) (contDiffAt_fst.fst.prodMk contDiffAt_snd)
  have hd : ContDiffAt ℝ ∞ (fun q : E × ℝ => fderiv ℝ (f q.1) q.2) (x,t) :=
    hh.fderiv contDiffAt_snd (by simp)
  simpa only [fderiv_apply_one_eq_deriv] using hd.clm_apply (contDiffAt_const (c := (1 : ℝ)))

 theorem slice_second_smooth {f : E → ℝ → ℝ} {x : E}
    (hf : ContDiffAt ℝ ∞ (Function.uncurry f) (x,0)) :
    ContDiffAt ℝ ∞ (fun p : E => deriv (fun t => deriv (f p) t) 0) x := by
  exact (slice_deriv_smooth (f := fun p t => deriv (f p) t)
    (slice_deriv_smooth hf)).comp x (contDiffAt_id.prodMk contDiffAt_const)
end
end ParameterCalculus

namespace WeakMTW
noncomputable section
variable {n : ℕ} {M : Type*} [MetricSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M] [CompactSpace M]

 def actionHessianDiag (x : M) (v ξ : TangentSpace (model n) x) : ℝ :=
  deriv (fun t : ℝ => deriv (fun t' : ℝ => cost (exp x (t'•ξ)) (exp x v)) t) 0

 theorem cost_exp_parameter_smooth (x : M) {v : TangentSpace (model n) x}
    (hv : v ∈ injectivityDomain x) (ξ : TangentSpace (model n) x) :
    ContDiffAt ℝ ∞ (fun q : TangentSpace (model n) x × ℝ =>
      cost (exp x (q.2•ξ)) (exp x q.1)) (v,0) := by
  have h₁ : ContMDiff 𝓘(ℝ, TangentSpace (model n) x × ℝ) (model n) ∞
      (fun q : TangentSpace (model n) x × ℝ => exp x (q.2•ξ)) :=
    (exp_fibre_smooth x).comp (contMDiff_iff_contDiff.mpr (contDiff_snd.smul contDiff_const))
  have h₂ : ContMDiff 𝓘(ℝ, TangentSpace (model n) x × ℝ) (model n) ∞
      (fun q : TangentSpace (model n) x × ℝ => exp x q.1) :=
    (exp_fibre_smooth x).comp (contMDiff_iff_contDiff.mpr contDiff_fst)
  have hc : ContMDiffAt ((model n).prod (model n)) 𝓘(ℝ,ℝ) ∞
      (fun q : M × M => cost q.1 q.2) (exp x ((0 : ℝ)•ξ),exp x v) := by
    simpa only [zero_smul,exp_zero] using cost_smooth_at_injectivity x hv
  exact contMDiffAt_iff_contDiffAt.mp (hc.comp (v,0) ((h₁.prodMk h₂).contMDiffAt))

 theorem actionHessianDiag_smooth (x : M) {v : TangentSpace (model n) x}
    (hv : v ∈ injectivityDomain x) (ξ : TangentSpace (model n) x) :
    ContDiffAt ℝ ∞ (fun u => actionHessianDiag x u ξ) v :=
  ParameterCalculus.slice_second_smooth (cost_exp_parameter_smooth x hv ξ)

omit [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M] [CompactSpace M] [IsManifold (model n) ∞ M] in
 theorem mtw_eq_hessian_diag (x : M) (v ξ η : TangentSpace (model n) x) :
    mtw x v ξ η = -(3/2 : ℝ) *
      deriv (fun s : ℝ => deriv (fun r : ℝ => actionHessianDiag x (v+r•η) ξ) s) 0 := rfl

omit [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M] [CompactSpace M] [IsManifold (model n) ∞ M] in
 theorem mtw_on_line_eq (x : M) (v ξ η : TangentSpace (model n) x) (s : ℝ) :
    mtw x (v+s•η) ξ η = -(3/2 : ℝ) *
      deriv (deriv (fun r : ℝ => actionHessianDiag x (v+r•η) ξ)) s := by
  let F : ℝ → ℝ := fun r => actionHessianDiag x (v+r•η) ξ
  have he : (fun r => actionHessianDiag x (v+s•η+r•η) ξ) = fun r => F (r+s) := by
    funext r
    dsimp only [F]
    congr 1
    rw [add_smul]
    abel
  rw [mtw_eq_hessian_diag,he]
  simp only [deriv_comp_add_const,zero_add]
  rfl

 theorem transverse_action_concave (hMTW : HasWeakMTW (n := n) (M := M))
    (x : M) (v ξ η : TangentSpace (model n) x) (hξη : inner ℝ ξ η = 0)
    {D : Set ℝ} (hD : Convex ℝ D)
    (hI : ∀ s ∈ D, v+s•η ∈ injectivityDomain x) :
    ConcaveOn ℝ D (fun s => actionHessianDiag x (v+s•η) ξ) := by
  let F : ℝ → ℝ := fun s => actionHessianDiag x (v+s•η) ξ
  have hF (s : ℝ) (hs : s ∈ D) : ContDiffAt ℝ ∞ F s :=
    (actionHessianDiag_smooth x (hI s hs) ξ).comp s (contDiffAt_const.add (contDiffAt_id.smul contDiffAt_const))
  refine concaveOn_of_deriv2_nonpos hD (fun s hs => (hF s hs).continuousAt.continuousWithinAt)
    (fun s hs => ((hF s (interior_subset hs)).differentiableAt (by simp)).differentiableWithinAt)
    (fun s hs => ?_) (fun s hs => ?_)
  · have hh : ContDiffAt ℝ ∞ (deriv F) s := by
      have hd := (hF s (interior_subset hs)).fderiv_right (m := ∞) (by simp)
      simpa only [fderiv_apply_one_eq_deriv] using hd.clm_apply (contDiffAt_const (c := (1 : ℝ)))
    exact (hh.differentiableAt (by simp)).differentiableWithinAt
  · have hh := hMTW x (v+s•η) (hI s (interior_subset hs)) ξ η hξη
    rw [mtw_on_line_eq] at hh
    change deriv (deriv F) s ≤ 0
    change 0 ≤ -(3/2 : ℝ) * deriv (deriv F) s at hh
    linarith

end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
