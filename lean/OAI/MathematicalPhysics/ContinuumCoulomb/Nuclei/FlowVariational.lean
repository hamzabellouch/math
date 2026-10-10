import OAI.MathematicalPhysics.ContinuumCoulomb.Nuclei.FlowMixedDerivative

namespace OAI

/-! The first variational equation for a C⁴ local model of the transport
flow, including the endpoints of the closed time interval. -/

noncomputable section
open Set Filter ContinuousLinearMap
open scoped Topology ContDiff
namespace ContinuumCoulomb

theorem flow_model_time_partial (H : ℝ × Position → Position)
    (hH : ContDiff ℝ 4 H) (v : ℝ → Position → Position)
    (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) (x : Position)
    (hODE : HasDerivWithinAt (fun s => H (s,x)) (v t (H (t,x))) (Icc (0:ℝ) 1) t) :
    fderiv ℝ H (t,x) (1,0) = v t (H (t,x)) := by
  have hp : HasDerivAt (fun s : ℝ => (s,x)) ((1:ℝ),(0:Position)) t :=
    (hasDerivAt_id t).prodMk (hasDerivAt_const t x)
  have hd := ((hH.differentiable (by norm_num)) (t,x)).hasFDerivAt.comp_hasDerivAt t hp
  have hd' : HasDerivWithinAt (fun s => H (s,x)) (fderiv ℝ H (t,x) (1,0))
      (Icc (0:ℝ) 1) t := by
    apply hd.hasDerivWithinAt.congr_of_eventuallyEq
    exact Filter.Eventually.of_forall (fun _ => rfl)
    rfl
  have hu := (uniqueDiffOn_Icc (by norm_num : (0:ℝ)<1)).uniqueDiffWithinAt ht
  exact (hd'.derivWithin hu).symm.trans (hODE.derivWithin hu)

theorem flow_model_variational (H : ℝ × Position → Position)
    (hH : ContDiff ℝ 4 H) (v : ℝ → Position → Position) (O : Set Position)
    (hO : IsOpen O) (x : Position) (hx : x ∈ O)
    (hODE : ∀ y ∈ O, ∀ t ∈ Icc (0:ℝ) 1,
      HasDerivWithinAt (fun s => H (s,y)) (v t (H (t,y))) (Icc (0:ℝ) 1) t)
    (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1)
    (hv : DifferentiableAt ℝ (v t) (H (t,x))) (e : Position) :
    HasDerivWithinAt (fun s => fderiv ℝ (fun y => H (s,y)) x e)
      (fderiv ℝ (v t) (H (t,x)) (fderiv ℝ (fun y => H (t,y)) x e))
      (Icc (0:ℝ) 1) t := by
  have heq : (fun y => fderiv ℝ H (t,y) (1,0)) =ᶠ[𝓝 x]
      (fun y => v t (H (t,y))) := by
    filter_upwards [hO.mem_nhds hx] with y hy
    exact flow_model_time_partial H hH v t ht y (hODE y hy t ht)
  have hs : DifferentiableAt ℝ (fun y => H (t,y)) x :=
    (hH.comp (contDiff_const.prodMk contDiff_id)).differentiable (by norm_num) x
  have hc := hv.hasFDerivAt.comp x hs.hasFDerivAt
  have hdf : fderiv ℝ (fun y => fderiv ℝ H (t,y) (1,0)) x e =
      fderiv ℝ (v t) (H (t,x)) (fderiv ℝ (fun y => H (t,y)) x e) := by
    rw [heq.fderiv_eq]
    change fderiv ℝ (v t ∘ (fun y => H (t,y))) x e = _
    rw [hc.fderiv]
    rfl
  rw [←hdf]
  exact (flow_mixed_spatial_derivative H hH t x e).hasDerivWithinAt

end ContinuumCoulomb

end

end OAI
