import Mathlib
import OAI.Analysis.BiholderTransport.Coordinates.TwoSidedFiberLog
import OAI.Analysis.BiholderTransport.CostGeometry.BranchCost2

namespace OAI

section
section
noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
section EndpointLowerJet
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma exists_smooth_normal_endpoint_log_of_nonconjugate {z y : M}
    {q : TangentSpace 𝓘(ℝ,Model n) z} (hend : riemannianExp z q=y)
    (hq : Function.Injective (fderiv ℝ (fun v => extChartAt 𝓘(ℝ,Model n)
      (riemannianExp z q) (riemannianExp z v)) q)) :
    ∃ e : TangentSpace 𝓘(ℝ,Model n) y → TangentSpace 𝓘(ℝ,Model n) z,
      ContDiffAt ℝ ∞ e 0 ∧ e 0=q ∧
      (∀ᶠ w in 𝓝 0, riemannianExp z (e w)=riemannianExp y w) ∧
      Function.Injective (fderiv ℝ e 0) := by
  let V := TangentSpace 𝓘(ℝ,Model n) z
  let W := TangentSpace 𝓘(ℝ,Model n) y
  obtain ⟨log,hlog,hlogq,hlogi,_⟩ := exists_smooth_two_sided_fiber_log_of_nonconjugate hq
  rw [hend] at hlog hlogq hlogi
  let e : W → V := fun w => log (riemannianExp y w)
  have he : ContDiffAt ℝ ∞ e 0 :=
    ((show ContMDiffAt 𝓘(ℝ,Model n) 𝓘(ℝ,V) ∞ log (riemannianExp y 0) from
      by simpa only [riemannianExp_zero] using hlog).comp 0
      (contMDiff_riemannianExp_fiber y 0)).contDiffAt
  have he0 : e 0=q := by dsimp [e]; rw [riemannianExp_zero,hlogq]
  have hei : ∀ᶠ w in 𝓝 (0:W), riemannianExp z (e w)=riemannianExp y w :=
    (show ContinuousAt (riemannianExp y) (0:W) from (continuous_riemannianExp y).continuousAt).eventually
      (by simpa only [riemannianExp_zero] using hlogi)
  let χ := extChartAt 𝓘(ℝ,Model n) y
  let F : V → Model n := fun v => χ (riemannianExp z v)
  let G : W → Model n := fun w => χ (riemannianExp y w)
  have hF : ContDiffAt ℝ ∞ F q :=
    ((show ContMDiffAt 𝓘(ℝ,Model n) 𝓘(ℝ,Model n) ∞ χ (riemannianExp z q) from
      by rw [hend]; exact contMDiffAt_extChartAt).comp q
      (contMDiff_riemannianExp_fiber z q)).contDiffAt
  have hEq : (fun w => F (e w)) =ᶠ[𝓝 (0:W)] G := hei.mono (fun _ hw => congrArg χ hw)
  have hD := hEq.fderiv_eq (𝕜 := ℝ)
  rw [fderiv_fun_comp 0 (by simpa only [he0] using hF.differentiableAt (by simp))
    (he.differentiableAt (by simp)),he0] at hD
  have hG : Function.Injective (fderiv ℝ G 0) := by
    simpa only [G,χ,riemannianExp_zero] using
      riemannianExp_interior_nonconjugate (zero_mem_injectivityDomain (n := n) y)
  refine ⟨e,he,he0,hei,?_⟩
  have hcomp : Function.Injective ((fderiv ℝ F q).comp (fderiv ℝ e 0)) := by
    rw [hD]
    exact hG
  exact Function.Injective.of_comp (f := fderiv ℝ F q) (g := fderiv ℝ e 0) hcomp

omit [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma norm_reverseRay (z : TangentBundle 𝓘(ℝ,Model n) M) :
    ‖(reverseRay z).2‖=‖z.2‖ := by
  change ‖(-1:ℝ) • (sprayFlow 1 z).2‖=‖z.2‖
  rw [neg_one_smul,norm_neg,sprayFlow_speed]

lemma exists_reverse_branch_with_forward_action
    (z : TangentBundle 𝓘(ℝ,Model n) M)
    (hz : Function.Injective (fderiv ℝ (fun v => extChartAt 𝓘(ℝ,Model n)
      (riemannianExp z.1 z.2) (riemannianExp z.1 v)) z.2)) :
    ∃ G : M×M → ℝ,
      ContMDiffAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) 𝓘(ℝ,ℝ) ∞ G
        ((reverseRay z).1,riemannianExp (reverseRay z).1 (reverseRay z).2) ∧
      (∀ᶠ r in 𝓝 z,G (riemannianExp r.1 r.2,r.1)=‖r.2‖^2/2) ∧
      ∀ᶠ r in 𝓝 (reverseRay z),r.2∈injectivityDomain r.1 →
        (fun q : M×M => cost q.1 q.2) =ᶠ[𝓝 (r.1,riemannianExp r.1 r.2)] G := by
  obtain ⟨G,hG,ha,hagree⟩ := exists_smooth_cost_branch_with_action
    (reverseRay z) (reverseRay_nonconjugate z hz)
  refine ⟨G,hG,?_,hagree⟩
  filter_upwards [continuous_reverseRay.continuousAt.eventually ha] with r hr
  rw [norm_reverseRay,reverseRay_endpoint,reverseRay_base] at hr
  exact hr

end EndpointLowerJet
end WeakMTWTransport

end

end

end

end OAI
