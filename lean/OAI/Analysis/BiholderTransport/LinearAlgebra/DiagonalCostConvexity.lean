import Mathlib
import OAI.Analysis.BiholderTransport.Regularity.NormLower

namespace OAI

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma chartCost_diagonal_coercive {a : M} {z : Model n}
    (hz : z∈(extChartAt 𝓘(ℝ,Model n) a).target) :
    ∃ m>0, ∀ d : Model n, m*‖d‖^2 ≤
      fderiv ℝ (fderiv ℝ (chartCost a ((extChartAt 𝓘(ℝ,Model n) a).symm z))) z d d := by
  let χ := extChartAt 𝓘(ℝ,Model n) a
  let x := χ.symm z
  have hx : x∈χ.source := χ.map_target hz
  have hxz : χ x=z := χ.right_inv hz
  change extChartAt 𝓘(ℝ,Model n) a x=z at hxz
  have hp := zero_mem_injectivityDomain (n := n) x
  obtain ⟨e,he,he0,hei,hinj⟩ := exists_smooth_chart_fiber_log hp
    (show riemannianExp x 0∈χ.source from by rwa [riemannianExp_zero])
  simp only [riemannianExp_zero,hxz] at he he0 hei hinj
  obtain ⟨m,hm,hbound⟩ := exists_norm_sq_lower_of_injective (fderiv ℝ e z) hinj
  refine ⟨m,hm,fun d => ?_⟩
  have hC : ContDiffAt ℝ 2 (normalCost (n := n) x 0) 0 :=
    (normalCost_contDiffAt hp).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hzero : fderiv ℝ (normalCost (n := n) x 0) 0=0 := by
    rw [(normalCost_hasFDerivAt_zero hp).fderiv]
    simp only [neg_zero,map_zero]
  have heq : chartCost a x =ᶠ[𝓝 z] (fun w => normalCost (n := n) x 0 (e w)) := by
    filter_upwards [hei] with w hw
    simp only [normalCost,riemannianExp_zero,hw,chartCost]
  rw [heq.fderiv.fderiv_eq]
  have H := second_fderiv_comp_stationary (f := normalCost (n := n) x 0) (g := e)
    (he0.symm ▸ hC) (he.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
    (by rwa [he0]) d d
  rw [H,he0]
  change m*‖d‖^2 ≤ normalHessian x 0 (fderiv ℝ e z d) (fderiv ℝ e z d)
  rw [←hessianValue_eq_normalHessian hp,hessianValue_zero]
  exact hbound d

end WeakMTWTransport

end

end OAI
