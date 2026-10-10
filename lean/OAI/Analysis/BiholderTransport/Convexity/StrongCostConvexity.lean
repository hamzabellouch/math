import Mathlib
import OAI.Analysis.BiholderTransport.LinearAlgebra.DiagonalCostConvexity
import OAI.Analysis.BiholderTransport.Coordinates.ShortLocalMinimum
import OAI.Analysis.BiholderTransport.LinearAlgebra.OuterDisplacementJetBound

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

local instance strongCostDualGroup : NormedAddCommGroup (Model n →L[ℝ] ℝ) := inferInstance
local instance strongCostDualSpace : NormedSpace ℝ (Model n →L[ℝ] ℝ) := inferInstance
local instance strongCostBilinearGroup : NormedAddCommGroup (Model n →L[ℝ] Model n →L[ℝ] ℝ) := inferInstance
local instance strongCostBilinearSpace : NormedSpace ℝ (Model n →L[ℝ] Model n →L[ℝ] ℝ) := inferInstance

lemma chartCost_uniform_strongConvex {a : M} {x : Model n}
    (hx : x∈(extChartAt 𝓘(ℝ,Model n) a).target) :
    ∃ m>0,∃ r>0,∃ V∈𝓝 x,∀ z∈V,
      StrongConvexOn (Metric.closedBall x r) m
        (chartCost a ((extChartAt 𝓘(ℝ,Model n) a).symm z)) := by
  let F : Model n → Model n → ℝ := fun z =>
    chartCost a ((extChartAt 𝓘(ℝ,Model n) a).symm z)
  have hc : ContDiffAt ℝ ∞ (Function.uncurry F) (x,x) :=
    chartCost_pair_contDiffAt_diagonal hx
  have hH : ContinuousAt (fun q : Model n×Model n =>
      fderiv ℝ (fderiv ℝ (F q.1)) q.2) (x,x) :=
    (ContDiffAt.partial_snd_fderiv_two hc).continuousAt
  obtain ⟨k,hk,hpos⟩ := chartCost_diagonal_coercive hx
  have H := @ContinuousAt.norm (Model n×Model n) (Model n →L[ℝ] Model n →L[ℝ] ℝ) _ _ _ _
    (hH.sub (continuousAt_const (y := fderiv ℝ (fderiv ℝ (F x)) x)))
  have hn : ∀ᶠ q : Model n×Model n in 𝓝 (x,x),
      ‖fderiv ℝ (fderiv ℝ (F q.1)) q.2-fderiv ℝ (fderiv ℝ (F x)) x‖<k/2 := by
    apply H.eventually_lt continuousAt_const
    simpa only [Pi.sub_apply,Prod.fst,Prod.snd,sub_self,ContinuousLinearMap.opNorm_zero]
      using (half_pos hk)
  have hd : ∀ᶠ q : Model n×Model n in 𝓝 (x,x),ContDiffAt ℝ 2 (F q.1) q.2 := by
    filter_upwards [(hc.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).eventually (by simp)] with q hq
    exact hq.comp (f := fun z:Model n => (q.1,z)) q.2 (contDiffAt_const.prodMk contDiffAt_id)
  obtain ⟨V,hV,U,hU,hVU⟩ := mem_nhds_prod_iff.mp (hn.and hd)
  obtain ⟨r,hr,hrU⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hU
  refine ⟨k/2,half_pos hk,r,hr,V,hV,?_⟩
  intro z hz
  apply strongConvexOn_of_hessian_lower (convex_closedBall x r)
    (fun w hw => (hVU (a := (z,w)) ⟨hz,hrU hw⟩).2)
  intro w hw d
  have hn' := (hVU (a := (z,w)) ⟨hz,hrU hw⟩).1
  have hb := (fderiv ℝ (fderiv ℝ (F z)) w-fderiv ℝ (fderiv ℝ (F x)) x).le_opNorm₂ d d
  have hh := hpos d
  have hm := mul_le_mul_of_nonneg_right hn'.le (sq_nonneg ‖d‖)
  have ha := neg_le_abs (fderiv ℝ (fderiv ℝ (F z)) w d d-
    fderiv ℝ (fderiv ℝ (F x)) x d d)
  simp only [sub_apply,Real.norm_eq_abs] at hb
  dsimp only [F] at hb ha hm
  nlinarith only [hb,ha,hh,hm]
end WeakMTWTransport

end

end OAI
