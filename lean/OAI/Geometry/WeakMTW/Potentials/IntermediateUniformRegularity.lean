import Mathlib
import OAI.Geometry.WeakMTW.Potentials.IntermediateDuality
import OAI.Geometry.WeakMTW.Potentials.IntermediateUniformBounds

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold NNReal
namespace WeakMTW
noncomputable section
variable {n : ℕ} {M : Type*} [MetricSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M] [CompactSpace M]
open QuadraticEnvelope

 theorem intermediate_uniform_coordinate_c11 (hMTW : HasWeakMTW (n := n) (M := M))
     {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b < 1) (z : M) :
     ∃ r : ℝ, ∃ C : ℝ≥0, 0 < r ∧ Metric.ball (chartAt (Model n) z z) r ⊆ (chartAt (Model n) z).target ∧
       ∀ u v : M → ℝ, IsDualPair u v → ∀ t ∈ Icc a b,
         LipschitzOnWith C (fderiv ℝ (fun X : Model n => hopfLax t u ((chartAt (Model n) z).symm X)))
           (Metric.ball (chartAt (Model n) z z) r) := by
   obtain ⟨V,hV,R,K,hR,hK,hbound⟩ := intermediate_uniform_support_bounds (n := n) ha hab hb z
   let c := chartAt (Model n) z
   have hz : z ∈ c.source := mem_chart_source (Model n) z
   have hZ : c z ∈ c.target := c.map_source hz
   have hpre : c.symm ⁻¹' V ∈ 𝓝 (c z) := by
     apply (c.symm.continuousAt hZ).preimage_mem_nhds
     rwa [c.left_inv hz]
   obtain ⟨δ,hδ,hδb⟩ := Metric.mem_nhds_iff.mp (inter_mem hpre (c.open_target.mem_nhds hZ))
   let r := min R δ
   have hr : 0 < r := lt_min hR hδ
   have hballR : Metric.ball (c z) r ⊆ Metric.ball (c z) R := Metric.ball_subset_ball (min_le_left _ _)
   have hballδ : Metric.ball (c z) r ⊆ Metric.ball (c z) δ := Metric.ball_subset_ball (min_le_right _ _)
   have hball : Metric.ball (c z) (r/4) ⊆ Metric.ball (c z) r := Metric.ball_subset_ball (by linarith)
   refine ⟨r/4,⟨12*K,by positivity⟩,by positivity,fun X hX => (hδb (hballδ (hball hX))).2,?_⟩
   intro u v huv t ht
   have ht0 : 0 < t := ha.trans_le ht.1
   have ht1 : t < 1 := ht.2.trans_lt hb
   let e := potentialHomeomorph hMTW ⟨v,huv.2.1,huv.2.2.1⟩ ht0 ht1
   let q (X : Model n) := e.symm (c.symm X)
   let g (X : Model n) := intermediateUpperCost z (t,(q X).val)
   let h (X : Model n) := intermediateLowerCost z (t,(q X).val)
   apply (two_sided_uniform (g := g) (h := h) hr hK _ _).2
   · intro X hX Y hY
     have hq : (q X).val ∈ totalMinimizingSet := ((globalSupportingProperty hMTW
       ⟨v,huv.2.1,huv.2.2.1⟩).1 (q X).val.1 (q X).val.2 (q X).property).1
     have hproj : intermediateCenter (t,(q X).val) = c.symm X := e.apply_symm_apply (c.symm X)
     exact hbound t ht (q X).val hq (hproj ▸ (hδb (hballδ hX)).1) Y (hballR hY)
   · intro X hX Y
     have hs := intermediate_two_sided_supports hMTW huv ht0 ht1 (q X)
     have hproj : potentialProjection u t (q X) = c.symm X := e.apply_symm_apply (c.symm X)
     rw [hproj] at hs
     have huY := (hs.1 (c.symm Y)).2
     have hvY := (hs.1 (c.symm Y)).1
     change hopfLax t u (c.symm X)+(-cost (c.symm Y) (exp (q X).val.1 (q X).val.2)/(1-t))-
         (-cost (c.symm X) (exp (q X).val.1 (q X).val.2)/(1-t)) ≤ hopfLax t u (c.symm Y) ∧
       hopfLax t u (c.symm Y) ≤ hopfLax t u (c.symm X)+
         cost (c.symm Y) (q X).val.1/t-cost (c.symm X) (q X).val.1/t
     constructor
     · rw [neg_div,neg_div]
       linarith [hs.2.2]
     · rw [cost_comm (c.symm Y) (q X).val.1,cost_comm (c.symm X) (q X).val.1]
       linarith [hs.2.1]
end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
