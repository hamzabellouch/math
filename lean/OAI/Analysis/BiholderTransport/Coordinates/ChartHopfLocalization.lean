import Mathlib
import OAI.Analysis.BiholderTransport.Regularity.HopfApproximation

namespace OAI

noncomputable section
open Set Filter Metric Manifold Bundle
open scoped Topology ContDiff NNReal

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

omit [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma uniform_hopfLax_chart_localization (L : ℝ≥0) (a : M) {R:ℝ} (hR : 0<R) :
    ∃ δ>0,∃ V∈𝓝 (extChartAt 𝓘(ℝ,Model n) a a),
      ∀ t:ℝ,0<t → t<δ → ∀ z∈V,∀ w:M → ℝ,LipschitzWith L w →
      ∀ y:M,hopfLax t w ((extChartAt 𝓘(ℝ,Model n) a).symm z)=
        w y+cost y ((extChartAt 𝓘(ℝ,Model n) a).symm z)/t →
        y∈(extChartAt 𝓘(ℝ,Model n) a).source ∧
        extChartAt 𝓘(ℝ,Model n) a y∈ball (extChartAt 𝓘(ℝ,Model n) a a) R := by
  let χ := extChartAt 𝓘(ℝ,Model n) a
  have hsrc : χ.source∩χ⁻¹'ball (χ a) R∈𝓝 a :=
    inter_mem (extChartAt_source_mem_nhds (I := 𝓘(ℝ,Model n)) a)
      ((continuousAt_extChartAt (I := 𝓘(ℝ,Model n)) a).preimage_mem_nhds (ball_mem_nhds _ hR))
  have H := uniform_hopfLax_minimizers_eventually_in L hsrc
  have hT : χ a∈χ.target := mem_extChartAt_target a
  have hi : ContinuousAt χ.symm (χ a) :=
    (continuousOn_extChartAt_symm a (χ a) hT).continuousAt ((isOpen_extChartAt_target a).mem_nhds hT)
  have he : χ.symm (χ a)=a := χ.left_inv (mem_extChartAt_source a)
  have hq : Tendsto (fun q:ℝ×Model n => (q.1,χ.symm q.2)) (𝓝 (0,χ a)) (𝓝 (0,a)) := by
    simpa only [Function.comp_apply,Prod.snd,he] using (continuousAt_fst.prodMk (hi.comp (x := ((0:ℝ),χ a)) continuousAt_snd)).tendsto
  have HH := hq.eventually H
  obtain ⟨U,hU,V,hV,hUV⟩ := mem_nhds_prod_iff.mp HH
  obtain ⟨δ,hδ,hδU⟩ := Metric.mem_nhds_iff.mp hU
  refine ⟨δ,hδ,V,hV,?_⟩
  intro t ht htδ z hz w hw y hy
  have htU : t∈U := hδU (by simpa only [mem_ball,Real.dist_eq,sub_zero,abs_of_pos ht] using htδ)
  exact hUV (a := (t,z)) ⟨htU,hz⟩ ht w hw y hy
end WeakMTWTransport

end

end OAI
