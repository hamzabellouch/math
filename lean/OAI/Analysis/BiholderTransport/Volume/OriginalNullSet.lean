import Mathlib
import OAI.Analysis.BiholderTransport.Geodesics.ChartLipschitz
import OAI.Analysis.BiholderTransport.Volume.EuclideanVolumeFactorNe
import OAI.Analysis.BiholderTransport.Coordinates.ChartAlexandrov

namespace OAI

section

noncomputable section
open Set Filter Metric Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal

namespace WeakMTWTransport
section OriginalNullSet
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

omit [Nonempty M] in
lemma original_ae_chart_null {P:M → Prop} (hP:∀ᵐ x ∂metricVolume n,P x) (a:M) :
    ∃r>0,∃N:Set (Model n),volume N=0 ∧
      ball (extChartAt 𝓘(ℝ,Model n) a a) r ⊆ (extChartAt 𝓘(ℝ,Model n) a).target ∧
      ∀z∈ball (extChartAt 𝓘(ℝ,Model n) a a) r,z∉N →
        P ((extChartAt 𝓘(ℝ,Model n) a).symm z) := by
  let χ:=extChartAt 𝓘(ℝ,Model n) a
  obtain ⟨C,R,hR,hS,hC⟩:=exists_lipschitzOn_chart (n:=n) a
  have ht:χ a∈χ.target:=mem_extChartAt_target (I:=𝓘(ℝ,Model n)) a
  have hi:ContinuousAt χ.symm (χ a):=continuousAt_extChartAt_symm'' ht
  have he:χ.symm (χ a)=a:=χ.left_inv (mem_extChartAt_source a)
  obtain ⟨r,hr,hsub⟩:=Metric.mem_nhds_iff.mp (inter_mem
    ((isOpen_extChartAt_target a).mem_nhds ht)
    (hi.preimage_mem_nhds (he.symm ▸ ball_mem_nhds a hR)))
  let B:Set M:=ball a R ∩ {x | ¬P x}
  let N:Set (Model n):=χ '' B
  have hB:metricVolume n B=0:=measure_mono_null inter_subset_right (ae_iff.mp hP)
  have hN:volume N=0:=by
    apply (Measure.absolutelyContinuous_isAddHaarMeasure volume (metricVolume (M:=Model n) n))
    apply le_antisymm _ zero_le
    have H:=lipschitzOn_metricVolume_image_le (hC.mono (show B⊆ball a R from inter_subset_left)) n
    rw [hB,mul_zero] at H
    exact H
  refine ⟨r,hr,N,hN,fun z hz=>(hsub hz).1,?_⟩
  intro z hz hn
  by_contra hp
  apply hn
  exact ⟨χ.symm z,⟨by
    have hb:= (hsub hz).2
    change dist (χ.symm z) (χ.symm (χ a)) < R at hb
    rw [he] at hb
    exact hb,hp⟩,χ.right_inv (hsub hz).1⟩

omit [Nonempty M] in
lemma original_chart_good_null {P:M → Prop} (hP:∀ᵐ x ∂metricVolume n,P x)
    {u v:M → ℝ} (hu:Continuous u) (hdual:IsCostDualPair u v) (a:M) :
    ∃r>0,∃N:Set (Model n),volume N=0 ∧
      ball (extChartAt 𝓘(ℝ,Model n) a a) r ⊆ (extChartAt 𝓘(ℝ,Model n) a).target ∧
      ∀z∈ball (extChartAt 𝓘(ℝ,Model n) a a) r,z∉N →
        P ((extChartAt 𝓘(ℝ,Model n) a).symm z) ∧
        ∃p:Model n,∃A:Model n →L[ℝ] Model n,
          (∀d e,inner ℝ (A d) e=inner ℝ d (A e)) ∧
          HasQuadraticExpansion (fun h=>v ((extChartAt 𝓘(ℝ,Model n) a).symm (z+h))) p A := by
  obtain ⟨r,hr,N,hN,ht,hg⟩:=original_ae_chart_null (n:=n) hP a
  obtain ⟨s,hs,Q,hQ,hst,hq⟩:=original_chart_alexandrov_null (n:=n) hu hdual a
  refine ⟨min r s,lt_min hr hs,N∪Q,measure_union_null hN hQ,?_,?_⟩
  · exact (ball_subset_ball (min_le_left _ _)).trans ht
  · intro z hz hn
    have hNr:z∉N:=fun hm=>hn (Or.inl hm)
    have hQr:z∉Q:=fun hm=>hn (Or.inr hm)
    exact ⟨hg z (ball_subset_ball (min_le_left _ _) hz) hNr,
      hq z (ball_subset_ball (min_le_right _ _) hz) hQr⟩
end OriginalNullSet
end WeakMTWTransport

end
end

end OAI
