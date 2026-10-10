import Mathlib
import OAI.Analysis.BiholderTransport.Regularity.ReverseRegular
import OAI.Analysis.BiholderTransport.Regularity.ActiveGraphLimit
import OAI.Analysis.BiholderTransport.Coordinates.GraphCoordinates

namespace OAI

section

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
section CenterRayLimit
variable {n : ℕ} {M : Type*} [MetricSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]

def chartRay (c:M) (b r:Model n) : TangentBundle 𝓘(ℝ,Model n) M :=
  ⟨(extChartAt 𝓘(ℝ,Model n) c).symm b,chartFiberInverse c b r⟩

lemma chartRay_at_center (c:M) (r:Model n) :
    chartRay c (extChartAt 𝓘(ℝ,Model n) c c) r=⟨c,r⟩ := by
  simp only [chartRay,chartFiberInverse_at_center]
  exact congrArg (fun y:M=>(⟨y,r⟩:TangentBundle 𝓘(ℝ,Model n) M))
    ((extChartAt 𝓘(ℝ,Model n) c).left_inv (mem_extChartAt_source c))

lemma chartRay_tendsto {c:M} {b r:ℕ → Model n} {r0:Model n}
    (hb:Tendsto b atTop (𝓝 (extChartAt 𝓘(ℝ,Model n) c c)))
    (hr:Tendsto r atTop (𝓝 r0)) :
    Tendsto (fun k=>chartRay c (b k) (r k)) atTop
      (𝓝 (⟨c,r0⟩:TangentBundle 𝓘(ℝ,Model n) M)) := by
  let χ:=extChartAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n))
    (⟨c,0⟩:TangentBundle 𝓘(ℝ,Model n) M)
  have hc:extChartAt 𝓘(ℝ,Model n) c c∈(extChartAt 𝓘(ℝ,Model n) c).target:=
    (extChartAt 𝓘(ℝ,Model n) c).map_source (mem_extChartAt_source c)
  have ht:(extChartAt 𝓘(ℝ,Model n) c c,r0)∈χ.target:=
    (tangent_chart_target_iff _ _).mpr hc
  have H: Tendsto (fun k=>χ.symm (b k,r k)) atTop
      (𝓝 (χ.symm (extChartAt 𝓘(ℝ,Model n) c c,r0))):=
    (continuousAt_extChartAt_symm'' ht).tendsto.comp (hb.prodMk_nhds hr)
  rw [tangent_chart_symm_trivialization hc] at H
  change Tendsto _ _ (𝓝 (chartRay c (extChartAt 𝓘(ℝ,Model n) c c) r0)) at H
  rw [chartRay_at_center] at H
  apply H.congr'
  filter_upwards [hb.eventually ((isOpen_extChartAt_target _).mem_nhds hc)] with k hk
  exact tangent_chart_symm_trivialization hk

section
variable [CompactSpace M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]

lemma modified_reverseRay_tendsto {c:M} {b r:ℕ → Model n} {l:ℕ → ℝ} {r0:Model n} {l0:ℝ}
    (hb:Tendsto b atTop (𝓝 (extChartAt 𝓘(ℝ,Model n) c c)))
    (hr:Tendsto r atTop (𝓝 r0)) (hl:Tendsto l atTop (𝓝 l0)) :
    Tendsto (fun k=>reverseRay (tangentScale (l k) (chartRay c (b k) (r k)))) atTop
      (𝓝 (reverseRay (⟨c,l0 • r0⟩:TangentBundle 𝓘(ℝ,Model n) M))) := by
  exact continuous_reverseRay.continuousAt.tendsto.comp
    (contMDiff_tangentScale.continuous.continuousAt.tendsto.comp
      (hl.prodMk_nhds (chartRay_tendsto hb hr)))

end

lemma graph_coordinates_tendsto {q:ℕ → TangentBundle 𝓘(ℝ,Model n) M}
    {q0:TangentBundle 𝓘(ℝ,Model n) M} (hq:Tendsto q atTop (𝓝 q0)) :
    Tendsto (fun k=>graphBaseCoordinate q0.1 (q k)) atTop
      (𝓝 (extChartAt 𝓘(ℝ,Model n) q0.1 q0.1)) ∧
    Tendsto (fun k=>graphVelocityCoordinate q0.1 (q k)) atTop (𝓝 q0.2) := by
  let χ:=extChartAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n))
    (⟨q0.1,0⟩:TangentBundle 𝓘(ℝ,Model n) M)
  have hs:q0∈χ.source:=(tangent_chart_source_iff _ _).mpr (mem_extChartAt_source _)
  have H:=((continuousOn_extChartAt _).continuousAt
    ((isOpen_extChartAt_source _).mem_nhds hs)).tendsto.comp hq
  have HV:Tendsto (fun k=>graphVelocityCoordinate q0.1 (q k)) atTop
      (𝓝 (graphVelocityCoordinate q0.1 q0)):=H.snd_nhds
  rw [graph_coordinates_at_center] at HV
  exact ⟨H.fst_nhds,HV⟩

end CenterRayLimit
end WeakMTWTransport

end
end

end OAI
