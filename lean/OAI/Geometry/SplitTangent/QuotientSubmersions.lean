import Mathlib
import OAI.Geometry.SplitTangent.ActualQuotientCharts
import OAI.Geometry.SplitTangent.BasicSubmersionTransport
import OAI.Geometry.SplitTangent.LeafJetAtlas
import OAI.Geometry.SplitTangent.Basic
import OAI.Geometry.SplitTangent.SwappedProductChart
import OAI.Geometry.SplitTangent.ChartSubmersion
import OAI.Geometry.SplitTangent.BasicDerivativeKernel

namespace OAI

/-! Quotient Submersions. -/

noncomputable section
open Set Filter Topology
open scoped Manifold ContDiff
universe u
namespace SplitTangent.LeafJetAtlas
variable {X : ComplexManifold.{u}} {S : TangentSplitting X}
  [CompactSpace X.Carrier] [ConnectedSpace X.Carrier]
  {L : LeafJetAtlas S} (M : LeafJetAtlas S.swap) {e : ProjectiveEmbedding X}
  {hRC : RationallyConnected e} {hdim : 0<X.dim}
namespace QuotientChartData
variable {i : X.Carrier} (D : L.QuotientChartData e hRC hdim i)

lemma chart_comp_quotient_eventuallyEq_rectangle {a : S.FirstModel i} {b : S.SecondModel i}
    (ha : a∈D.U) (hb : b∈D.V) :
    D.chart ∘ L.leafQuotient e hRC hdim =ᶠ[𝓝 ((L.chart i).chart.symm (a,b))]
      (fun y => ((L.chart i).chart y).2) := by
  let P := L.chart i
  have ht : (a,b)∈P.chart.target := D.rectangle ⟨ha,hb⟩
  have hs := P.chart.map_target ht
  have hx : P.chart (P.chart.symm (a,b))=(a,b) := P.chart.right_inv ht
  have hn := Filter.Eventually.and (P.chart.open_source.mem_nhds hs)
    ((P.chart.continuousAt hs).preimage_mem_nhds (by
      rw [hx]
      exact (D.open_U.prod D.open_V).mem_nhds ⟨ha,hb⟩))
  filter_upwards [hn] with y hy
  change D.chart (L.leafQuotient e hRC hdim y)=(P.chart y).2
  conv_lhs => rw [←P.chart.left_inv hy.1]
  exact D.chart_quotient_rectangle hy.2.1 hy.2.2

lemma chart_comp_quotient_submersion_rectangle {a : S.FirstModel i} {b : S.SecondModel i}
    (ha : a∈D.U) (hb : b∈D.V) :
    BasicSubmersionAt (D.chart ∘ L.leafQuotient e hRC hdim) ((L.chart i).chart.symm (a,b)) := by
  refine ⟨D.chart_comp_quotient_contMDiffAt_rectangle ha hb,?_⟩
  let P := L.chart i
  have hs := P.chart.map_target (D.rectangle (show (a,b)∈D.U ×ˢ D.V from ⟨ha,hb⟩))
  rw [(D.chart_comp_quotient_eventuallyEq_rectangle ha hb).mfderiv_eq]
  exact P.snd_mfderiv_surjective hs

lemma chart_comp_quotient_submersion {x : X.Carrier}
    (hx : L.leafQuotient e hRC hdim x∈D.chart.source) :
    BasicSubmersionAt (D.chart ∘ L.leafQuotient e hRC hdim) x := by
  obtain ⟨b,hb,he⟩ := hx
  exact (L.basic_submersion_leaf D.chart_comp_quotient_basic
    ((L.leafQuotient_eq_iff e hRC hdim _ _).mp he)).mp
      (D.chart_comp_quotient_submersion_rectangle D.mem_U hb)

include M in
lemma chart_comp_quotient_kernel {x : X.Carrier}
    (hx : L.leafQuotient e hRC hdim x∈D.chart.source) :
    LinearMap.ker (mfderiv (ModelWithCorners X) 𝓘(ℂ,S.SecondModel i)
      (D.chart ∘ L.leafQuotient e hRC hdim) x).toLinearMap=S.first x := by
  let : FiniteDimensional ℂ (Tangent X x) := by
    change FiniteDimensional ℂ (Model X)
    infer_instance
  let d := (mfderiv (ModelWithCorners X) 𝓘(ℂ,S.SecondModel i)
    (D.chart ∘ L.leafQuotient e hRC hdim) x).toLinearMap
  have hs := D.chart_comp_quotient_submersion hx
  have hsub : S.first x≤d.ker := by
    intro v hv
    exact L.basic_derivative_annihilates_first D.chart_comp_quotient_basic
      (hs.1.mdifferentiableAt (by simp)) hv
  apply Eq.symm
  apply Submodule.eq_of_le_of_finrank_le hsub
  have hd := d.finrank_range_add_finrank_ker
  have hsur : d.range=⊤ := LinearMap.range_eq_top.mpr hs.2
  rw [hsur,finrank_top] at hd
  have hr := (L.chart i).swap.first_finrank (by
    rw [AlignedProductChart.swap_source]
    exact L.mem_source i)
  have hc := M.first_rank_eq i x
  rw [S.swap_first] at hr hc
  have hp := (S.projector x).toLinearMap.finrank_range_add_finrank_ker
  change Module.finrank ℂ (S.first x)+Module.finrank ℂ (S.second x)=_ at hp
  change Module.finrank ℂ (S.SecondModel i)+Module.finrank ℂ d.ker=
    Module.finrank ℂ (Tangent X x) at hd
  rw [←hr,hc,Nat.add_comm] at hd
  have hk : Module.finrank ℂ d.ker=Module.finrank ℂ (S.first x) :=
    Nat.add_right_cancel (hd.trans hp.symm)
  exact hk.le

end QuotientChartData
end SplitTangent.LeafJetAtlas

end

end OAI
