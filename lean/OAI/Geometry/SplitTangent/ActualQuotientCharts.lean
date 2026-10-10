import Mathlib
import OAI.Geometry.SplitTangent.TensorVanishing
import OAI.Geometry.SplitTangent.LeafJetAtlas
import OAI.Geometry.SplitTangent.Basic
import OAI.Geometry.SplitTangent.SwappedProductChart
import OAI.Geometry.SplitTangent.CompactLeafQuotient
import OAI.Geometry.SplitTangent.GenericLeafProductCover
import OAI.Geometry.SplitTangent.HolomorphicBasicTransport
import OAI.Geometry.SplitTangent.GlobalTopologicalProduct
import OAI.Geometry.SplitTangent.TransverseQuotient

namespace OAI

/-! Actual Quotient Charts. -/

noncomputable section
open Set Filter Topology
open scoped Manifold ContDiff
universe u
namespace SplitTangent.LeafJetAtlas
variable {X : ComplexManifold.{u}} {S : TangentSplitting X}
  [CompactSpace X.Carrier] [ConnectedSpace X.Carrier]
  (L : LeafJetAtlas S) (e : ProjectiveEmbedding X) (hRC : RationallyConnected e)
  (hdim : 0<X.dim)

structure QuotientChartData (i : X.Carrier) where
  U : Set (S.FirstModel i)
  V : Set (S.SecondModel i)
  a : S.FirstModel i
  open_U : IsOpen U
  connected_U : IsPreconnected U
  open_V : IsOpen V
  rectangle : U ×ˢ V ⊆ (L.chart i).chart.target
  mem_U : a∈U
  transverse_injective : Set.InjOn
    (fun b => L.leafQuotient e hRC hdim ((L.chart i).chart.symm (a,b))) V

namespace QuotientChartData
variable {L e hRC hdim} {i : X.Carrier} (D : L.QuotientChartData e hRC hdim i)

def transversal : S.SecondModel i → L.CompactLeafSpace e hRC hdim :=
  fun b => L.leafQuotient e hRC hdim ((L.chart i).chart.symm (D.a,b))

lemma transversal_continuousOn : ContinuousOn D.transversal D.V := by
  intro b hb
  apply (L.continuous_leafQuotient e hRC hdim).continuousAt.comp_continuousWithinAt
  apply ((L.chart i).chart.symm.continuousAt (D.rectangle (show (D.a,b)∈D.U ×ˢ D.V from ⟨D.mem_U,hb⟩))).comp_continuousWithinAt
  exact (continuous_const.prodMk continuous_id).continuousWithinAt

lemma transversal_isOpenMap : IsOpenMap (D.V.domRestrict D.transversal) := by
  exact L.isOpenMap_transverseQuotient e hRC hdim i D.open_U D.connected_U D.open_V D.rectangle D.mem_U

def embedding : OpenPartialHomeomorph (S.SecondModel i) (L.CompactLeafSpace e hRC hdim) :=
  OpenPartialHomeomorph.ofContinuousOpenRestrict
    (D.transverse_injective.toPartialEquiv D.transversal D.V)
    D.transversal_continuousOn D.transversal_isOpenMap D.open_V

def chart : OpenPartialHomeomorph (L.CompactLeafSpace e hRC hdim) (S.SecondModel i) :=
  D.embedding.symm

@[simp] lemma embedding_apply (b : S.SecondModel i) : D.embedding b=D.transversal b := rfl
@[simp] lemma chart_target : D.chart.target=D.V := rfl
@[simp] lemma chart_source : D.chart.source=D.transversal '' D.V := rfl

lemma chart_quotient_rectangle {a : S.FirstModel i} {b : S.SecondModel i}
    (ha : a∈D.U) (hb : b∈D.V) :
    D.chart (L.leafQuotient e hRC hdim ((L.chart i).chart.symm (a,b)))=b := by
  have he := L.leafQuotient_constant_plaque e hRC hdim i D.connected_U D.rectangle ha D.mem_U hb
  rw [he]
  exact D.embedding.left_inv hb

lemma quotient_mem_chart_rectangle {a : S.FirstModel i} {b : S.SecondModel i}
    (ha : a∈D.U) (hb : b∈D.V) :
    L.leafQuotient e hRC hdim ((L.chart i).chart.symm (a,b))∈D.chart.source := by
  rw [chart_source]
  exact ⟨b,hb,L.leafQuotient_constant_plaque e hRC hdim i D.connected_U D.rectangle D.mem_U ha hb⟩

lemma chart_comp_quotient_basic : L.Basic (D.chart ∘ L.leafQuotient e hRC hdim) := by
  intro x y hxy
  dsimp
  rw [(L.leafQuotient_eq_iff e hRC hdim x y).mpr hxy]

lemma chart_comp_quotient_contMDiffAt_rectangle {a : S.FirstModel i} {b : S.SecondModel i}
    (ha : a∈D.U) (hb : b∈D.V) :
    ContMDiffAt (ModelWithCorners X) 𝓘(ℂ,S.SecondModel i) ω
      (D.chart ∘ L.leafQuotient e hRC hdim) ((L.chart i).chart.symm (a,b)) := by
  let x := (L.chart i).chart.symm (a,b)
  have ht : (a,b)∈(L.chart i).chart.target := D.rectangle ⟨ha,hb⟩
  have hs := (L.chart i).chart.map_target ht
  have hx : (L.chart i).chart x=(a,b) := (L.chart i).chart.right_inv ht
  have hf := (ContinuousLinearMap.snd ℂ (S.FirstModel i) (S.SecondModel i)).contDiff.contMDiff.contMDiffAt.comp x
    ((L.chart i).holomorphicAt hs)
  apply hf.congr_of_eventuallyEq
  have hN : ∀ᶠ y in 𝓝 x,y∈(L.chart i).chart.source ∧ (L.chart i).chart y∈D.U ×ˢ D.V :=
    Filter.Eventually.and ((L.chart i).chart.open_source.mem_nhds hs)
      (((L.chart i).chart.continuousAt hs).preimage_mem_nhds (by
        rw [hx]
        exact (D.open_U.prod D.open_V).mem_nhds ⟨ha,hb⟩))
  filter_upwards [hN] with y hy
  change D.chart (L.leafQuotient e hRC hdim y)=((L.chart i).chart y).2
  conv_lhs => rw [←(L.chart i).chart.left_inv hy.1]
  exact D.chart_quotient_rectangle hy.2.1 hy.2.2

lemma chart_comp_quotient_contMDiffAt {x : X.Carrier}
    (hx : L.leafQuotient e hRC hdim x∈D.chart.source) :
    ContMDiffAt (ModelWithCorners X) 𝓘(ℂ,S.SecondModel i) ω
      (D.chart ∘ L.leafQuotient e hRC hdim) x := by
  obtain ⟨b,hb,he⟩ := hx
  have hf := D.chart_comp_quotient_contMDiffAt_rectangle D.mem_U hb
  exact (L.basic_contMDiffAt_leaf D.chart_comp_quotient_basic
    ((L.leafQuotient_eq_iff e hRC hdim _ _).mp he)).mp hf

end QuotientChartData

variable (M : LeafJetAtlas S.swap)
lemma exists_quotientChartData_of_regular {x : X.Carrier}
    (hx : L.leafPair M e hRC hdim x∈L.regularLeafPairs M e hRC hdim) :
    ∃ D : L.QuotientChartData e hRC hdim x,
      L.leafQuotient e hRC hdim x∈D.chart.source := by
  obtain ⟨N,hN,hxN,hinj⟩ := L.leafPair_locally_injective_of_regular M e hRC hdim hx
  let P := L.chart x
  have hxs := L.mem_source x
  have hxt := P.chart.map_source hxs
  have hn : P.chart.target ∩ P.chart.symm ⁻¹' N∈𝓝 (P.chart x) :=
    Filter.inter_mem (P.chart.open_target.mem_nhds hxt)
      ((P.chart.symm.continuousAt hxt).preimage_mem_nhds (by
        rw [P.chart.left_inv hxs]
        exact hN.mem_nhds hxN))
  obtain ⟨r,hr,hsub⟩ := Metric.mem_nhds_iff.mp hn
  let U := Metric.ball (P.chart x).1 r
  let V := Metric.ball (P.chart x).2 r
  have hrect : U ×ˢ V ⊆ P.chart.target ∩ P.chart.symm ⁻¹' N := by
    intro p hp
    apply hsub
    simpa only [U,V,Set.mem_prod,Metric.mem_ball,Prod.dist_eq,max_lt_iff] using hp
  have ha : (P.chart x).1∈U := Metric.mem_ball_self hr
  have hb : (P.chart x).2∈V := Metric.mem_ball_self hr
  have hcol : ∀b∈V,((P.chart x).1,b)∈P.chart.target ∧ P.chart.symm ((P.chart x).1,b)∈N :=
    fun b hb => hrect (show ((P.chart x).1,b)∈U ×ˢ V from ⟨ha,hb⟩)
  have hi : Set.InjOn (fun b => L.leafQuotient e hRC hdim (P.chart.symm ((P.chart x).1,b))) V := by
    intro b hb c hc he
    have hm : M.leafQuotient e hRC hdim (P.chart.symm ((P.chart x).1,b))=
        M.leafQuotient e hRC hdim (P.chart.symm ((P.chart x).1,c)) := by
      apply (M.leafQuotient_eq_iff e hRC hdim _ _).mpr
      exact M.arbitrary_plaque_mem_leaf P.swap (b := (P.chart x).1)
        (convex_ball _ _).isPreconnected (fun k hk => by
          rw [AlignedProductChart.swap_target]
          exact (hcol k hk).1) hb hc
    have hp := hinj (hcol b hb).2 (hcol c hc).2 (Prod.ext he hm)
    have hp' := congrArg P.chart hp
    rw [P.chart.right_inv (hcol b hb).1,P.chart.right_inv (hcol c hc).1] at hp'
    exact congrArg Prod.snd hp'
  let D : L.QuotientChartData e hRC hdim x :=
    ⟨U,V,(P.chart x).1,Metric.isOpen_ball,(convex_ball _ _).isPreconnected,
      Metric.isOpen_ball,(fun p hp => (hrect hp).1),ha,hi⟩
  refine ⟨D,?_⟩
  have h := D.quotient_mem_chart_rectangle ha hb
  simpa only [P,Prod.eta,(L.chart x).chart.left_inv hxs] using h

end SplitTangent.LeafJetAtlas

end

end OAI
