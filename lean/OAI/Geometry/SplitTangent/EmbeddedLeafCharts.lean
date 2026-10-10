import Mathlib
import OAI.Geometry.SplitTangent.EmbeddedHolomorphicAtlas
import OAI.Geometry.SplitTangent.EmbeddedPlaqueChart
import OAI.Geometry.SplitTangent.TensorVanishing
import OAI.Geometry.SplitTangent.LeafJetAtlas
import OAI.Geometry.SplitTangent.LeafRank
import OAI.Geometry.SplitTangent.Basic
import OAI.Geometry.SplitTangent.LeafPlaques

namespace OAI

/-! Embedded Leaf Charts. -/

noncomputable section
open Set Filter Topology
open scoped Manifold ContDiff
universe u
namespace SplitTangent.LeafJetAtlas
variable {X : ComplexManifold.{u}} {S : TangentSplitting X}
  (L : LeafJetAtlas S) (x₀ : X.Carrier)

section
-- Keep the structural size used by the generated EmbeddedLeafChart instance.
private local instance (index : X.Carrier) :
    SizeOf (EmbeddedPlaqueChart.Data (A := S.FirstModel index)
      (B := S.SecondModel index) (L.leaf x₀)) :=
  @EmbeddedPlaqueChart.Data._sizeOf_inst _ _ _ _ _ _ _
    (instSizeOfDefault _) (instSizeOfDefault _) (instSizeOfDefault _)
    (fun _ => instSizeOfDefault _)

structure EmbeddedLeafChart (y : L.leaf x₀) where
  index : X.Carrier
  data : EmbeddedPlaqueChart.Data (A := S.FirstModel index) (B := S.SecondModel index) (L.leaf x₀)
  ambient_eq : data.ambient=(L.chart index).chart
  point_eq : data.point=y
end

lemma exists_embeddedLeafChart {y : L.leaf x₀}
    (hy : L.plaques.LocallySinglePlaque (L.leaf x₀) y.val) :
    Nonempty (L.EmbeddedLeafChart x₀ y) := by
  obtain ⟨i,U,V,hU,hUc,hV,hrect,hys,hyUV,huniq⟩ := hy
  refine ⟨⟨i,{
    ambient := (L.chart i).chart
    U := U
    V := V
    open_U := hU
    open_V := hV
    rectangle := hrect
    point := y
    mem_source := hys
    mem_rectangle := hyUV
    saturated := ?_
    unique_transverse := huniq },rfl,rfl⟩⟩
  intro a ha
  apply L.plaques.leaf_saturated y.property
  have hh := L.plaques.related_in_rectangle hUc hrect hyUV.1 ha hyUV.2
  change L.plaques.Related ((L.chart i).chart.symm ((L.chart i).chart y.val))
    ((L.chart i).chart.symm (a,((L.chart i).chart y.val).2)) at hh
  simpa only [(L.chart i).chart.left_inv hys] using hh

namespace EmbeddedLeafChart
variable {L x₀} {y : L.leaf x₀} (D : L.EmbeddedLeafChart x₀ y)
  [PreconnectedSpace X.Carrier]

def rankEquiv : S.FirstModel D.index ≃L[ℂ] (Fin (Module.finrank ℂ (S.first x₀)) → ℂ) :=
  ContinuousLinearEquiv.ofFinrankEq (by
    have hs : y.val∈(L.chart D.index).chart.source := by
      simpa only [D.ambient_eq,D.point_eq] using D.data.mem_source
    simpa only [Module.finrank_fintype_fun_eq_card,Fintype.card_fin] using
      ((L.chart D.index).first_finrank hs).symm.trans (L.first_rank_eq y.val x₀))

def chart : OpenPartialHomeomorph (L.leaf x₀) (Fin (Module.finrank ℂ (S.first x₀)) → ℂ) :=
  D.data.chart.trans D.rankEquiv.toHomeomorph.toOpenPartialHomeomorph

lemma mem_source : y∈D.chart.source := by
  change y∈D.data.chart.source ∧ D.data.chart y∈Set.univ
  exact ⟨by simpa only [D.point_eq] using D.data.chart_mem,Set.mem_univ _⟩

lemma source_ambient {z : L.leaf x₀} (hz : z∈D.chart.source) :
    z.val∈(L.chart D.index).chart.source := by
  rw [←D.ambient_eq]
  exact hz.1.1

lemma target_pair {a : Fin (Module.finrank ℂ (S.first x₀)) → ℂ}
    (ha : a∈D.chart.target) :
    (D.rankEquiv.symm a,((L.chart D.index).chart y.val).2)∈(L.chart D.index).chart.target := by
  have hh := D.data.rectangle (show (D.rankEquiv.symm a,(D.data.ambient D.data.point.val).2)∈D.data.U ×ˢ D.data.V
    from ⟨ha.2,D.data.mem_rectangle.2⟩)
  simpa only [D.ambient_eq,D.point_eq] using hh

def forward (z : X.Carrier) := D.rankEquiv (((L.chart D.index).chart z).1)
def inverse (a : Fin (Module.finrank ℂ (S.first x₀)) → ℂ) :=
  (L.chart D.index).chart.symm (D.rankEquiv.symm a,((L.chart D.index).chart y.val).2)

lemma forward_eq (z : L.leaf x₀) : D.forward z.val=D.chart z := by
  change D.rankEquiv (((L.chart D.index).chart z.val).1)=D.rankEquiv ((D.data.ambient z.val).1)
  rw [D.ambient_eq]

lemma inverse_eq {a : Fin (Module.finrank ℂ (S.first x₀)) → ℂ}
    (ha : a∈D.chart.target) : D.inverse a=(D.chart.symm a).val := by
  change (L.chart D.index).chart.symm (D.rankEquiv.symm a,((L.chart D.index).chart y.val).2)=
    (D.data.chart.symm (D.rankEquiv.symm a)).val
  have ha' : D.rankEquiv.symm a∈D.data.chart.target := ha.2
  simpa only [D.ambient_eq,D.point_eq] using (D.data.chart_inverse_val ha').symm

lemma forward_holomorphic {z : L.leaf x₀} (hz : z∈D.chart.source) :
    ContMDiffAt (ModelWithCorners X) 𝓘(ℂ,Fin (Module.finrank ℂ (S.first x₀)) → ℂ) ω D.forward z.val := by
  exact D.rankEquiv.contDiff.contMDiff.contMDiffAt.comp z.val
    ((ContinuousLinearMap.fst ℂ (S.FirstModel D.index) (S.SecondModel D.index)).contDiff.contMDiff.contMDiffAt.comp z.val
      ((L.chart D.index).holomorphicAt (D.source_ambient hz)))

lemma inverse_holomorphic {a : Fin (Module.finrank ℂ (S.first x₀)) → ℂ}
    (ha : a∈D.chart.target) :
    ContMDiffAt 𝓘(ℂ,Fin (Module.finrank ℂ (S.first x₀)) → ℂ) (ModelWithCorners X) ω D.inverse a := by
  exact ((L.chart D.index).inverse_holomorphicAt (D.target_pair ha)).comp a
    (D.rankEquiv.symm.contDiff.contMDiff.contMDiffAt.prodMk_space contMDiffAt_const)

end EmbeddedLeafChart

variable [PreconnectedSpace X.Carrier]

def embeddedAtlas (h : ∀y∈L.leaf x₀,L.plaques.LocallySinglePlaque (L.leaf x₀) y) :
    EmbeddedHolomorphicAtlas X (Module.finrank ℂ (S.first x₀)) (L.leaf x₀) := by
  let D : ∀y : L.leaf x₀,L.EmbeddedLeafChart x₀ y :=
    fun y => Classical.choice (L.exists_embeddedLeafChart x₀ (h y.val y.property))
  exact {
    chart := fun y => (D y).chart
    mem_source := fun y => (D y).mem_source
    forward := fun y => (D y).forward
    inverse := fun y => (D y).inverse
    forward_eq := fun y z _ => (D y).forward_eq z
    inverse_eq := fun y _ ha => (D y).inverse_eq ha
    forward_holomorphic := fun y _ hz => (D y).forward_holomorphic hz
    inverse_holomorphic := fun y _ ha => (D y).inverse_holomorphic ha }

end SplitTangent.LeafJetAtlas

end

end OAI
