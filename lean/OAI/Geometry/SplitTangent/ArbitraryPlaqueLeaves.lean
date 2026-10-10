import Mathlib
import OAI.Geometry.SplitTangent.FoliationLeaves
import OAI.Geometry.SplitTangent.TensorVanishing
import OAI.Geometry.SplitTangent.LeafJetAtlas
import OAI.Geometry.SplitTangent.Basic
import OAI.Geometry.SplitTangent.LeafPlaques
import OAI.Geometry.SplitTangent.LeafTopology

namespace OAI

/-! Arbitrary Plaque Leaves. -/

noncomputable section
open Set Filter Topology
open scoped Manifold ContDiff
universe u
namespace SplitTangent.LeafJetAtlas
variable {X : ComplexManifold.{u}} {S : TangentSplitting X} (L : LeafJetAtlas S)

lemma germIn_leaf (y : X.Carrier) : L.GermIn (L.leaf y) y := by
  let P := L.chart y
  have hys := L.mem_source y
  obtain ⟨U,V,hU,hUc,hV,hyUV,hrect⟩ := UniformPlaqueSlices.connected_rectangle
    (P.chart.open_target.mem_nhds (P.chart.map_source hys))
  filter_upwards [hU.mem_nhds hyUV.1] with a ha
  have hh := L.plaques.related_in_rectangle hUc hrect hyUV.1 ha hyUV.2
  have he : P.chart.symm ((P.chart y).1,(P.chart y).2)=y := P.chart.left_inv hys
  change L.plaques.Related (P.chart.symm ((P.chart y).1,(P.chart y).2)) _ at hh
  rw [he] at hh
  exact Relation.ReflTransGen.single hh

variable {A B : Type*} [NormedAddCommGroup A] [NormedSpace ℂ A] [CompleteSpace A]
  [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B]

lemma arbitrary_plaque_germ (P : AlignedProductChart S A B) {a : A} {b : B}
    (ht : (a,b)∈P.chart.target) :
    ∀ᶠ c in 𝓝 a,P.chart.symm (c,b)∈L.leaf (P.chart.symm (a,b)) := by
  have h := (L.germIn_iff P (P.chart.map_target ht)).mp (L.germIn_leaf (P.chart.symm (a,b)))
  change ∀ᶠ c in 𝓝 (P.chart (P.chart.symm (a,b))).1,
    P.chart.symm (c,(P.chart (P.chart.symm (a,b))).2)∈L.leaf (P.chart.symm (a,b)) at h
  simpa only [P.chart.right_inv ht] using h

lemma arbitrary_plaque_leaf_eq (P : AlignedProductChart S A B) {U : Set A} {b : B}
    (hU : IsPreconnected U) (hT : ∀a∈U,(a,b)∈P.chart.target)
    {a c : A} (ha : a∈U) (hc : c∈U) :
    L.leaf (P.chart.symm (a,b))=L.leaf (P.chart.symm (c,b)) := by
  let : PreconnectedSpace U := isPreconnected_iff_preconnectedSpace.mp hU
  have hlc : IsLocallyConstant (fun t : U => L.leaf (P.chart.symm (t.val,b))) := by
    apply (IsLocallyConstant.iff_eventually_eq _).mpr
    intro t
    filter_upwards [continuous_subtype_val.continuousAt.eventually
      (L.arbitrary_plaque_germ P (hT t.val t.property))] with v hv
    exact L.plaques.leaf_eq_of_mem hv
  exact hlc.apply_eq_of_preconnectedSpace ⟨a,ha⟩ ⟨c,hc⟩

lemma arbitrary_plaque_mem_leaf (P : AlignedProductChart S A B) {U : Set A} {b : B}
    (hU : IsPreconnected U) (hT : ∀a∈U,(a,b)∈P.chart.target)
    {a c : A} (ha : a∈U) (hc : c∈U) :
    P.chart.symm (c,b)∈L.leaf (P.chart.symm (a,b)) := by
  rw [L.arbitrary_plaque_leaf_eq P hU hT ha hc]
  exact PlaqueSystem.Reachable.refl L.plaques _

end SplitTangent.LeafJetAtlas

end

end OAI
