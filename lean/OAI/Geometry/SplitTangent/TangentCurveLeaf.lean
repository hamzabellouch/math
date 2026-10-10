import Mathlib
import OAI.Geometry.SplitTangent.TensorVanishing
import OAI.Geometry.SplitTangent.LeafJetAtlas
import OAI.Geometry.SplitTangent.Basic
import OAI.Geometry.SplitTangent.LeafPlaques
import OAI.Geometry.SplitTangent.LeafTopology
import OAI.Geometry.SplitTangent.LeafGermIdentity
import OAI.Geometry.SplitTangent.TangentRationalChains

namespace OAI

/-! Tangent Curve Leaf. -/

noncomputable section
open Set Filter Topology
open scoped Manifold ContDiff
universe u
namespace SplitTangent.LeafJetAtlas
variable {X : ComplexManifold.{u}} {S : TangentSplitting X} (L : LeafJetAtlas S)

lemma tangent_curve_eventually_related {f : ℂ → X.Carrier}
    (hf : ContMDiff 𝓘(ℂ,ℂ) (ModelWithCorners X) ω f)
    (ht : ∀z,mfderiv 𝓘(ℂ,ℂ) (ModelWithCorners X) f z (1 : ℂ)∈S.first (f z)) (z : ℂ) :
    ∀ᶠ w in 𝓝 z,L.plaques.Related (f z) (f w) := by
  let P := L.chart (f z)
  have hz : f z∈P.chart.source := L.mem_source _
  have htz : P.chart (f z)∈P.chart.target := P.chart.map_source hz
  obtain ⟨U,V,hU,hUc,hV,hUV,hrect⟩ := UniformPlaqueSlices.connected_rectangle
    (P.chart.open_target.mem_nhds htz)
  have hc := (P.holomorphicAt hz).continuousAt.comp (hf z).continuousAt
  have hs : ∀ᶠ w in 𝓝 z,f w∈P.chart.source :=
    (hf z).continuousAt.preimage_mem_nhds (P.chart.open_source.mem_nhds hz)
  have hpair : ∀ᶠ w in 𝓝 z,P.chart (f w)∈U ×ˢ V :=
    hc.preimage_mem_nhds ((hU.prod hV).mem_nhds hUV)
  filter_upwards [hs,hpair,P.tangent_curve_snd_eventually hf hz ht] with w hws hwUV hwb
  have hh := L.plaques.related_in_rectangle hUc hrect hUV.1 hwUV.1 hUV.2
  have hw : P.chart.symm ((P.chart (f w)).1,(P.chart (f z)).2)=f w := by
    rw [←hwb,Prod.mk.eta,P.chart.left_inv hws]
  change L.plaques.Related (P.chart.symm ((P.chart (f z)).1,(P.chart (f z)).2))
    (P.chart.symm ((P.chart (f w)).1,(P.chart (f z)).2)) at hh
  rwa [Prod.mk.eta,P.chart.left_inv hz,hw] at hh

lemma tangent_curve_same_leaf {f : ℂ → X.Carrier}
    (hf : ContMDiff 𝓘(ℂ,ℂ) (ModelWithCorners X) ω f)
    (ht : ∀z,mfderiv 𝓘(ℂ,ℂ) (ModelWithCorners X) f z (1 : ℂ)∈S.first (f z)) (z w : ℂ) :
    f w∈L.leaf (f z) := by
  have hlc : IsLocallyConstant (fun q => L.leaf (f q)) := by
    apply (IsLocallyConstant.iff_eventually_eq _).mpr
    intro q
    filter_upwards [L.tangent_curve_eventually_related hf ht q] with t ht
    exact L.plaques.leaf_eq_of_mem (Relation.ReflTransGen.single ht)
  rw [hlc.apply_eq_of_preconnectedSpace z w]
  exact Relation.ReflTransGen.refl

lemma tangent_rational_curve_finite {g : RationalCurve X} (ht : g.TangentTo S.first) (z : ℂ) :
    g.finite z∈L.leaf (g.finite 1) :=
  L.tangent_curve_same_leaf g.finite_holomorphic ht.1 1 z

lemma tangent_rational_curve_infinity {g : RationalCurve X} (ht : g.TangentTo S.first) (z : ℂ) :
    g.infinity z∈L.leaf (g.finite 1) := by
  have hh := L.tangent_curve_same_leaf g.infinity_holomorphic ht.2 1 z
  have he : g.finite 1=g.infinity 1 := by simpa using g.overlap 1 one_ne_zero
  rwa [←he] at hh

end SplitTangent.LeafJetAtlas

end

end OAI
