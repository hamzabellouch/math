import Mathlib
import OAI.Geometry.SplitTangent.TensorVanishing
import OAI.Geometry.SplitTangent.LeafJetAtlas
import OAI.Geometry.SplitTangent.Basic
import OAI.Geometry.SplitTangent.LeafPlaques
import OAI.Geometry.SplitTangent.ArbitraryPlaqueLeaves

namespace OAI

/-! Holomorphic Basic Transport. -/

noncomputable section
open Set Filter Topology
open scoped Manifold ContDiff
universe u
namespace SplitTangent.LeafJetAtlas
variable {X : ComplexManifold.{u}} {S : TangentSplitting X} (L : LeafJetAtlas S)
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

 
def Basic (f : X.Carrier → E) : Prop := ∀x y,y∈L.leaf x → f x=f y

variable {A B : Type*} [NormedAddCommGroup A] [NormedSpace ℂ A] [CompleteSpace A]
  [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B]

lemma basic_contMDiffAt_rectangle (P : AlignedProductChart S A B)
    {U : Set A} {V : Set B} (hU : IsOpen U) (hUc : IsPreconnected U) (hV : IsOpen V)
    (hrect : U ×ˢ V⊆P.chart.target) {a c : A} {b : B}
    (ha : a∈U) (hc : c∈U) (hb : b∈V)
    {f : X.Carrier → E} (hbasic : L.Basic f)
    (hf : ContMDiffAt (ModelWithCorners X) 𝓘(ℂ,E) ω f (P.chart.symm (a,b))) :
    ContMDiffAt (ModelWithCorners X) 𝓘(ℂ,E) ω f (P.chart.symm (c,b)) := by
  let x := P.chart.symm (c,b)
  let H : X.Carrier → X.Carrier := fun y => P.chart.symm (a,(P.chart y).2)
  have hxt : (c,b)∈P.chart.target := hrect ⟨hc,hb⟩
  have hxs : x∈P.chart.source := P.chart.map_target hxt
  have hx : P.chart x=(c,b) := P.chart.right_inv hxt
  have hN : ContMDiffAt (ModelWithCorners X) 𝓘(ℂ,A × B) ω
      (fun y => (a,(P.chart y).2)) x :=
    contMDiffAt_const.prodMk_space
      ((ContinuousLinearMap.snd ℂ A B).contDiff.contMDiff.contMDiffAt.comp x
        (P.holomorphicAt hxs))
  have hH : ContMDiffAt (ModelWithCorners X) (ModelWithCorners X) ω H x := by
    apply ContMDiffAt.comp x _ hN
    apply P.inverse_holomorphicAt
    simpa only [hx] using hrect ⟨ha,hb⟩
  have hHx : H x=P.chart.symm (a,b) := by simp only [H,hx]
  have hcomp : ContMDiffAt (ModelWithCorners X) 𝓘(ℂ,E) ω (f ∘ H) x := by
    apply ContMDiffAt.comp x _ hH
    rwa [hHx]
  apply hcomp.congr_of_eventuallyEq
  have hnear : ∀ᶠ y in 𝓝 x,y∈P.chart.source ∧ P.chart y∈U ×ˢ V :=
    Filter.Eventually.and (P.chart.open_source.mem_nhds hxs)
      ((P.chart.continuousAt hxs).preimage_mem_nhds (by
        rw [hx]
        exact (hU.prod hV).mem_nhds ⟨hc,hb⟩))
  filter_upwards [hnear] with y hy
  change f y=f (H y)
  have hmem := L.arbitrary_plaque_mem_leaf P hUc
    (fun k hk => hrect ⟨hk,hy.2.2⟩) hy.2.1 ha
  have he : P.chart.symm ((P.chart y).1,(P.chart y).2)=y := P.chart.left_inv hy.1
  rw [he] at hmem
  exact hbasic y _ hmem

lemma basic_contMDiffAt_local (P : AlignedProductChart S A B)
    {a : A} {b : B} (hT : (a,b)∈P.chart.target)
    {f : X.Carrier → E} (hbasic : L.Basic f) :
    ∀ᶠ c in 𝓝 a,
      (ContMDiffAt (ModelWithCorners X) 𝓘(ℂ,E) ω f (P.chart.symm (c,b)) ↔
       ContMDiffAt (ModelWithCorners X) 𝓘(ℂ,E) ω f (P.chart.symm (a,b))) := by
  obtain ⟨U,V,hU,hUc,hV,hUV,hrect⟩ := UniformPlaqueSlices.connected_rectangle
    (P.chart.open_target.mem_nhds hT)
  filter_upwards [hU.mem_nhds hUV.1] with c hc
  exact ⟨L.basic_contMDiffAt_rectangle P hU hUc hV hrect hc hUV.1 hUV.2 hbasic,
    L.basic_contMDiffAt_rectangle P hU hUc hV hrect hUV.1 hc hUV.2 hbasic⟩

lemma basic_contMDiffAt_plaque (P : AlignedProductChart S A B)
    {U : Set A} {b : B} (hUc : IsPreconnected U) (hT : ∀a∈U,(a,b)∈P.chart.target)
    {a c : A} (ha : a∈U) (hc : c∈U)
    {f : X.Carrier → E} (hbasic : L.Basic f) :
    ContMDiffAt (ModelWithCorners X) 𝓘(ℂ,E) ω f (P.chart.symm (a,b)) ↔
    ContMDiffAt (ModelWithCorners X) 𝓘(ℂ,E) ω f (P.chart.symm (c,b)) := by
  let : PreconnectedSpace U := isPreconnected_iff_preconnectedSpace.mp hUc
  let p : U → Prop := fun t => ContMDiffAt (ModelWithCorners X) 𝓘(ℂ,E) ω f (P.chart.symm (t.val,b))
  have hp : IsLocallyConstant p := by
    apply (IsLocallyConstant.iff_eventually_eq _).mpr
    intro t
    filter_upwards [continuous_subtype_val.continuousAt.eventually
      (L.basic_contMDiffAt_local P (hT t.val t.property) hbasic)] with v hv
    exact propext hv
  exact Iff.of_eq (hp.apply_eq_of_preconnectedSpace ⟨a,ha⟩ ⟨c,hc⟩)

lemma basic_contMDiffAt_related {f : X.Carrier → E} (hbasic : L.Basic f)
    {x y : X.Carrier} (hxy : L.plaques.Related x y) :
    ContMDiffAt (ModelWithCorners X) 𝓘(ℂ,E) ω f x ↔
    ContMDiffAt (ModelWithCorners X) 𝓘(ℂ,E) ω f y := by
  obtain ⟨i,b,U,hU,hT,a,ha,c,hc,rfl,rfl⟩ := hxy
  exact L.basic_contMDiffAt_plaque (L.chart i) hU hT ha hc hbasic

lemma basic_contMDiffAt_leaf {f : X.Carrier → E} (hbasic : L.Basic f)
    {x y : X.Carrier} (hxy : y∈L.leaf x) :
    ContMDiffAt (ModelWithCorners X) 𝓘(ℂ,E) ω f x ↔
    ContMDiffAt (ModelWithCorners X) 𝓘(ℂ,E) ω f y := by
  induction hxy with
  | refl => exact Iff.rfl
  | @tail y z _ hyz ih => exact ih.trans (L.basic_contMDiffAt_related hbasic hyz)

end SplitTangent.LeafJetAtlas

end

end OAI
