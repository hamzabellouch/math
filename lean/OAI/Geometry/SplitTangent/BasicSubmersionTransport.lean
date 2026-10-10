import Mathlib
import OAI.Geometry.SplitTangent.TensorVanishing
import OAI.Geometry.SplitTangent.LeafJetAtlas
import OAI.Geometry.SplitTangent.Basic
import OAI.Geometry.SplitTangent.HolomorphicBasicTransport

namespace OAI

/-! Basic Submersion Transport. -/

noncomputable section
open Set Filter Topology
open scoped Manifold ContDiff
universe u
namespace SplitTangent.LeafJetAtlas
variable {X : ComplexManifold.{u}} {S : TangentSplitting X} (L : LeafJetAtlas S)
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def BasicSubmersionAt (f : X.Carrier → E) (x : X.Carrier) : Prop :=
  ContMDiffAt (ModelWithCorners X) 𝓘(ℂ,E) ω f x ∧
    Function.Surjective (mfderiv (ModelWithCorners X) 𝓘(ℂ,E) f x)

variable {A B : Type*} [NormedAddCommGroup A] [NormedSpace ℂ A] [CompleteSpace A]
  [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B]

lemma basic_submersion_rectangle (P : AlignedProductChart S A B)
    {U : Set A} {V : Set B} (hU : IsOpen U) (hUc : IsPreconnected U) (hV : IsOpen V)
    (hrect : U ×ˢ V⊆P.chart.target) {a c : A} {b : B}
    (ha : a∈U) (hc : c∈U) (hb : b∈V)
    {f : X.Carrier → E} (hbasic : L.Basic f)
    (hf : BasicSubmersionAt f (P.chart.symm (a,b))) :
    BasicSubmersionAt f (P.chart.symm (c,b)) := by
  have hfc := L.basic_contMDiffAt_rectangle P hU hUc hV hrect ha hc hb hbasic hf.1
  refine ⟨hfc,?_⟩
  let x := P.chart.symm (a,b)
  let H : X.Carrier → X.Carrier := fun y => P.chart.symm (c,(P.chart y).2)
  have hxt : (a,b)∈P.chart.target := hrect ⟨ha,hb⟩
  have hxs : x∈P.chart.source := P.chart.map_target hxt
  have hx : P.chart x=(a,b) := P.chart.right_inv hxt
  have hN : ContMDiffAt (ModelWithCorners X) 𝓘(ℂ,A × B) ω
      (fun y => (c,(P.chart y).2)) x :=
    contMDiffAt_const.prodMk_space
      ((ContinuousLinearMap.snd ℂ A B).contDiff.contMDiff.contMDiffAt.comp x
        (P.holomorphicAt hxs))
  have hH : ContMDiffAt (ModelWithCorners X) (ModelWithCorners X) ω H x := by
    apply ContMDiffAt.comp x _ hN
    apply P.inverse_holomorphicAt
    simpa only [hx] using hrect (show (c,b)∈U ×ˢ V from ⟨hc,hb⟩)
  have hHx : H x=P.chart.symm (c,b) := by simp only [H,hx]
  have heq : f ∘ H =ᶠ[𝓝 x] f := by
    have hnear : ∀ᶠ y in 𝓝 x,y∈P.chart.source ∧ P.chart y∈U ×ˢ V :=
      Filter.Eventually.and (P.chart.open_source.mem_nhds hxs)
        ((P.chart.continuousAt hxs).preimage_mem_nhds (by
          rw [hx]
          exact (hU.prod hV).mem_nhds ⟨ha,hb⟩))
    filter_upwards [hnear] with y hy
    have hmem := L.arbitrary_plaque_mem_leaf P hUc
      (fun k hk => hrect ⟨hk,hy.2.2⟩) hy.2.1 hc
    rw [P.chart.left_inv hy.1] at hmem
    exact (hbasic y _ hmem).symm
  have hd := heq.mfderiv_eq (I := ModelWithCorners X) (I' := 𝓘(ℂ,E))
  have hdiff : MDifferentiableAt (ModelWithCorners X) 𝓘(ℂ,E) f (H x) := by
    rw [hHx]
    exact hfc.mdifferentiableAt (by simp)
  rw [mfderiv_comp x hdiff (hH.mdifferentiableAt (by simp)),hHx] at hd
  have hs : Function.Surjective ((mfderiv (ModelWithCorners X) 𝓘(ℂ,E) f (P.chart.symm (c,b))).comp
      (mfderiv (ModelWithCorners X) (ModelWithCorners X) H x)) := by
    rw [hd]
    exact hf.2
  intro v
  obtain ⟨w,hw⟩ := hs v
  exact ⟨mfderiv (ModelWithCorners X) (ModelWithCorners X) H x w,hw⟩

lemma basic_submersion_local (P : AlignedProductChart S A B)
    {a : A} {b : B} (hT : (a,b)∈P.chart.target)
    {f : X.Carrier → E} (hbasic : L.Basic f) :
    ∀ᶠ c in 𝓝 a, BasicSubmersionAt f (P.chart.symm (c,b)) ↔
      BasicSubmersionAt f (P.chart.symm (a,b)) := by
  obtain ⟨U,V,hU,hUc,hV,hUV,hrect⟩ := UniformPlaqueSlices.connected_rectangle
    (P.chart.open_target.mem_nhds hT)
  filter_upwards [hU.mem_nhds hUV.1] with c hc
  exact ⟨L.basic_submersion_rectangle P hU hUc hV hrect hc hUV.1 hUV.2 hbasic,
    L.basic_submersion_rectangle P hU hUc hV hrect hUV.1 hc hUV.2 hbasic⟩

lemma basic_submersion_plaque (P : AlignedProductChart S A B)
    {U : Set A} {b : B} (hUc : IsPreconnected U) (hT : ∀a∈U,(a,b)∈P.chart.target)
    {a c : A} (ha : a∈U) (hc : c∈U) {f : X.Carrier → E} (hbasic : L.Basic f) :
    BasicSubmersionAt f (P.chart.symm (a,b)) ↔ BasicSubmersionAt f (P.chart.symm (c,b)) := by
  let : PreconnectedSpace U := isPreconnected_iff_preconnectedSpace.mp hUc
  let p : U → Prop := fun t => BasicSubmersionAt f (P.chart.symm (t.val,b))
  have hp : IsLocallyConstant p := by
    apply (IsLocallyConstant.iff_eventually_eq _).mpr
    intro t
    filter_upwards [continuous_subtype_val.continuousAt.eventually
      (L.basic_submersion_local P (hT t.val t.property) hbasic)] with s hs
    exact propext hs
  exact Iff.of_eq (hp.apply_eq_of_preconnectedSpace ⟨a,ha⟩ ⟨c,hc⟩)

lemma basic_submersion_leaf {f : X.Carrier → E} (hbasic : L.Basic f)
    {x y : X.Carrier} (hxy : y∈L.leaf x) : BasicSubmersionAt f x ↔ BasicSubmersionAt f y := by
  induction hxy with
  | refl => exact Iff.rfl
  | @tail y z _ hyz ih =>
    obtain ⟨i,b,U,hU,hT,a,ha,c,hc,rfl,rfl⟩ := hyz
    exact ih.trans (L.basic_submersion_plaque (L.chart i) hU hT ha hc hbasic)
end SplitTangent.LeafJetAtlas

end

end OAI
