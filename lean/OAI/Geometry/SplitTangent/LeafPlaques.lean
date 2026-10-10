import Mathlib
import OAI.Geometry.SplitTangent.FoliationLeaves
import OAI.Geometry.SplitTangent.TensorVanishing
import OAI.Geometry.SplitTangent.LeafJetAtlas
import OAI.Geometry.SplitTangent.Basic
import OAI.Geometry.SplitTangent.ManifoldLeafJets

namespace OAI

/-! Leaf Plaques. -/

noncomputable section
open Set Filter Topology
open scoped Manifold ContDiff
universe u
namespace SplitTangent
namespace AlignedProductChart
variable {X : ComplexManifold.{u}} {S : TangentSplitting X}
  {A B C D : Type*}
  [NormedAddCommGroup A] [NormedSpace ℂ A]
  [NormedAddCommGroup B] [NormedSpace ℂ B]
  [NormedAddCommGroup C] [NormedSpace ℂ C] [CompleteSpace C]
  [NormedAddCommGroup D] [NormedSpace ℂ D] [CompleteSpace D]

def GermIn (P : AlignedProductChart S A B) (Z : Set X.Carrier) (y : X.Carrier) : Prop :=
  ∀ᶠ a in 𝓝 (P.chart y).1,P.chart.symm (a,(P.chart y).2)∈Z

lemma germIn_transfer [CompleteSpace A] [CompleteSpace B]
    (P : AlignedProductChart S A B) (Q : AlignedProductChart S C D)
    {Z : Set X.Carrier} {y : X.Carrier} (hy : y∈P.chart.source) (hq : y∈Q.chart.source)
    (h : Q.GermIn Z y) : P.GermIn Z y := by
  let s : A → X.Carrier := fun a => P.chart.symm (a,(P.chart y).2)
  have hs : s (P.chart y).1=y := P.chart.left_inv hy
  have hsc : ContinuousAt s (P.chart y).1 := by
    exact (P.inverse_holomorphicAt (P.chart.map_source hy)).continuousAt.comp
      (f := fun a : A => (a,(P.chart y).2)) (x := (P.chart y).1)
      (continuousAt_id.prodMk continuousAt_const)
  have ht : ContinuousAt (Q.chart ∘ s) (P.chart y).1 :=
    (Q.chart.continuousAt hq).comp_of_eq hsc hs
  have hQ : ∀ᶠ a in 𝓝 (P.chart y).1,s a∈Q.chart.source :=
    hsc.preimage_mem_nhds (by rw [hs]; exact Q.chart.open_source.mem_nhds hq)
  have hpi : Tendsto (fun a : A => (a,(P.chart y).2)) (𝓝 (P.chart y).1) (𝓝 (P.chart y)) :=
    continuousAt_id.prodMk continuousAt_const
  have haxes := hpi.eventually (P.transition_product Q (P.chart.map_source hy)
    (by simpa only [P.chart.left_inv hy] using hq))
  have hfirst : Tendsto (fun a => (Q.chart (s a)).1) (𝓝 (P.chart y).1) (𝓝 (Q.chart y).1) := by
    simpa only [ContinuousAt,Function.comp_apply,hs] using ht.fst
  filter_upwards [hQ,haxes,hfirst.eventually h] with a hQa hax ha
  have hb : (Q.chart (s a)).2=(Q.chart y).2 := by
    have hb := congrArg Prod.snd hax
    simpa only [Function.comp_apply,Prod.mk.eta,P.chart.left_inv hy,s] using hb
  change s a∈Z
  have he : Q.chart.symm ((Q.chart (s a)).1,(Q.chart y).2)=s a := by
    rw [←hb,Prod.mk.eta,Q.chart.left_inv hQa]
  rwa [he] at ha

lemma germIn_iff [CompleteSpace A] [CompleteSpace B]
    (P : AlignedProductChart S A B) (Q : AlignedProductChart S C D)
    {Z : Set X.Carrier} {y : X.Carrier} (hy : y∈P.chart.source) (hq : y∈Q.chart.source) :
    P.GermIn Z y ↔ Q.GermIn Z y :=
  ⟨Q.germIn_transfer P hq hy,P.germIn_transfer Q hy hq⟩

lemma all_jets_of_germ_zero [CompleteSpace A] [CompleteSpace B]
    (P : AlignedProductChart S A B) (L : LeafJetAtlas S)
    {f : X.Carrier → ℂ} {y : X.Carrier} (hy : y∈P.chart.source)
    (hf : ContMDiffAt (ModelWithCorners X) 𝓘(ℂ,ℂ) ω f y)
    (hz : (fun a => f (P.chart.symm (a,(P.chart y).2))) =ᶠ[𝓝 (P.chart y).1] 0) :
    ∀m,L.jet f y m=0 := by
  have hP : ∀m,P.jet f y m=0 := by
    intro m
    apply (P.jet_eq_zero_iff f hy m).mpr
    apply (HorizontalJet.value_eq_zero_iff _ _ _).mpr
    have he := (hz.iteratedFDeriv ℂ m).self_of_nhds
    simpa only [Function.comp_apply,iteratedFDeriv_zero,Pi.zero_apply] using he
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    change (L.chart y).jet f y m=0
    rw [← P.jet_independent (L.chart y) hy (L.mem_source y) hf m (fun n hn => ih n hn)]
    exact hP m

end AlignedProductChart

namespace LeafJetAtlas
variable {X : ComplexManifold.{u}} {S : TangentSplitting X} (L : LeafJetAtlas S)

def plaques : PlaqueSystem X.Carrier S.FirstModel S.SecondModel where
  chart x := (L.chart x).chart
  covering x := ⟨x,L.mem_source x⟩

abbrev leaf (x : X.Carrier) : Set X.Carrier := L.plaques.leaf x

def GermIn (Z : Set X.Carrier) (y : X.Carrier) : Prop := (L.chart y).GermIn Z y

lemma germIn_iff {A B : Type*}
    [NormedAddCommGroup A] [NormedSpace ℂ A] [CompleteSpace A]
    [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B]
    (P : AlignedProductChart S A B) {Z : Set X.Carrier} {y : X.Carrier}
    (hy : y∈P.chart.source) : L.GermIn Z y ↔ P.GermIn Z y :=
  (L.chart y).germIn_iff P (L.mem_source y) hy

lemma germIn_mem {Z : Set X.Carrier} {y : X.Carrier} (h : L.GermIn Z y) : y∈Z := by
  have he := h.self_of_nhds
  simpa only [Prod.mk.eta,(L.chart y).chart.left_inv (L.mem_source y)] using he

end LeafJetAtlas
end SplitTangent

end

end OAI
