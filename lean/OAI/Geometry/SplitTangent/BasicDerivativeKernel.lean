import Mathlib
import OAI.Geometry.SplitTangent.TensorVanishing
import OAI.Geometry.SplitTangent.LeafJetAtlas
import OAI.Geometry.SplitTangent.Basic
import OAI.Geometry.SplitTangent.HolomorphicBasicTransport

namespace OAI

/-! Basic Derivative Kernel. -/

noncomputable section
open Set Filter Topology
open scoped Manifold ContDiff
universe u
namespace SplitTangent.LeafJetAtlas
variable {X : ComplexManifold.{u}} {S : TangentSplitting X} (L : LeafJetAtlas S)
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

variable {A B : Type*} [NormedAddCommGroup A] [NormedSpace ℂ A] [CompleteSpace A]
  [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B]

def chartRetraction (P : AlignedProductChart S A B) (x : X.Carrier) :
    X.Carrier → X.Carrier := fun y => P.chart.symm ((P.chart x).1,(P.chart y).2)

omit [CompleteSpace A] [CompleteSpace B] in
lemma chartRetraction_self (P : AlignedProductChart S A B) {x : X.Carrier}
    (hx : x∈P.chart.source) : chartRetraction P x x=x := by
  dsimp [chartRetraction]
  exact P.chart.left_inv hx

omit [CompleteSpace A] [CompleteSpace B] in
lemma chartRetraction_mdifferentiable (P : AlignedProductChart S A B) {x : X.Carrier}
    (hx : x∈P.chart.source) :
    MDifferentiableAt (ModelWithCorners X) (ModelWithCorners X) (chartRetraction P x) x := by
  let C : A × B → A × B := fun p => ((P.chart x).1,p.2)
  have hC : MDifferentiableAt 𝓘(ℂ,A × B) 𝓘(ℂ,A × B) C (P.chart x) :=
    ((differentiableAt_const ((P.chart x).1)).prodMk differentiableAt_snd).mdifferentiableAt
  have hp := (P.holomorphicAt hx).mdifferentiableAt (by simp)
  change MDifferentiableAt _ _ (P.chart.symm ∘ (C ∘ P.chart)) x
  apply MDifferentiableAt.comp x _ (hC.comp x hp)
  apply (P.inverse_holomorphicAt _).mdifferentiableAt (by simp)
  change ((P.chart x).1,(P.chart x).2)∈P.chart.target
  exact P.chart.map_source hx

omit [CompleteSpace A] [CompleteSpace B] in
lemma chartRetraction_deriv_zero (P : AlignedProductChart S A B) {x : X.Carrier}
    (hx : x∈P.chart.source) {v : Tangent X x} (hv : v∈S.first x) :
    mfderiv (ModelWithCorners X) (ModelWithCorners X) (chartRetraction P x) x v=0 := by
  let C : A × B → A × B := fun p => ((P.chart x).1,p.2)
  let dC : A × B →L[ℂ] A × B :=
    (0 : A × B →L[ℂ] A).prod (ContinuousLinearMap.snd ℂ A B)
  have hc : HasFDerivAt C dC (P.chart x) :=
    (hasFDerivAt_const _ _).prodMk hasFDerivAt_snd
  have hcx : C (P.chart x)=P.chart x := Prod.eta _
  have hp := (P.holomorphicAt hx).mdifferentiableAt (by simp)
  have hi := (P.inverse_holomorphicAt (P.chart.map_source hx)).mdifferentiableAt (by simp)
  have hC : MDifferentiableAt 𝓘(ℂ,A × B) 𝓘(ℂ,A × B) C (P.chart x) :=
    hc.differentiableAt.mdifferentiableAt
  have hm := Submodule.mem_map_of_mem (f :=
    (mfderiv (ModelWithCorners X) 𝓘(ℂ,A × B) P.chart x).toLinearMap) hv
  rw [P.first x hx] at hm
  change (mfderiv (ModelWithCorners X) 𝓘(ℂ,A × B) P.chart x v).2=0 at hm
  change mfderiv (ModelWithCorners X) (ModelWithCorners X) (P.chart.symm ∘ (C ∘ P.chart)) x v=0
  rw [mfderiv_comp x (by simpa only [Function.comp_apply,hcx] using hi) (hC.comp x hp),
    mfderiv_comp x hC hp,mfderiv_eq_fderiv,hc.fderiv]
  change (mfderiv 𝓘(ℂ,A × B) (ModelWithCorners X) P.chart.symm (C (P.chart x)))
    (0,(mfderiv (ModelWithCorners X) 𝓘(ℂ,A × B) P.chart x v).2)=0
  rw [hm]
  exact map_zero _

omit [NormedAddCommGroup E] [NormedSpace ℂ E] in
lemma basic_chartRetraction (P : AlignedProductChart S A B) {x : X.Carrier}
    (hx : x∈P.chart.source) {f : X.Carrier → E} (hbasic : L.Basic f) :
    f ∘ chartRetraction P x =ᶠ[𝓝 x] f := by
  obtain ⟨U,V,hU,hUc,hV,hUV,hrect⟩ := UniformPlaqueSlices.connected_rectangle
    (P.chart.open_target.mem_nhds (P.chart.map_source hx))
  have hn := Filter.Eventually.and (P.chart.open_source.mem_nhds hx)
    ((P.chart.continuousAt hx).preimage_mem_nhds ((hU.prod hV).mem_nhds hUV))
  filter_upwards [hn] with y hy
  have hmem := L.arbitrary_plaque_mem_leaf P hUc
    (fun a ha => hrect ⟨ha,hy.2.2⟩) hy.2.1 hUV.1
  rw [P.chart.left_inv hy.1] at hmem
  exact (hbasic y _ hmem).symm

lemma basic_derivative_annihilates_first {f : X.Carrier → E} (hbasic : L.Basic f)
    {x : X.Carrier} (hf : MDifferentiableAt (ModelWithCorners X) 𝓘(ℂ,E) f x)
    {v : Tangent X x} (hv : v∈S.first x) :
    mfderiv (ModelWithCorners X) 𝓘(ℂ,E) f x v=0 := by
  let P := L.chart x
  have hx := L.mem_source x
  have hself := chartRetraction_self P hx
  have hd := (L.basic_chartRetraction P hx hbasic).mfderiv_eq
    (I := ModelWithCorners X) (I' := 𝓘(ℂ,E))
  rw [mfderiv_comp x (by simpa only [hself] using hf)
    (chartRetraction_mdifferentiable P hx),hself] at hd
  have hdv := DFunLike.congr_fun hd v
  change mfderiv (ModelWithCorners X) 𝓘(ℂ,E) f x
    (mfderiv (ModelWithCorners X) (ModelWithCorners X) (chartRetraction P x) x v)=
      mfderiv (ModelWithCorners X) 𝓘(ℂ,E) f x v at hdv
  rw [←hdv,chartRetraction_deriv_zero P hx hv]
  exact map_zero _
end SplitTangent.LeafJetAtlas

end

end OAI
