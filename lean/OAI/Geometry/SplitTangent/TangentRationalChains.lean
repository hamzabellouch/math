import Mathlib
import OAI.Geometry.SplitTangent.BoxTransportBase
import OAI.Geometry.SplitTangent.Basic
import OAI.Geometry.SplitTangent.RationalFamilyCover

namespace OAI

/-! Tangent Rational Chains. -/

noncomputable section
open Set Filter Topology
open scoped ContDiff Manifold
universe u
namespace SplitTangent

 

def RationalCurve.TangentTo {X : ComplexManifold.{u}} (g : RationalCurve X)
    (D : ∀x : X.Carrier, Submodule ℂ (Tangent X x)) : Prop :=
  (∀z, mfderiv 𝓘(ℂ,ℂ) (ModelWithCorners X) g.finite z (1 : ℂ) ∈ D (g.finite z)) ∧
  (∀z, mfderiv 𝓘(ℂ,ℂ) (ModelWithCorners X) g.infinity z (1 : ℂ) ∈ D (g.infinity z))

namespace TangentBox
variable {X : ComplexManifold.{u}} {S : TangentSplitting X} {g : RationalCurve X}
  (B : TangentBox S g)

 
def horizontal (b : Bool) (t : ℂ) : RationalCurve X where
  finite z := B.chart false b (z,t)
  infinity z := B.chart true b (z,t)
  finite_holomorphic := (B.holomorphic false b).comp
    ((contDiff_id.prodMk contDiff_const : ContDiff ℂ ω (fun z : ℂ => (z,t))).contMDiff)
  infinity_holomorphic := (B.holomorphic true b).comp
    ((contDiff_id.prodMk contDiff_const : ContDiff ℂ ω (fun z : ℂ => (z,t))).contMDiff)
  overlap z hz := by
    have h := B.overlap false b true b (z,t) ⟨fun _ => hz,fun h => (h rfl).elim⟩
    simpa [ReciprocalCharts.changeChart,ReciprocalCharts.coord] using h

lemma horizontal_derivative (a b : Bool) (s t : ℂ) :
    mfderiv 𝓘(ℂ,ℂ) (ModelWithCorners X) (fun z => B.chart a b (z,t)) s (1 : ℂ)=
      mfderiv 𝓘(ℂ,ℂ × ℂ) (ModelWithCorners X) (B.chart a b) (s,t) (1,0) := by
  have hd : HasFDerivAt (fun w : ℂ => (w,t))
      ((ContinuousLinearMap.id ℂ ℂ).prod (0 : ℂ →L[ℂ] ℂ)) s :=
    (hasFDerivAt_id s).prodMk (hasFDerivAt_const t s)
  have hm : MDifferentiableAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ × ℂ) (fun w : ℂ => (w,t)) s :=
    hd.differentiableAt.mdifferentiableAt
  have hchain := mfderiv_comp s ((B.holomorphic a b (s,t)).mdifferentiableAt (by simp)) hm
  change mfderiv 𝓘(ℂ,ℂ) (ModelWithCorners X)
    ((B.chart a b) ∘ (fun w : ℂ => (w,t))) s (1 : ℂ)=_
  rw [hchain,mfderiv_eq_fderiv,hd.fderiv]
  rfl

lemma horizontal_tangent (b : Bool) (t : ℂ) : (B.horizontal b t).TangentTo S.first := by
  constructor <;> intro z
  · change mfderiv 𝓘(ℂ,ℂ) (ModelWithCorners X) (fun z => B.chart false b (z,t)) z (1 : ℂ)∈_
    rw [B.horizontal_derivative]
    exact (B.tangency false b (z,t)).1
  · change mfderiv 𝓘(ℂ,ℂ) (ModelWithCorners X) (fun z => B.chart true b (z,t)) z (1 : ℂ)∈_
    rw [B.horizontal_derivative]
    exact (B.tangency true b (z,t)).1

lemma vertical_rational_tangent (a : Bool) (s : ℂ) : (B.vertical a s).TangentTo S.second :=
  ⟨fun z => B.vertical_tangent a false s z,fun z => B.vertical_tangent a true s z⟩

end TangentBox

 
def TangentRationalRelated {X : ComplexManifold.{u}}
    (D : ∀x : X.Carrier, Submodule ℂ (Tangent X x)) (x y : X.Carrier) : Prop :=
  ∃g : RationalCurve X, g.TangentTo D ∧ ∃a b : OnePoint ℂ, g.value a=x ∧ g.value b=y

 

def TangentChainRelated {X : ComplexManifold.{u}}
    (D : ∀x : X.Carrier, Submodule ℂ (Tangent X x)) :=
  Relation.ReflTransGen (TangentRationalRelated D)

lemma TangentRationalRelated.symm {X : ComplexManifold.{u}}
    {D : ∀x : X.Carrier, Submodule ℂ (Tangent X x)} {x y : X.Carrier}
    (h : TangentRationalRelated D x y) : TangentRationalRelated D y x := by
  obtain ⟨g,hg,a,b,ha,hb⟩ := h
  exact ⟨g,hg,b,a,hb,ha⟩

 

theorem TangentSplitting.two_tangent_curves_of_rational
    {X : ComplexManifold.{u}} [CompactSpace X.Carrier] (S : TangentSplitting X) (e : ProjectiveEmbedding X)
    (g : RationalCurve X) (a b : ℂ) :
    ∃z, TangentRationalRelated S.first (g.finite a) z ∧
      TangentRationalRelated S.second z (g.finite b) := by
  obtain ⟨B⟩ := S.exists_projective_tangent_box e g
  refine ⟨B.chart false false (b,a), ?_, ?_⟩
  · refine ⟨B.horizontal false a,B.horizontal_tangent false a,
      (a : OnePoint ℂ),(b : OnePoint ℂ),?_,rfl⟩
    exact B.finite_diagonal a
  · refine ⟨B.vertical false b,B.vertical_rational_tangent false b,
      (a : OnePoint ℂ),(b : OnePoint ℂ),rfl,?_⟩
    exact B.finite_diagonal b

lemma TangentChainRelated.refl {X : ComplexManifold.{u}}
    (D : ∀ x : X.Carrier, Submodule ℂ (Tangent X x)) (x : X.Carrier) :
    TangentChainRelated D x x := Relation.ReflTransGen.refl

lemma TangentChainRelated.trans {X : ComplexManifold.{u}}
    {D : ∀ x : X.Carrier, Submodule ℂ (Tangent X x)} {x y z : X.Carrier}
    (hxy : TangentChainRelated D x y) (hyz : TangentChainRelated D y z) :
    TangentChainRelated D x z := Relation.ReflTransGen.trans hxy hyz

lemma TangentChainRelated.symm {X : ComplexManifold.{u}}
    {D : ∀ x : X.Carrier, Submodule ℂ (Tangent X x)} {x y : X.Carrier}
    (h : TangentChainRelated D x y) : TangentChainRelated D y x := by
  induction h with
  | refl => exact .refl _ _
  | @tail y z _ hyz ih =>
    exact (Relation.ReflTransGen.single hyz.symm).trans ih

def tangentChainSetoid {X : ComplexManifold.{u}}
    (D : ∀ x : X.Carrier, Submodule ℂ (Tangent X x)) : Setoid X.Carrier where
  r := TangentChainRelated D
  iseqv := ⟨.refl D, fun h => h.symm, fun h k => h.trans k⟩

 

theorem TangentSplitting.general_mixed_tangent_curves
    {X : ComplexManifold.{u}} [CompactSpace X.Carrier] (S : TangentSplitting X)
    (e : ProjectiveEmbedding X) (hRC : RationallyConnected e) :
    ∃ U : Set (X.Carrier × X.Carrier), IsZariskiOpenPair e U ∧ U.Nonempty ∧ Dense U ∧
      ∀ xy ∈ U, ∃ z, TangentRationalRelated S.first xy.1 z ∧
        TangentRationalRelated S.second z xy.2 := by
  obtain ⟨U,hUz,hUn,hUd,hU⟩ := hRC
  refine ⟨U,hUz,hUn,hUd,?_⟩
  intro xy hxy
  obtain ⟨g,h0,h1⟩ := RationallyConnected.fixed_endpoints hU hxy
  simpa only [h0,h1] using S.two_tangent_curves_of_rational e g 0 1

end SplitTangent

end

end OAI
