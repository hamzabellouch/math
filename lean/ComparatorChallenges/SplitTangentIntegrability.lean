import Mathlib

namespace OAI

 

noncomputable section
open scoped Manifold ContDiff LinearAlgebra.Projectivization
open Set Bundle

universe u
namespace SplitTangent

 
structure ComplexManifold where
  dim : ℕ
  Carrier : Type u
  [topology : TopologicalSpace Carrier]
  [charts : ChartedSpace (Fin dim → ℂ) Carrier]
  [holomorphicAtlas : IsManifold 𝓘(ℂ, Fin dim → ℂ) ω Carrier]
  [hausdorff : T2Space Carrier]
  [secondCountable : SecondCountableTopology Carrier]

attribute [instance] ComplexManifold.topology ComplexManifold.charts
  ComplexManifold.holomorphicAtlas ComplexManifold.hausdorff
  ComplexManifold.secondCountable

abbrev Model (X : ComplexManifold.{u}) := Fin X.dim → ℂ
abbrev ModelWithCorners (X : ComplexManifold.{u}) := 𝓘(ℂ, Model X)
abbrev Tangent (X : ComplexManifold.{u}) (x : X.Carrier) :=
  TangentSpace (ModelWithCorners X) x

abbrev ProjectiveSpace (N : ℕ) := ℙ ℂ (Fin (N + 1) → ℂ)

 

def projectiveCoordinates {N : ℕ} (i : Fin (N + 1))
    (p : ProjectiveSpace N) : Fin (N + 1) → ℂ :=
  fun j => (p.rep i)⁻¹ * p.rep j

 

structure ProjectiveEmbedding (X : ComplexManifold.{u}) where
  N : ℕ
  map : X.Carrier → ProjectiveSpace N
  injective : Function.Injective map
  open_patch : ∀ i, IsOpen {x | (map x).rep i ≠ 0}
  holomorphic : ∀ i, ContMDiffOn (ModelWithCorners X) 𝓘(ℂ, Fin (N + 1) → ℂ) ω
    (fun x => projectiveCoordinates i (map x)) {x | (map x).rep i ≠ 0}
  immersion : ∀ x i, (map x).rep i ≠ 0 → Function.Injective
    (mfderiv (ModelWithCorners X) 𝓘(ℂ, Fin (N + 1) → ℂ)
      (fun y => projectiveCoordinates i (map y)) x)

 
structure RationalCurve (X : ComplexManifold.{u}) where
  finite : ℂ → X.Carrier
  infinity : ℂ → X.Carrier
  finite_holomorphic : ContMDiff 𝓘(ℂ, ℂ) (ModelWithCorners X) ω finite
  infinity_holomorphic : ContMDiff 𝓘(ℂ, ℂ) (ModelWithCorners X) ω infinity
  overlap : ∀ z : ℂ, z ≠ 0 → finite z = infinity z⁻¹

def RationalCurve.value {X : ComplexManifold.{u}} (g : RationalCurve X)
    (z : OnePoint ℂ) : X.Carrier :=
  z.elim (g.infinity 0) g.finite

abbrev PairPolynomial (N : ℕ) := MvPolynomial (Fin 2 × Fin (N + 1)) ℂ

 
def Bihomogeneous {N : ℕ} (p : PairPolynomial N) : Prop :=
  ∃ a b : ℕ, ∀ m ∈ p.support,
    (∑ i : Fin (N + 1), m (0, i)) = a ∧
    (∑ i : Fin (N + 1), m (1, i)) = b

def pairEval {X : ComplexManifold.{u}} (e : ProjectiveEmbedding X)
    (p : PairPolynomial e.N) (xy : X.Carrier × X.Carrier) : ℂ :=
  MvPolynomial.eval
    (fun k : Fin 2 × Fin (e.N + 1) =>
      if k.1 = 0 then (e.map xy.1).rep k.2 else (e.map xy.2).rep k.2) p

 

def IsZariskiOpenPair {X : ComplexManifold.{u}} (e : ProjectiveEmbedding X)
    (U : Set (X.Carrier × X.Carrier)) : Prop :=
  ∃ equations : Set (PairPolynomial e.N),
    (∀ p ∈ equations, Bihomogeneous p) ∧
    U = {xy | ∃ p ∈ equations, pairEval e p xy ≠ 0}

 

def RationallyConnected {X : ComplexManifold.{u}} (e : ProjectiveEmbedding X) : Prop :=
  ∃ U : Set (X.Carrier × X.Carrier), IsZariskiOpenPair e U ∧ U.Nonempty ∧ Dense U ∧
    ∀ xy ∈ U, ∃ g : RationalCurve X, ∃ a b : OnePoint ℂ,
      g.value a = xy.1 ∧ g.value b = xy.2

 

structure TangentSplitting (X : ComplexManifold.{u}) where
  projector : ∀ x : X.Carrier, Tangent X x →L[ℂ] Tangent X x
  idempotent : ∀ x v, projector x (projector x v) = projector x v
  holomorphic : ContMDiff
    ((ModelWithCorners X).prod 𝓘(ℂ, Model X))
    ((ModelWithCorners X).prod 𝓘(ℂ, Model X)) ω
    (fun v : TangentBundle (ModelWithCorners X) X.Carrier =>
      (⟨v.proj, projector v.proj v.2⟩ : TangentBundle (ModelWithCorners X) X.Carrier))
  first_positive : ∀ x, 0 < Module.finrank ℂ (LinearMap.range (projector x).toLinearMap)
  second_positive : ∀ x, 0 < Module.finrank ℂ (LinearMap.ker (projector x).toLinearMap)

def TangentSplitting.first {X : ComplexManifold.{u}} (S : TangentSplitting X) (x : X.Carrier) :
    Submodule ℂ (Tangent X x) := LinearMap.range (S.projector x).toLinearMap

def TangentSplitting.second {X : ComplexManifold.{u}} (S : TangentSplitting X) (x : X.Carrier) :
    Submodule ℂ (Tangent X x) := LinearMap.ker (S.projector x).toLinearMap

 

def HolomorphicSectionOn (X : ComplexManifold.{u})
    (V : ∀ x : X.Carrier, Tangent X x) (U : Set X.Carrier) : Prop :=
  ContMDiffOn (ModelWithCorners X) ((ModelWithCorners X).prod 𝓘(ℂ, Model X)) ω
    (fun x => (⟨x, V x⟩ : TangentBundle (ModelWithCorners X) X.Carrier)) U

 
def Integrable (X : ComplexManifold.{u}) (D : ∀ x : X.Carrier, Submodule ℂ (Tangent X x)) : Prop :=
  ∀ U : Set X.Carrier, IsOpen U → ∀ V W : ∀ x : X.Carrier, Tangent X x,
    HolomorphicSectionOn X V U → HolomorphicSectionOn X W U →
    (∀ x ∈ U, V x ∈ D x) → (∀ x ∈ U, W x ∈ D x) →
    ∀ x ∈ U, VectorField.mlieBracketWithin (ModelWithCorners X) V W U x ∈ D x

 

def IntegrabilityStatement : Prop :=
  ∀ (X : ComplexManifold.{u}), ConnectedSpace X.Carrier → CompactSpace X.Carrier →
    2 ≤ X.dim → ∀ e : ProjectiveEmbedding X, RationallyConnected e →
    ∀ S : TangentSplitting X, Integrable X S.first ∧ Integrable X S.second

theorem integrability_main : IntegrabilityStatement.{u} := by
  sorry

end SplitTangent

end

end OAI
