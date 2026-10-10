import Mathlib

namespace OAI

noncomputable section

open scoped Manifold ContDiff
open Set

namespace UniversalCoverSplitting

universe u v

abbrev Model (n : ℕ) := Fin n → ℂ
abbrev model (n : ℕ) := 𝓘(ℂ, Model n)

structure ComplexManifold (n : ℕ) where
  Carrier : Type u
  [topology : TopologicalSpace Carrier]
  [charted : ChartedSpace (Model n) Carrier]
  [hausdorff : T2Space Carrier]
  [secondCountable : SecondCountableTopology Carrier]
  [complexSmooth : IsManifold (model n) ∞ Carrier]

attribute [instance] ComplexManifold.topology ComplexManifold.charted
  ComplexManifold.hausdorff ComplexManifold.secondCountable ComplexManifold.complexSmooth

variable {n r₁ r₂ : ℕ}

abbrev Tangent (X : ComplexManifold.{u} n) (x : X.Carrier) := TangentSpace (model n) x
abbrev RealMetricField (X : ComplexManifold.{u} n) :=
  ∀ x : X.Carrier, Tangent X x →ₗ[ℝ] Tangent X x →ₗ[ℝ] ℝ

def metricInChart {X : ComplexManifold.{u} n} (g : RealMetricField X)
    (c : X.Carrier) (z u v : Model n) : ℝ :=
  let e := extChartAt (model n) c
  let q := mfderiv (model n) (model n) e.symm z
  g (e.symm z) (q u) (q v)

def fundamentalInChart {X : ComplexManifold.{u} n} (g : RealMetricField X)
    (c : X.Carrier) (z u v : Model n) : ℝ :=
  metricInChart g c z (Complex.I • u) v

structure KahlerMetric (X : ComplexManifold.{u} n) where
  metric : RealMetricField X
  symmetric : ∀ x u v, metric x u v = metric x v u
  positive : ∀ x u, u ≠ 0 → 0 < metric x u u
  hermitian : ∀ x u v, metric x (Complex.I • u) (Complex.I • v) = metric x u v
  smooth : ∀ c u v, ContDiffOn ℝ ∞ (fun z ↦ metricInChart metric c z u v)
    (extChartAt (model n) c).target
  closed : ∀ c z, z ∈ (extChartAt (model n) c).target → ∀ u v w : Model n,
    fderiv ℝ (fun y ↦ fundamentalInChart metric c y v w) z u +
    fderiv ℝ (fun y ↦ fundamentalInChart metric c y w u) z v +
    fderiv ℝ (fun y ↦ fundamentalInChart metric c y u v) z w = 0

abbrev ProjectionField (X : ComplexManifold.{u} n) :=
  ∀ x : X.Carrier, Tangent X x →L[ℂ] Tangent X x

def projectionInChart {X : ComplexManifold.{u} n} (P : ProjectionField X)
    (c : X.Carrier) (z : Model n) : Model n →L[ℂ] Model n :=
  let e := extChartAt (model n) c
  (mfderiv (model n) (model n) e (e.symm z)).comp
    ((P (e.symm z)).comp (mfderiv (model n) (model n) e.symm z))

def HolomorphicProjection {X : ComplexManifold.{u} n} (P : ProjectionField X) : Prop :=
  ∀ c, DifferentiableOn ℂ (projectionInChart P c) (extChartAt (model n) c).target

def Integrable {X : ComplexManifold.{u} n} (P : ProjectionField X) : Prop :=
  ∀ c U, IsOpen U → U ⊆ (extChartAt (model n) c).target →
    ∀ V W : Model n → Model n,
      DifferentiableOn ℂ V U → DifferentiableOn ℂ W U →
      (∀ z ∈ U, projectionInChart P c z (V z) = V z) →
      (∀ z ∈ U, projectionInChart P c z (W z) = W z) →
      ∀ z ∈ U, projectionInChart P c z (VectorField.lieBracket ℂ V W z) =
        VectorField.lieBracket ℂ V W z

structure HolomorphicSplitting (X : ComplexManifold.{u} n) (r₁ r₂ : ℕ) where
  projection : ProjectionField X
  idempotent : ∀ x v, projection x (projection x v) = projection x v
  holomorphic : HolomorphicProjection projection
  first_rank : ∀ x, Module.finrank ℂ (LinearMap.range (projection x).toLinearMap) = r₁
  second_rank : ∀ x, Module.finrank ℂ (LinearMap.ker (projection x).toLinearMap) = r₂

def complementaryProjection {X : ComplexManifold.{u} n}
    (S : HolomorphicSplitting X r₁ r₂) : ProjectionField X :=
  fun x ↦ ContinuousLinearMap.id ℂ (Tangent X x) - S.projection x

def LocalBiholomorphism {X : ComplexManifold.{u} n} {Z : ComplexManifold.{v} n}
    (π : Z.Carrier → X.Carrier) : Prop :=
  ∀ z, ∃ e : OpenPartialHomeomorph Z.Carrier X.Carrier,
    z ∈ e.source ∧ (∀ w ∈ e.source, e w = π w) ∧
      MDifferentiableOn (model n) (model n) e e.source ∧
      MDifferentiableOn (model n) (model n) e.symm e.target

structure OrdinaryUniversalCover (X : ComplexManifold.{u} n)
    (Z : ComplexManifold.{v} n) where
  projection : Z.Carrier → X.Carrier
  covering : IsCoveringMap projection
  [connected : ConnectedSpace Z.Carrier]
  [simplyConnected : SimplyConnectedSpace Z.Carrier]
  liftedComplexStructure : LocalBiholomorphism projection

def CompatibleProduct {X : ComplexManifold.{u} n} {Z : ComplexManifold.{v} n}
    (S : HolomorphicSplitting X r₁ r₂) (π : OrdinaryUniversalCover X Z)
    (Y₁ : ComplexManifold.{v} r₁) (Y₂ : ComplexManifold.{v} r₂) : Prop :=
  ∃ Φ : Z.Carrier ≃ₜ (Y₁.Carrier × Y₂.Carrier),
    MDifferentiable (model n) ((model r₁).prod (model r₂)) Φ ∧
    MDifferentiable ((model r₁).prod (model r₂)) (model n) Φ.symm ∧
    (∀ z, Submodule.map
      (mfderiv (model n) ((model r₁).prod (model r₂)) Φ z).toLinearMap
      (Submodule.comap (mfderiv (model n) (model n) π.projection z).toLinearMap
        (LinearMap.range (S.projection (π.projection z)).toLinearMap)) =
      LinearMap.ker (ContinuousLinearMap.snd ℂ (Model r₁) (Model r₂)).toLinearMap) ∧
    (∀ z, Submodule.map
      (mfderiv (model n) ((model r₁).prod (model r₂)) Φ z).toLinearMap
      (Submodule.comap (mfderiv (model n) (model n) π.projection z).toLinearMap
        (LinearMap.ker (S.projection (π.projection z)).toLinearMap)) =
      LinearMap.ker (ContinuousLinearMap.fst ℂ (Model r₁) (Model r₂)).toLinearMap)

open Set
open scoped Manifold ContDiff
variable {n r₁ r₂ : ℕ}

theorem main (X : ComplexManifold.{u} n) [CompactSpace X.Carrier]
    [ConnectedSpace X.Carrier] (hn : 2 ≤ n) (hr₁ : 0 < r₁) (hr₂ : 0 < r₂)
    (g : KahlerMetric X) (S : HolomorphicSplitting X r₁ r₂)
    (h₁ : Integrable S.projection) (h₂ : Integrable (complementaryProjection S))
    (Z : ComplexManifold.{v} n) (π : OrdinaryUniversalCover X Z) :
    ∃ (Y₁ : ComplexManifold.{v} r₁) (Y₂ : ComplexManifold.{v} r₂),
      ConnectedSpace Y₁.Carrier ∧ ConnectedSpace Y₂.Carrier ∧
      SimplyConnectedSpace Y₁.Carrier ∧ SimplyConnectedSpace Y₂.Carrier ∧
      CompatibleProduct S π Y₁ Y₂ := by
  sorry

end UniversalCoverSplitting

end

end OAI
