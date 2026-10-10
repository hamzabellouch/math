import Mathlib

namespace OAI

namespace CoveringOrder
open Set MeasureTheory
open scoped ENNReal

abbrev Space (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- Actual discrete full-rank lattice coverings; no assumed density theorem. -/
structure LatticeCover {n : ℕ} (K : Set (Space n)) where
  lattice : Submodule ℤ (Space n)
  discrete : DiscreteTopology lattice
  fullrank : IsZLattice ℝ lattice
  covers : ∀ y, ∃ l : lattice, y - l.val ∈ K

noncomputable def euclideanVolume (n : ℕ) :
    @Measure (EuclideanSpace ℝ (Fin n))
      (@WithLp.measurableSpace 2 (Fin n → ℝ)
        (@MeasurableSpace.pi (Fin n) (fun _ => ℝ) (fun _ => Real.measurableSpace))) :=
  @Measure.map (Fin n → ℝ) (EuclideanSpace ℝ (Fin n))
    (@MeasurableSpace.pi (Fin n) (fun _ => ℝ) (fun _ => Real.measurableSpace))
    (@WithLp.measurableSpace 2 (Fin n → ℝ)
      (@MeasurableSpace.pi (Fin n) (fun _ => ℝ) (fun _ => Real.measurableSpace)))
    (@WithLp.toLp 2 (Fin n → ℝ))
    (Measure.pi (fun _ : Fin n => @volume ℝ Real.measureSpace))

noncomputable def euclideanCovolume {n : ℕ}
    (lattice : Submodule ℤ (EuclideanSpace ℝ (Fin n))) : ℝ≥0∞ :=
  addCovolume lattice (EuclideanSpace ℝ (Fin n)) (euclideanVolume n)

noncomputable def latticeDensity {n : ℕ} {K : Set (Space n)}
    (cover : LatticeCover K) : ℝ≥0∞ :=
  euclideanVolume n K / euclideanCovolume cover.lattice

noncomputable def thetaL {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) : ℝ≥0∞ :=
  ⨅ cover : LatticeCover K, latticeDensity cover

end CoveringOrder

namespace TranslativeCovering

open Set Filter MeasureTheory
open scoped ENNReal

abbrev Space (n : ℕ) := EuclideanSpace ℝ (Fin n)

def cube (n : ℕ) (R : ℝ) : Set (Space n) :=
  {x | ∀ i, -R ≤ x i ∧ x i ≤ R}

def LocallyFiniteCenters {n : ℕ} (X : Set (Space n)) : Prop :=
  ∀ B : Set (Space n), Bornology.IsBounded B → (X ∩ B).Finite

def Covers {n : ℕ} (K X : Set (Space n)) : Prop :=
  ∀ y, ∃ x ∈ X, y - x ∈ K

def ConvexBody {n : ℕ} (K : Set (Space n)) : Prop :=
  IsCompact K ∧ Convex ℝ K ∧ (interior K).Nonempty

def CentrallySymmetric {n : ℕ} (K : Set (Space n)) : Prop :=
  ∃ z, ∀ x, x ∈ K ↔ (2 : ℝ) • z - x ∈ K

noncomputable def upperCenterIntensity {n : ℕ} (X : Set (Space n)) : ℝ≥0∞ :=
  Filter.limsup (fun R : ℝ =>
    (↑(X ∩ cube n R).ncard : ℝ≥0∞) / ENNReal.ofReal ((2 * R) ^ n)) atTop

noncomputable def thetaT {n : ℕ} (K : Set (Space n)) : ℝ≥0∞ :=
  ⨅ X : {X : Set (Space n) // LocallyFiniteCenters X ∧ Covers K X},
    volume K * upperCenterIntensity X.val

end TranslativeCovering

namespace CoveringOrder
open Set MeasureTheory
open scoped ENNReal

abbrev Body (n : ℕ) := {K : Set (Space n) // TranslativeCovering.ConvexBody K}
abbrev SymmetricBody (n : ℕ) :=
  {K : Body n // TranslativeCovering.CentrallySymmetric K.val}

noncomputable def translativeSup (n : ℕ) : ℝ≥0∞ :=
  ⨆ K : Body n, TranslativeCovering.thetaT K.val

noncomputable def symmetricTranslativeSup (n : ℕ) : ℝ≥0∞ :=
  ⨆ K : SymmetricBody n, TranslativeCovering.thetaT K.val.val

noncomputable def latticeSup (n : ℕ) : ℝ≥0∞ :=
  ⨆ K : Body n, thetaL K.val

noncomputable def symmetricLatticeSup (n : ℕ) : ℝ≥0∞ :=
  ⨆ K : SymmetricBody n, thetaL K.val.val

/-- The finite real comparison scale, viewed in extended nonnegative reals. -/
def orderBounds (c C : ℝ) (n : ℕ) (a : ℝ≥0∞) : Prop :=
  ENNReal.ofReal (c * (n : ℝ) * Real.log (n : ℝ)) ≤ a ∧
    a ≤ ENNReal.ofReal (C * (n : ℝ) * Real.log (n : ℝ))

/-- All four extremal quantities have common
absolute positive comparison constants. ENNReal bounds imply finiteness rather
than mapping a potentially infinite density to zero through `toReal`. -/
def OptimalOrder : Prop :=
  ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
    orderBounds c C n (translativeSup n) ∧
    orderBounds c C n (symmetricTranslativeSup n) ∧
    orderBounds c C n (latticeSup n) ∧
    orderBounds c C n (symmetricLatticeSup n)

end CoveringOrder

/-- Translative and lattice covering densities over all convex bodies and over
centrally symmetric convex bodies have the same asymptotic order. -/
theorem CoveringOrder.optimal_order : CoveringOrder.OptimalOrder := by
  sorry

end OAI
