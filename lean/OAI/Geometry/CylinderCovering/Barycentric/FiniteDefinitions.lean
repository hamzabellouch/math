import OAI.Geometry.CylinderCovering.Barycentric.SweepsDefinitions
import OAI.Geometry.CylinderCovering.Radial.RiemannDefinitions

namespace OAI

open Set MeasureTheory Filter
open scoped Topology InnerProductSpace
noncomputable section

namespace RadialCoordinates.BarycentricFinite

abbrev Space := BarycentricSpace

def midpoint (N : ℕ) (i : Fin N) : ℝ :=
  (CylinderCovering.RadialRiemann.point 0 1 N i +
    CylinderCovering.RadialRiemann.point 0 1 N (i + 1)) / 2

def secondDirection (k t : ℝ) : Space :=
  !₂[(1 + k * angular t) / 2, (-1 + k * angular t) / 2,
    -k * t^2, k * (1-t)^2]

def firstAxis (k t : ℝ) : Space := ‖firstDirection k t‖⁻¹ • firstDirection k t

def secondAxis (k t : ℝ) : Space := ‖secondDirection k t‖⁻¹ • secondDirection k t

def projection (u z : Space) : Space := z - inner ℝ u z • u

def firstLocalSweep (k : ℝ) (N : ℕ) (i : Fin N) : Set Space :=
  {z | ∃ t ∈ CylinderCovering.RadialRiemann.cell 0 1 N i,
    ∃ S ∈ Icc (0 : ℝ) (cap k t), ∃ p ∈ Icc (-1 : ℝ) 1,
      z = firstSweepPoint k t S p}

def secondLocalSweep (k : ℝ) (N : ℕ) (i : Fin N) : Set Space :=
  {z | ∃ t ∈ CylinderCovering.RadialRiemann.cell 0 1 N i,
    ∃ S ∈ Icc (0 : ℝ) (cap k t), ∃ p ∈ Icc (-1 : ℝ) 1,
      z = secondSweepPoint k t S p}

def firstBase (k : ℝ) (N : ℕ) (i : Fin N) : Set Space :=
  projection (firstAxis k (midpoint N i)) '' firstLocalSweep k N i

def secondBase (k : ℝ) (N : ℕ) (i : Fin N) : Set Space :=
  projection (secondAxis k (midpoint N i)) '' secondLocalSweep k N i

def cylinder (u : Space) (B : Set Space) : Set Space :=
  {z | ∃ b ∈ B, ∃ s : ℝ, z = b + s • u}

def area (B : Set Space) : ℝ := (Measure.euclideanHausdorffMeasure 2).real B

def totalArea (k : ℝ) (N : ℕ) : ℝ :=
  (∑ i : Fin N, area (firstBase k N i)) + ∑ i : Fin N, area (secondBase k N i)

def Statement : Prop :=
  ∀ k : ℝ, 0 < k → k ≤ 1 / 5000 →
    (∀ N : ℕ, 0 < N →
      (∀ i : Fin N,
        ‖firstAxis k (midpoint N i)‖ = 1 ∧
        ‖secondAxis k (midpoint N i)‖ = 1 ∧
        IsCompact (firstBase k N i) ∧ IsCompact (secondBase k N i) ∧
        MeasurableSet (firstBase k N i) ∧ MeasurableSet (secondBase k N i) ∧
        Measure.euclideanHausdorffMeasure 2 (firstBase k N i) ≠ ⊤ ∧
        Measure.euclideanHausdorffMeasure 2 (secondBase k N i) ≠ ⊤ ∧
        (∀ z ∈ firstBase k N i,
          inner ℝ (firstAxis k (midpoint N i)) z = 0 ∧ ∑ j, z j = 1) ∧
        (∀ z ∈ secondBase k N i,
          inner ℝ (secondAxis k (midpoint N i)) z = 0 ∧ ∑ j, z j = 1)) ∧
      (∀ z ∈ barycentricSimplex,
        (∃ i : Fin N, z ∈ cylinder (firstAxis k (midpoint N i)) (firstBase k N i)) ∨
        (∃ i : Fin N, z ∈ cylinder (secondAxis k (midpoint N i)) (secondBase k N i)))) ∧
    (∀ δ : ℝ, 0 < δ → ∀ᶠ N in atTop, totalArea k N ≤ 2 * J k + δ) ∧
    Filter.limsup (totalArea k) atTop ≤ 2 * J k ∧
    (∀ᶠ N in atTop, 0 < N ∧ totalArea k N < Real.sqrt 2 / 4)

end RadialCoordinates.BarycentricFinite

end

end OAI
