import Mathlib

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped RealInnerProductSpace

namespace PettyProjection

abbrev Space (n : ℕ) := EuclideanSpace ℝ (Fin n)

def IsConvexBody {n : ℕ} (K : Set (Space n)) : Prop :=
  IsCompact K ∧ Convex ℝ K ∧ (interior K).Nonempty

def unitBall (n : ℕ) : Set (Space n) := Metric.closedBall 0 1

def kappa (n : ℕ) : ℝ := volume.real (unitBall n)

def perpendicular {n : ℕ} (u : Space n) : Submodule ℝ (Space n) :=
  (Submodule.span ℝ {u})ᗮ

/-- Volume in the induced Euclidean structure on the orthogonal hyperplane. -/
def shadowVolume {n : ℕ} (K : Set (Space n)) (u : Space n) : ℝ :=
  (volume : Measure (perpendicular u)).real
    ((perpendicular u).orthogonalProjectionOnto '' K)

/-- The body with support function equal to the volumes of orthogonal shadows,
expressed as its defining intersection of supporting half-spaces. -/
def projectionBody {n : ℕ} (K : Set (Space n)) : Set (Space n) :=
  {x | ∀ u : Space n, ‖u‖ = 1 → ⟪u, x⟫ ≤ shadowVolume K u}

def projectionRatio {n : ℕ} (K : Set (Space n)) : ℝ :=
  volume.real (projectionBody K) / volume.real K ^ (n - 1)

def pettyConstant (n : ℕ) : ℝ :=
  kappa (n - 1) ^ n * kappa n ^ (2 - (n : ℤ))

def IsEllipsoid {n : ℕ} (K : Set (Space n)) : Prop :=
  ∃ (a : Space n) (T : Space n ≃ₗ[ℝ] Space n),
    K = (fun x => a + T x) '' unitBall n

/-- The exact unrestricted inequality and its global equality characterization.
-/
theorem petty_projection_volume (n : ℕ) (hn : 4 ≤ n)
    (K : Set (Space n)) (hK : IsConvexBody K) :
    pettyConstant n ≤ projectionRatio K ∧
      (projectionRatio K = pettyConstant n ↔ IsEllipsoid K) := by
  sorry

end PettyProjection
end

end OAI
