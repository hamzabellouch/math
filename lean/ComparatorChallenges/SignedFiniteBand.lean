import Mathlib

namespace OAI

noncomputable section

namespace SignedDisk

open MeasureTheory Set
open scoped ENNReal NNReal Topology ContDiff

namespace CenteredDiskEndpoint

/-- The Euclidean plane, with its Euclidean norm. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

def diskAverage (f : Plane → ℝ) (x : Plane) (r : ℝ) : ℝ :=
  (∫ y in Metric.ball x r, f y) / (Real.pi * r ^ 2)

/-- The i-th coordinate derivative of a smooth test function. -/
def testPartial (φ : Plane → ℝ) (i : Fin 2) (x : Plane) : ℝ :=
  fderiv ℝ φ x (EuclideanSpace.single i 1)

/-- Distributional first derivatives represented by a vector-valued function. -/
def HasWeakGradient (f : Plane → ℝ) (g : Plane → Plane) : Prop :=
  ∀ (φ : Plane → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ →
    ∀ i : Fin 2, (∫ x, f x * testPartial φ i x) = -∫ x, g x i * φ x

/-- The gradient L1 norm in Euclidean norm. -/
def gradientNorm (g : Plane → Plane) : ℝ := ∫ x, ‖g x‖

/-- Signed envelope over all real radii in the closed band, including its endpoints. -/
def signedBand (f : Plane → ℝ) (a b : ℝ) (x : Plane) : ℝ :=
  sSup ((fun r => diskAverage f x r) '' Icc a b)

def SignedFiniteBandStatement : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ (f : Plane → ℝ), ContDiff ℝ ∞ f → HasCompactSupport f →
    ∀ (a : ℝ), 0 < a → ∀ m : ℕ,
      LocallyIntegrable (signedBand f a ((2 : ℝ)^m * a)) ∧
      ∃ G : Plane → Plane, Integrable G ∧
        HasWeakGradient (signedBand f a ((2 : ℝ)^m * a)) G ∧
        gradientNorm G ≤ C * gradientNorm (gradient f)

theorem main_signed_finite_band : SignedFiniteBandStatement := by
  sorry

end CenteredDiskEndpoint

end SignedDisk

end

end OAI
