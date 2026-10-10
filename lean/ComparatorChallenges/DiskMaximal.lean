import Mathlib

namespace OAI

open MeasureTheory Set
open scoped ENNReal NNReal Topology ContDiff

noncomputable section
namespace CenteredDiskEndpoint

/-- The Euclidean plane, not the product space with its max norm. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- Absolute disk average, retaining possible infinite values. -/
def absoluteDiskAverage (f : Plane → ℝ) (x : Plane) (r : ℝ) : ℝ≥0∞ :=
  (∫⁻ y in Metric.ball x r, ENNReal.ofReal |f y|) /
    ENNReal.ofReal (Real.pi * r ^ 2)

/-- The actual centered disk maximal function, over every positive real radius. -/
def maximal (f : Plane → ℝ) (x : Plane) : ℝ≥0∞ :=
  ⨆ (r : ℝ) (_ : 0 < r), absoluteDiskAverage f x r

/-- Real representative; the endpoint also asserts that `maximal f` is finite a.e. -/
def maximalReal (f : Plane → ℝ) (x : Plane) : ℝ := (maximal f x).toReal

/-- The i-th coordinate derivative of a smooth test function. -/
def testPartial (φ : Plane → ℝ) (i : Fin 2) (x : Plane) : ℝ :=
  fderiv ℝ φ x (EuclideanSpace.single i 1)

/-- Distributional first derivatives represented by a vector-valued function. -/
def HasWeakGradient (f : Plane → ℝ) (g : Plane → Plane) : Prop :=
  ∀ (φ : Plane → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ →
    ∀ i : Fin 2, (∫ x, f x * testPartial φ i x) = -∫ x, g x i * φ x

/-- Local W^(1,1), expressed using the same distributional gradient convention. -/
def InW11Loc (f : Plane → ℝ) : Prop :=
  LocallyIntegrable f ∧
    ∃ g : Plane → Plane, LocallyIntegrable g ∧ HasWeakGradient f g

/-- The gradient L1 norm in Euclidean norm. -/
def gradientNorm (g : Plane → Plane) : ℝ := ∫ x, ‖g x‖

/-- Exact endpoint, including finiteness before passing to the real representative.
Quantifying the input gradient makes the norm bound independent of a choice of
representative of its weak derivatives. -/
def EndpointStatement : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ (f : Plane → ℝ) (g : Plane → Plane),
      Integrable f → Integrable g → HasWeakGradient f g →
      (∀ᵐ x, maximal f x ≠ ⊤) ∧
      LocallyIntegrable (maximalReal f) ∧
      InW11Loc (maximalReal f) ∧
      ∃ G : Plane → Plane, Integrable G ∧
        HasWeakGradient (maximalReal f) G ∧ gradientNorm G ≤ C * gradientNorm g

theorem main_endpoint : EndpointStatement := by
  sorry

end CenteredDiskEndpoint

end

end OAI
