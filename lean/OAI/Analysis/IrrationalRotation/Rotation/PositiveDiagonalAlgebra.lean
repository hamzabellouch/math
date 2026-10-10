import OAI.Analysis.IrrationalRotation.Model.OperatorProperties
import OAI.Analysis.IrrationalRotation.Rotation.PositiveDiagonalRepresentatives

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped ENNReal InnerProductSpace

namespace Invariant233.PositiveDiagonalModel

variable {Y : Type*} [MeasurableSpace Y] {μ : Measure Y}

theorem positive_diagonal_in_algebra
    [IsProbabilityMeasure μ] (σ : Y ≃ᵐ Y) (hσ : Ergodic σ μ)
    (M : VonNeumannAlgebra (Space μ))
    (_htrace : IsFaithfulTracialVector M (Lp.const 2 μ e0))
    (hfields : ∀ A : Space μ →L[ℂ] Space μ, A ∈ M →
      ∃ a : Y → Fiber →L[ℂ] Fiber,
        (∀ y, ‖a y‖ ≤ ‖A‖) ∧
        (∀ v, StronglyMeasurable fun y => a y v) ∧
        (∀ ξ : Space μ, A ξ =ᵐ[μ] fun y => a y (ξ y)) ∧
        (∀ᵐ y ∂μ, a y * fiberShift = fiberShift * a (σ y)))
    (f : Lp ℝ ∞ μ) (hpositive : ∀ᵐ y ∂μ, 0 < f y)
    (P : Space μ →L[ℂ] Space μ) (hPm : P ∈ M) (hP : IsStarProjection P)
    (hinv : (1 - P) * lpOrbitWeightedShift σ f * P = 0)
    (htrace0 : 0 < diagonalState P) (htrace1 : diagonalState P < 1) :
    ∃ p : Y → Fiber →L[ℂ] Fiber,
      (∀ y, ‖p y‖ ≤ ‖P‖) ∧
      (∀ v, StronglyMeasurable fun y => p y v) ∧
      (∀ ξ : Space μ, P ξ =ᵐ[μ] fun y => p y (ξ y)) ∧
      (∀ᵐ y ∂μ, IsStarProjection (p y)) ∧
      (∀ᵐ y ∂μ, p y * fiberShift = fiberShift * p (σ y)) ∧
      diagonalState P = ∫ y, (inner ℂ e0 (p y e0)).re ∂μ ∧
      (∀ᵐ y ∂μ, 0 < (inner ℂ e0 (p y e0)).re ∧
        (inner ℂ e0 (p y e0)).re < 1) := by
  obtain ⟨p, hbound, hm, hrep, hcov⟩ := hfields P hPm
  have hgpos : ∀ᵐ y ∂μ, 0 < boundedRepresentative f y := by
    filter_upwards [boundedRepresentative_ae_eq f, hpositive] with y hy hpos
    rw [hy]
    exact hpos
  refine ⟨p, hbound, hm, hrep, ?_, hcov, ?_, ?_⟩
  · exact DirectIntegral.ae_isStarProjection_of_representation
      (HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ Fiber)) P p
      ‖P‖ (norm_nonneg P) hbound hm hrep hP
  · exact DirectIntegral.real_constant_vector_state_eq_integral P p hrep e0
  · exact positive_diagonal_orbit σ hσ (boundedRepresentative f)
      (boundedRepresentative_measurable f) ‖f‖ (norm_nonneg f)
      (boundedRepresentative_bound f) hgpos P p hbound hm hrep hP hcov
      hinv htrace0 htrace1

end Invariant233.PositiveDiagonalModel

end

end OAI
