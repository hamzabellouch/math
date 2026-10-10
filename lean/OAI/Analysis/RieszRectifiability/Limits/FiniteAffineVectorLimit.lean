import Mathlib
import OAI.Analysis.RieszRectifiability.Flatness.BoundedPlaneBoxes
import OAI.Analysis.RieszRectifiability.Limits.LipschitzSquareWeakLimit
import OAI.Analysis.RieszRectifiability.Flatness.AssembledAffineHeight
import OAI.Analysis.RieszRectifiability.Kernel.EuclideanCoordinateMoments

namespace OAI

/-!
# Vector-valued affine strong limits

Coordinatewise affine limits assemble into one ambient affine map. On bounded projection
regions, coordinate square integrability and convergence combine through the Euclidean norm
identity to give vector-valued strong convergence.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Filter Topology WithLp
open scoped NNReal

theorem exists_vector_affine_strong_limit_of_coordinates {n q d : ℕ}
    (a z : Ambient d) (L : Ambient n →ₗᵢ[ℝ] Ambient d)
    (π : Ambient d → Fin n → ℝ) (K Q : ℝ≥0) (hπ : LipschitzWith Q π)
    (σ : ℕ → Measure (Ambient d)) [∀ j, IsFiniteMeasureOnCompacts (σ j)]
    (w : Fin q → ℕ → Ambient d → ℝ)
    (hw : ∀ i H j, MemLp (w i j) 2 ((σ j).restrict (boundedProjectionRegion π z K H)))
    (c : Fin q → ℝ) (M : Fin q → Ambient n →L[ℝ] ℝ)
    (hstrong : ∀ i H, Tendsto (fun j => ∫ x,
      (w i j x - ambientAffineHeight a L (c i) (M i) x) ^ 2
      ∂(σ j).restrict (boundedProjectionRegion π z K H)) atTop (𝓝 0)) :
    ∃ b : Ambient q, ∃ B : Ambient d →L[ℝ] Ambient q, ∀ H,
      (∀ j, Integrable (fun x => ‖toLp 2 (fun i => w i j x) - (b + B x)‖ ^ 2)
        ((σ j).restrict (boundedProjectionRegion π z K H))) ∧
      Tendsto (fun j => ∫ x, ‖toLp 2 (fun i => w i j x) - (b + B x)‖ ^ 2
        ∂(σ j).restrict (boundedProjectionRegion π z K H)) atTop (𝓝 0) := by
  obtain ⟨b, B, hcoord⟩ := exists_ambient_vector_affine a L c M
  refine ⟨b, B, ?_⟩
  intro H
  let μ := fun j => (σ j).restrict (boundedProjectionRegion π z K H)
  let r := fun j x => (toLp 2 (fun i => w i j x) : Ambient q) - (b + B x)
  have hr : ∀ j x i, r j x i = w i j x - ambientAffineHeight a L (c i) (M i) x := by
    intro j x i
    change w i j x - (b + B x) i = _
    rw [hcoord]
  have hi : ∀ j i, Integrable (fun x => (r j x i) ^ 2) (μ j) := by
    intro j i
    let := boundedProjectionRegion_finite (σ j) π z K H
    have hball : ∀ᵐ x ∂μ j, x ∈ ball z (planeBoxOuterRadius K H) := by
      filter_upwards [ae_restrict_mem (μ := σ j)
        (boundedProjectionRegion_isOpen π hπ.continuous z K H).measurableSet] with x hx
      exact hx.2
    have hv := lipschitz_memLp_of_ae_ball (μ j) z (planeBoxOuterRadius K H) hball
      (ambientAffineHeight a L (c i) (M i)) _ (ambientAffineHeight_lipschitz a L (c i) (M i))
    simpa only [hr] using! ((hw i H j).sub hv).integrable_sq
  refine ⟨fun j => integrable_euclidean_norm_sq_of_coordinates (μ j) (r j) (hi j), ?_⟩
  apply euclidean_norm_sq_tendsto_zero_of_coordinates μ r hi
  intro i
  simpa only [hr] using! hstrong i H

end

end RieszRectifiability

end OAI
