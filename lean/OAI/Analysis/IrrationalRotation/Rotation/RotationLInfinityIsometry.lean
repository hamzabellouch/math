import OAI.Analysis.IrrationalRotation.Rotation.RotationLInfinity
import OAI.Analysis.IrrationalRotation.Rotation.RotationMeasurableLaws

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace Invariant233.Rotation

theorem norm_lInfinityRepresentation (θ : ℝ) (a : Lp ℂ ∞ circleMeasure) :
    ‖lInfinityRepresentation θ a‖ = ‖a‖ := by
  apply le_antisymm (norm_lInfinityRepresentation_le θ a)
  have h := lpNorm_le_norm_of_orbit_representation θ (Lp.memLp a)
    (lInfinityRepresentation θ a) (lInfinityRepresentation_mem_algebra θ a)
    (lInfinityRepresentation_coordinate_ae θ a)
  rwa [← toReal_eLpNorm, ← Lp.norm_def] at h

def lInfinityRepresentationLI (θ : ℝ) :
    Lp ℂ ∞ circleMeasure →ₗᵢ[ℂ] (Hilbert →L[ℂ] Hilbert) where
  toLinearMap := (lInfinityRepresentationCLM θ).toLinearMap
  norm_map' := norm_lInfinityRepresentation θ

@[simp]
theorem lInfinityRepresentationLI_apply (θ : ℝ) (a : Lp ℂ ∞ circleMeasure) :
    lInfinityRepresentationLI θ a = lInfinityRepresentation θ a := rfl

theorem dist_lInfinityRepresentation (θ : ℝ) (a b : Lp ℂ ∞ circleMeasure) :
    dist (lInfinityRepresentation θ a) (lInfinityRepresentation θ b) = dist a b :=
  (lInfinityRepresentationLI θ).isometry.dist_eq a b

theorem isClosed_range_lInfinityRepresentation (θ : ℝ) :
    IsClosed (Set.range (lInfinityRepresentation θ)) :=
  (lInfinityRepresentationLI θ).isometry.isClosedEmbedding.isClosed_range

end Invariant233.Rotation

end

end OAI
