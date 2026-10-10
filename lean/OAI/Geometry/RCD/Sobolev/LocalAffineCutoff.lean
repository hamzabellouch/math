import OAI.Geometry.RCD.Coordinates.CommonFrameRadialFits
import OAI.Geometry.RCD.Coordinates.BoundedSplittingCoordinates

namespace OAI

/-! # A common cutoff for local affine radial residuals -/

open Set MeasureTheory
open scoped ENNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

omit [BorelSpace X] [ProperSpace X] in
/-- Two local representatives of the constant one have identical restrictions. -/
theorem local_cutoff_restrict_eq (Ω : Set X) (η ζ : SobolevSpace μ hQ)
    (hη : SobolevSpace.toLp μ hQ η =ᵐ[μ.restrict Ω] fun _ => (1 : ℝ))
    (hζ : SobolevSpace.toLp μ hQ ζ =ᵐ[μ.restrict Ω] fun _ => (1 : ℝ)) :
    SobolevSpace.restrictLp μ hQ Ω η = SobolevSpace.restrictLp μ hQ Ω ζ := by
  apply Lp.ext
  exact (SobolevSpace.restrictLp_coe μ hQ Ω η).trans
    (hη.trans (hζ.symm.trans (SobolevSpace.restrictLp_coe μ hQ Ω ζ).symm))

/-- Replacing the compact extension of an affine constant preserves both
the normalized value error and the local gradient energy of its residual. -/
theorem local_affine_cutoff_errors (Ω : Set X) (hfin : μ Ω ≠ ∞)
    (q η ζ : SobolevSpace μ hQ) (c : ℝ)
    (hη : SobolevSpace.toLp μ hQ η =ᵐ[μ.restrict Ω] fun _ => (1 : ℝ))
    (hζ : SobolevSpace.toLp μ hQ ζ =ᵐ[μ.restrict Ω] fun _ => (1 : ℝ)) :
    normalizeLocalL2 μ Ω hfin (SobolevSpace.restrictLp μ hQ Ω (q - c • η)) =
      normalizeLocalL2 μ Ω hfin (SobolevSpace.restrictLp μ hQ Ω (q - c • ζ)) ∧
    (∫ x in Ω, localGamma μ hQ (q - c • η) (q - c • η) x ∂μ) =
      ∫ x in Ω, localGamma μ hQ (q - c • ζ) (q - c • ζ) x ∂μ := by
  have hr : SobolevSpace.restrictLp μ hQ Ω (q - c • η) =
      SobolevSpace.restrictLp μ hQ Ω (q - c • ζ) := by
    simp only [map_sub, map_smul, local_cutoff_restrict_eq μ hQ Ω η ζ hη hζ]
  refine ⟨congrArg (normalizeLocalL2 μ Ω hfin) hr, ?_⟩
  have heq : SobolevSpace.toLp μ hQ (q - c • η) =ᵐ[μ.restrict Ω]
      SobolevSpace.toLp μ hQ (q - c • ζ) := by
    apply (SobolevSpace.restrictLp_coe μ hQ Ω (q - c • η)).symm.trans
    rw [hr]
    exact SobolevSpace.restrictLp_coe μ hQ Ω (q - c • ζ)
  exact integral_congr_ae (localGamma_pair_congr_ae μ hQ heq heq)

end RegularPointCoordinates

end

end OAI
