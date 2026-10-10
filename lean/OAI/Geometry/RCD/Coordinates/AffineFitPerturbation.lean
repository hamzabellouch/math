import OAI.Geometry.RCD.Harmonic.LocalL2Restriction
import OAI.Geometry.RCD.Harmonic.HomogeneousAffineImprovement

namespace OAI

/-! # Stability of the actual least-squares fit under harmonic correction -/

open Set MeasureTheory
open scoped ENNReal InnerProductSpace

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

theorem normalized_affineResidual_norm_le {n : ℕ}
    (u : Fin n → SobolevSpace μ hQ) (s : Set X) (hs : μ s ≠ ∞)
    (f : Lp ℝ 2 (μ.restrict s)) :
    ‖normalizeLocalL2 μ s hs (affineResidual μ hQ u s hs f)‖ ≤
      ‖normalizeLocalL2 μ s hs f‖ := by
  unfold normalizeLocalL2
  rw [← map_smul]
  exact affineResidual_norm_le μ hQ u s hs _

theorem normalized_affineResidual_perturbation {n : ℕ}
    (u : Fin n → SobolevSpace μ hQ) (s : Set X) (hs : μ s ≠ ∞)
    (f g : Lp ℝ 2 (μ.restrict s)) :
    ‖normalizeLocalL2 μ s hs (affineResidual μ hQ u s hs f)‖ ≤
      ‖normalizeLocalL2 μ s hs (f - g)‖ +
        ‖normalizeLocalL2 μ s hs (affineResidual μ hQ u s hs g)‖ := by
  have he : affineResidual μ hQ u s hs f =
      affineResidual μ hQ u s hs (f - g) + affineResidual μ hQ u s hs g := by
    rw [map_sub]
    abel
  rw [he, normalizeLocalL2, smul_add]
  exact (norm_add_le _ _).trans (add_le_add
    (normalized_affineResidual_norm_le μ hQ u s hs (f - g)) le_rfl)

theorem affineResidual_sub_affine {n : ℕ} (u : Fin n → SobolevSpace μ hQ)
    (s : Set X) (hs : μ s ≠ ∞) (f : Lp ℝ 2 (μ.restrict s))
    (c : ℝ) (v : Euclidean n) :
    affineResidual μ hQ u s hs (f - affineCoordinateMap μ hQ u s hs (c, v)) =
      affineResidual μ hQ u s hs f := by
  rw [map_sub]
  exact sub_eq_self.mpr (affineResidual_eq_zero_of_mem μ hQ u s hs _ ⟨(c, v), rfl⟩)

/-- Every actual outer affine projection has a Sobolev representative
which is harmonic wherever the columns and local constant are harmonic. -/
theorem affineProjection_harmonic_representative {n : ℕ}
    (u : Fin n → SobolevSpace μ hQ) (s : Set X) (hs : μ s ≠ ∞)
    (hu : ∀ i, IsSobolevHarmonicOn μ hQ s (u i))
    (η : SobolevSpace μ hQ) (hη : IsSobolevHarmonicOn μ hQ s η)
    (hηone : SobolevSpace.restrictLp μ hQ s η = restrictedOne μ s hs)
    (f : Lp ℝ 2 (μ.restrict s)) :
    ∃ (F : SobolevSpace μ hQ) (c : ℝ) (v : Euclidean n),
      F = c • η + sobolevColumnMap μ hQ u v ∧
      IsSobolevHarmonicOn μ hQ s F ∧
      SobolevSpace.restrictLp μ hQ s F = affineProjection μ hQ u s hs f := by
  obtain ⟨c, v, hcv⟩ := affineProjection_has_coefficients μ hQ u s hs f
  refine ⟨c • η + sobolevColumnMap μ hQ u v, c, v, rfl, ?_, ?_⟩
  · exact (hη.smul μ hQ c).add μ hQ (IsSobolevHarmonicOn.linearCombination μ hQ hu v)
  · rw [map_add, map_smul, hηone]
    exact hcv.symm

end RegularPointCoordinates

end

end OAI
