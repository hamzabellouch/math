import OAI.Geometry.RCD.Harmonic.AffineProjection

namespace OAI

/-! # Least-squares affine fits are independent of coordinate normalization -/

open Set MeasureTheory
open scoped InnerProductSpace ENNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

/-- An invertible linear coordinate change and a translation by constants
preserve the actual finite-dimensional affine subspace in local L². -/
theorem affineCoordinateSpace_eq_of_change {n : ℕ}
    (u u' : Fin n → SobolevSpace μ hQ) (s : Set X) (hfin : μ s ≠ ∞)
    (B : Euclidean n ≃L[ℝ] Euclidean n) (b : Euclidean n →L[ℝ] ℝ)
    (hchange : ∀ v, SobolevSpace.restrictLp μ hQ s (sobolevColumnMap μ hQ u' v) =
      SobolevSpace.restrictLp μ hQ s (sobolevColumnMap μ hQ u (B v)) +
        b v • restrictedOne μ s hfin) :
    affineCoordinateSpace μ hQ u' s hfin = affineCoordinateSpace μ hQ u s hfin := by
  ext f
  constructor
  · rintro ⟨⟨c, v⟩, rfl⟩
    refine ⟨(c + b v, B v), ?_⟩
    change (c + b v) • restrictedOne μ s hfin +
      SobolevSpace.restrictLp μ hQ s (sobolevColumnMap μ hQ u (B v)) =
      c • restrictedOne μ s hfin +
        SobolevSpace.restrictLp μ hQ s (sobolevColumnMap μ hQ u' v)
    rw [hchange, add_smul]
    abel
  · rintro ⟨⟨c, v⟩, rfl⟩
    refine ⟨(c - b (B.symm v), B.symm v), ?_⟩
    change (c - b (B.symm v)) • restrictedOne μ s hfin +
      SobolevSpace.restrictLp μ hQ s (sobolevColumnMap μ hQ u' (B.symm v)) =
      c • restrictedOne μ s hfin +
        SobolevSpace.restrictLp μ hQ s (sobolevColumnMap μ hQ u v)
    rw [hchange, B.apply_symm_apply, sub_smul]
    abel

/-- Consequently the least-squares projection itself is unchanged. -/
theorem affineProjection_eq_of_change {n : ℕ}
    (u u' : Fin n → SobolevSpace μ hQ) (s : Set X) (hfin : μ s ≠ ∞)
    (B : Euclidean n ≃L[ℝ] Euclidean n) (b : Euclidean n →L[ℝ] ℝ)
    (hchange : ∀ v, SobolevSpace.restrictLp μ hQ s (sobolevColumnMap μ hQ u' v) =
      SobolevSpace.restrictLp μ hQ s (sobolevColumnMap μ hQ u (B v)) +
        b v • restrictedOne μ s hfin) :
    affineProjection μ hQ u' s hfin = affineProjection μ hQ u s hfin := by
  simp only [affineProjection,
    affineCoordinateSpace_eq_of_change μ hQ u u' s hfin B b hchange]

theorem affineResidual_eq_of_change {n : ℕ}
    (u u' : Fin n → SobolevSpace μ hQ) (s : Set X) (hfin : μ s ≠ ∞)
    (B : Euclidean n ≃L[ℝ] Euclidean n) (b : Euclidean n →L[ℝ] ℝ)
    (hchange : ∀ v, SobolevSpace.restrictLp μ hQ s (sobolevColumnMap μ hQ u' v) =
      SobolevSpace.restrictLp μ hQ s (sobolevColumnMap μ hQ u (B v)) +
        b v • restrictedOne μ s hfin) :
    affineResidual μ hQ u' s hfin = affineResidual μ hQ u s hfin := by
  unfold affineResidual
  rw [affineProjection_eq_of_change μ hQ u u' s hfin B b hchange]

end RegularPointCoordinates

end

end OAI
