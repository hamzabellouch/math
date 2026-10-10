import OAI.Geometry.RCD.Coordinates.AffineFitDifference

namespace OAI

/-! # Size and centering of actual affine projections -/

open Set MeasureTheory
open scoped InnerProductSpace ENNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

theorem normalized_affineProjection_norm_le {n : ℕ}
    (u : Fin n → SobolevSpace μ hQ) (s : Set X) (hs : μ s ≠ ∞)
    (f : Lp ℝ 2 (μ.restrict s)) :
    ‖normalizeLocalL2 μ s hs (affineProjection μ hQ u s hs f)‖ ≤
      ‖normalizeLocalL2 μ s hs f‖ := by
  unfold normalizeLocalL2
  rw [← map_smul]
  exact affineProjection_norm_le μ hQ u s hs _

/-- Any coefficients of the actual fit inherit the harmonic evaluation
bound and the contraction of orthogonal projection. -/
theorem affineFit_center_bound {n : ℕ} (u : Fin n → SobolevSpace μ hQ)
    (s : Set X) (hs : μ s ≠ ∞) (v : Euclidean n) {C : ℝ} (hC : 0 ≤ C)
    (heval : ∀ c a, |c + ⟪v, a⟫_ℝ| ≤
      C * ‖normalizeLocalL2 μ s hs (affineCoordinateMap μ hQ u s hs (c, a))‖)
    (f : Lp ℝ 2 (μ.restrict s)) (c : ℝ) (a : Euclidean n)
    (hfit : affineProjection μ hQ u s hs f = affineCoordinateMap μ hQ u s hs (c, a)) :
    |c + ⟪v, a⟫_ℝ| ≤ C * ‖normalizeLocalL2 μ s hs f‖ := by
  have h := heval c a
  rw [← hfit] at h
  exact h.trans (mul_le_mul_of_nonneg_left
    (normalized_affineProjection_norm_le μ hQ u s hs f) hC)

omit [MetricSpace X] in
theorem normalized_constant_norm (s : Set X) (hs : μ s ≠ ∞) (hs0 : μ s ≠ 0) (c : ℝ) :
    ‖normalizeLocalL2 μ s hs (c • restrictedOne μ s hs)‖ = |c| := by
  have hn : ‖restrictedOne μ s hs‖ ≠ 0 := by
    rw [restrictedOne_norm]
    exact ne_of_gt (Real.sqrt_pos.mpr (ENNReal.toReal_pos hs0 hs))
  simp only [normalizeLocalL2, norm_smul, Real.norm_eq_abs, abs_inv, abs_norm]
  field_simp

/-- Subtracting the center value from a fit costs exactly its absolute
value in normalized L². -/
theorem centered_affineFit_error {n : ℕ} (u : Fin n → SobolevSpace μ hQ)
    (s : Set X) (hs : μ s ≠ ∞) (hs0 : μ s ≠ 0) (v : Euclidean n)
    (f : Lp ℝ 2 (μ.restrict s)) (c : ℝ) (a : Euclidean n)
    (hfit : affineProjection μ hQ u s hs f = affineCoordinateMap μ hQ u s hs (c, a)) :
    ‖normalizeLocalL2 μ s hs
      (f - affineCoordinateMap μ hQ u s hs (-⟪v, a⟫_ℝ, a))‖ ≤
      ‖normalizeLocalL2 μ s hs (affineResidual μ hQ u s hs f)‖ + |c + ⟪v, a⟫_ℝ| := by
  have he : f - affineCoordinateMap μ hQ u s hs (-⟪v, a⟫_ℝ, a) =
      affineResidual μ hQ u s hs f + (c + ⟪v, a⟫_ℝ) • restrictedOne μ s hs := by
    change f - affineCoordinateMap μ hQ u s hs (-⟪v, a⟫_ℝ, a) =
      (f - affineProjection μ hQ u s hs f) + _
    rw [hfit, affineCoordinateMap_apply, affineCoordinateMap_apply]
    module
  rw [he, normalizeLocalL2, smul_add]
  have hb := norm_add_le
    (normalizeLocalL2 μ s hs (affineResidual μ hQ u s hs f))
    (normalizeLocalL2 μ s hs ((c + ⟪v, a⟫_ℝ) • restrictedOne μ s hs))
  rwa [normalized_constant_norm μ s hs hs0] at hb

end RegularPointCoordinates

end

end OAI
