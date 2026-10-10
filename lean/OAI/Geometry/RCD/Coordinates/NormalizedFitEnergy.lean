import OAI.Geometry.RCD.Coordinates.NormalizedLocalL2

namespace OAI

/-! # Converting the normalized radial fit to its integral budget -/

open Set MeasureTheory
open scoped ENNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MeasurableSpace X] (μ : Measure X)

theorem norm_sq_le_of_normalized_fit (s : Set X) (hs : μ s ≠ ∞) (hs0 : μ s ≠ 0)
    (f : Lp ℝ 2 (μ.restrict s)) {A : ℝ} (hA : 0 ≤ A)
    (hfit : ‖normalizeLocalL2 μ s hs f‖ ≤ A) :
    ‖f‖ ^ 2 ≤ μ.real s * A ^ 2 := by
  have hmass : 0 < μ.real s := ENNReal.toReal_pos hs0 hs
  have he := normalizeLocalL2_norm_sq μ s hs f
  rw [← l2_norm_sq_eq_integral μ s f] at he
  have hb := (sq_le_sq₀ (norm_nonneg _) hA).mpr hfit
  rw [he] at hb
  calc
    _ = μ.real s * ((μ.real s)⁻¹ * ‖f‖ ^ 2) := by field_simp
    _ ≤ μ.real s * A ^ 2 := mul_le_mul_of_nonneg_left hb hmass.le

end RegularPointCoordinates

end

end OAI
