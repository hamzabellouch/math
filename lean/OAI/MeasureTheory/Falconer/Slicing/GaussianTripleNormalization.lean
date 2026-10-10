import OAI.MeasureTheory.Falconer.Slicing.GaussianTripleBand

namespace OAI

/-! # Exact cancellation of the three direction-slice normalization factors -/

namespace Falconer
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {d h : ℕ}

theorem gaussian_cubed_band_normalization {r C : ℝ} (hr : 0 < r) :
    (ENNReal.ofReal (r^(-(h:ℝ))))^3*ENNReal.ofReal ((C*r^3)^h) =
      ENNReal.ofReal (C^h) := by
  rw [← ENNReal.ofReal_pow (by positivity),← ENNReal.ofReal_mul (by positivity),
    Real.rpow_neg hr.le,Real.rpow_natCast,mul_pow]
  congr 1
  have he : (r^3)^h = (r^h)^3 := by
    simp only [← pow_mul]
    congr 1
    omega
  rw [he]
  field_simp

theorem gaussianRows_three_vector_normalized (v : Fin 3 → Space d)
    (hv : 0 < (Matrix.gram ℝ v).det) {r : ℝ} (hr : 0 < r) :
    (ENNReal.ofReal (r^(-(h:ℝ))))^3 *
      gaussianRows d h {A | ∀ i, ∀ j, |inner ℝ (v j) (A i)| ≤ r} ≤
    ENNReal.ofReal ((8*gaussianVolumeNormalization 3*(Real.sqrt (Matrix.gram ℝ v).det)⁻¹)^h) := by
  apply (mul_le_mul' le_rfl (gaussianRows_three_vector_band v hv hr.le)).trans_eq
  have he : gaussianVolumeNormalization 3*(Real.sqrt (Matrix.gram ℝ v).det)⁻¹*(2*r)^3 =
      (8*gaussianVolumeNormalization 3*(Real.sqrt (Matrix.gram ℝ v).det)⁻¹)*r^3 := by ring
  rw [he,gaussian_cubed_band_normalization hr]

end Falconer

end OAI
