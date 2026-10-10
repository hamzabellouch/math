import OAI.NumberTheory.Ostmann.QuadraticCenter.QuadraticArrayGrid
import OAI.NumberTheory.Ostmann.QuadraticCenter.QuadraticSumBound

namespace OAI

noncomputable section
namespace Ostmann.QuadraticCenter
open scoped BigOperators

theorem quadraticScale_normalization {R q : ℝ} (hR : 0 < R) (hq : 0 < q) :
    (Real.sqrt (R / q))⁻¹ = Real.sqrt q * (Real.sqrt R)⁻¹ := by
  rw [Real.sqrt_div hR.le]
  field_simp

theorem quadraticScale_argument {R q : ℝ} (hR : 0 < R) (hq : 0 < q) (w : ℝ) :
    (w / Real.sqrt (R / q)) ^ 2 = q * w ^ 2 / R := by
  rw [div_pow, Real.sq_sqrt (div_nonneg hR.le hq.le)]
  field_simp

theorem normalizedSmoothQuadraticSum_eq_grid_sum {P W : ℕ} {R q : ℝ}
    (hR : 0 < R) (hq : 0 < q) (hW : ⌊Real.sqrt (R / q)⌋₊ ≤ W)
    (a : ℕ → ℂ) (h θ : ℝ) :
    normalizedSmoothQuadraticSum P (Real.sqrt (R / q)) a ((h + θ) * q) =
      (Real.sqrt q : ℂ) * smoothQuadraticSum
        ((Finset.Ioc 0 W).filter (fun w => P ∣ w)) a (fun w => q * (w : ℝ) ^ 2) h θ R := by
  rw [normalizedSmoothQuadraticSum_truncation (Real.sqrt_pos.mpr (div_pos hR hq)) hW]
  unfold smoothQuadraticSum
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro w hw
  rw [quadraticScale_argument hR hq, quadraticScale_normalization hR hq]
  unfold quadraticAtom
  push_cast
  have he : (h + θ) * q * (w : ℝ) ^ 2 = (h + θ) * (q * (w : ℝ) ^ 2) := by ring
  rw [he]
  ring

theorem smoothQuadraticSum_norm_le {ω : Type*} (I : Finset ω)
    (a : ω → ℂ) (κ : ω → ℝ) (h θ : ℝ) {R A : ℝ} (hR : 1 ≤ R)
    (ha : ∀ w ∈ I, ‖a w‖ ≤ A) :
    ‖smoothQuadraticSum I a κ h θ R‖ ≤ I.card * A * cutoffFourierBound := by
  unfold smoothQuadraticSum
  calc
    _ ≤ ∑ w ∈ I, ‖quadraticAtom (a w) (κ w) h θ R‖ := norm_sum_le _ _
    _ ≤ ∑ _w ∈ I, A * cutoffFourierBound := by
      apply Finset.sum_le_sum
      intro w hw
      exact (norm_quadraticAtom hR (a w) (κ w) h θ).trans
        (mul_le_mul_of_nonneg_right (ha w hw) cutoffFourierBound_pos.le)
    _ = _ := by simp; ring

end Ostmann.QuadraticCenter

end

end OAI
