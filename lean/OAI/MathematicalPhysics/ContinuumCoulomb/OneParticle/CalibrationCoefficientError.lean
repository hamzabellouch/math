import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.CalibrationSquareError

namespace OAI

/-! A numerical calibration residual controls the actual superexchange
coefficient directly. No inverse-function or derivative lower bound is used. -/

noncomputable section
namespace ContinuumCoulomb

theorem calibrated_coefficient_error {a K gap τ ε : ℝ}
    (hK : 0 ≤ K) (hgap : 0 < gap) (hτ : 0 ≤ τ)
    (hres : |a - τ * Real.sqrt (K * gap)| ≤ ε) :
    |a ^ 2 / gap - τ ^ 2 * K| ≤
      ε * (2 * τ * Real.sqrt (K * gap) + ε) / gap := by
  let b := τ * Real.sqrt (K * gap)
  have hb : 0 ≤ b := mul_nonneg hτ (Real.sqrt_nonneg _)
  have he : 0 ≤ ε := (abs_nonneg _).trans hres
  have hb2 : b ^ 2 = τ ^ 2 * K * gap := by
    dsimp only [b]
    rw [mul_pow, Real.sq_sqrt (mul_nonneg hK hgap.le)]
    ring
  have ha : |a| ≤ b + ε := by
    calc
      _ = |(a - b) + b| := by congr 1; ring
      _ ≤ |a - b| + |b| := abs_add_le _ _
      _ ≤ ε + b := add_le_add hres (le_of_eq (abs_of_nonneg hb))
      _ = _ := by ring
  have hsum : |a + b| ≤ 2 * b + ε :=
    (abs_add_le _ _).trans (by rw [abs_of_nonneg hb]; linarith)
  have hsq : |a ^ 2 - b ^ 2| ≤ ε * (2 * b + ε) := by
    rw [show a ^ 2 - b ^ 2 = (a - b) * (a + b) by ring, abs_mul]
    exact mul_le_mul hres hsum (abs_nonneg _) he
  have hid : a ^ 2 / gap - τ ^ 2 * K = (a ^ 2 - b ^ 2) / gap := by
    rw [hb2]
    field_simp [hgap.ne']
  rw [hid, abs_div, abs_of_pos hgap]
  simpa only [b, mul_assoc] using div_le_div_of_nonneg_right hsq hgap.le

end ContinuumCoulomb

end

end OAI
