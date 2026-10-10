import OAI.MathematicalPhysics.Boltzmann.Compactness.RenormalizedIntegrability

namespace OAI

/-! # Entropy controls the positive gain excess over a large multiple of loss -/
noncomputable section
open scoped ENNReal
namespace BoltzmannNonuniqueness

theorem weighted_gain_le_scaled_loss_add_extendedProduction {A B k θ R : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hk : 0 ≤ k) (hθ : 0 ≤ θ) (hθone : θ ≤ 1) (hR : 2 ≤ R) :
    ENNReal.ofReal (k*θ*A) ≤ ENNReal.ofReal R*ENNReal.ofReal (k*θ*B) +
      ENNReal.ofReal (2/Real.log R)*ENNReal.ofReal k*extendedEntropyProduction A B := by
  have hg := gain_le_scaled_loss_add_extendedProduction hA hB hR
  have hθ' : ENNReal.ofReal θ ≤ 1 := by simpa using ENNReal.ofReal_le_ofReal hθone
  simp only [ENNReal.ofReal_mul (mul_nonneg hk hθ),ENNReal.ofReal_mul hk]
  calc
    ENNReal.ofReal k*ENNReal.ofReal θ*ENNReal.ofReal A ≤
        ENNReal.ofReal k*ENNReal.ofReal θ*(ENNReal.ofReal R*ENNReal.ofReal B+
          ENNReal.ofReal (2/Real.log R)*extendedEntropyProduction A B) := by gcongr
    _ = ENNReal.ofReal R*(ENNReal.ofReal k*ENNReal.ofReal θ*ENNReal.ofReal B)+
        ENNReal.ofReal (2/Real.log R)*ENNReal.ofReal k*ENNReal.ofReal θ*extendedEntropyProduction A B := by ring
    _ ≤ _ := by
      apply add_le_add le_rfl
      calc
        _ = (ENNReal.ofReal (2/Real.log R)*ENNReal.ofReal k*extendedEntropyProduction A B)*ENNReal.ofReal θ := by ring
        _ ≤ (ENNReal.ofReal (2/Real.log R)*ENNReal.ofReal k*extendedEntropyProduction A B)*1 := by gcongr
        _ = _ := mul_one _

theorem gain_excess_le_extendedProduction {A B k θ R : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hk : 0 ≤ k) (hθ : 0 ≤ θ) (hθone : θ ≤ 1) (hR : 2 ≤ R) :
    ENNReal.ofReal (k*θ*A-R*(k*θ*B)) ≤
      ENNReal.ofReal (2/Real.log R)*ENNReal.ofReal k*extendedEntropyProduction A B := by
  rw [ENNReal.ofReal_sub _ (mul_nonneg (by linarith) (mul_nonneg (mul_nonneg hk hθ) hB)),
    ENNReal.ofReal_mul (by linarith : 0 ≤ R)]
  apply tsub_le_iff_right.mpr
  simpa only [add_comm] using weighted_gain_le_scaled_loss_add_extendedProduction hA hB hk hθ hθone hR

end BoltzmannNonuniqueness

end

end OAI
