import OAI.MeasureTheory.Falconer.Recursion.FrostmanProfiles

namespace OAI

/-! # Absorbing the scalar shell's fixed cost and squared remainder

The shell width costs at most one power of R. Selecting the stationary
accuracy before scale therefore absorbs the square and the fixed constants.
-/

namespace Falconer

theorem eventual_scalar_shell_error_budget (T : ℝ) {C W : ℝ}
    (_hC : 0 ≤ C) (hW : 0 ≤ W) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ q ε : ℝ, q ≤ N → 0 ≤ ε →
      ε ≤ C*((2:ℝ)^N)^(-((T+2)/2)) →
      2*(2:ℝ)^q*ε^2*W ≤ ((2:ℝ)^N)^(-T) := by
  obtain ⟨N₀,hN₀⟩ := Regularization.fixed_constant_absorbed
    (by norm_num : (0:ℝ) < 1) (2*C^2*W)
  refine ⟨N₀,?_⟩
  intro N hN q ε hq hε hbound
  let R : ℝ := (2:ℝ)^N
  have hR : 0 < R := by dsimp [R]; positivity
  have hqR : (2:ℝ)^q ≤ R := by
    simpa only [Real.rpow_natCast] using
      Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) hq
  have hconst : 2*C^2*W ≤ R := by simpa only [Real.rpow_one] using hN₀ N hN
  have he : ε^2 ≤ C^2*R^(-(T+2)) := by
    have hpow := pow_le_pow_left₀ hε hbound 2
    convert hpow using 1
    rw [mul_pow,← Real.rpow_mul_natCast hR.le]
    congr 2
    ring
  calc
    _ ≤ 2*R*(C^2*R^(-(T+2)))*W := by gcongr
    _ = (2*C^2*W)*R*R^(-(T+2)) := by ring
    _ ≤ R*R*R^(-(T+2)) := by gcongr
    _ = R^(-T) := by
      rw [← sq,← Real.rpow_two,← Real.rpow_add hR]
      congr 1
      ring

theorem eventual_scalar_shell_absorption {σ C W : ℝ} (hσ : 0 < σ)
    (hC : 0 ≤ C) (hW : 0 ≤ W) (A T : ℝ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ q ε H F : ℝ, q ≤ N → 0 ≤ ε → 0 ≤ H →
      ε ≤ C*((2:ℝ)^N)^(-((T+2)/2)) →
      F ≤ A*H+2*(2:ℝ)^q*ε^2*W →
      F ≤ ((2:ℝ)^N)^σ*H+((2:ℝ)^N)^(-T) := by
  obtain ⟨N₁,hN₁⟩ := eventual_scalar_shell_error_budget T hC hW
  obtain ⟨N₂,hN₂⟩ := Regularization.fixed_constant_absorbed hσ A
  refine ⟨max N₁ N₂,?_⟩
  intro N hN q ε H F hq hε hH he hF
  exact hF.trans (add_le_add
    (mul_le_mul_of_nonneg_right (hN₂ N ((le_max_right _ _).trans hN)) hH)
    (hN₁ N ((le_max_left _ _).trans hN) q ε hq hε he))

end Falconer

end OAI
