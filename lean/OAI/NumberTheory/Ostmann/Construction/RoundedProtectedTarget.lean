import OAI.NumberTheory.Ostmann.Arithmetic.MovingProtectedTarget

namespace OAI

/-! # The protected target at the rounded integral endpoint -/
namespace Ostmann

theorem movingProtectedTarget_rounded_bounds (k : ℕ) (hk : 2 ≤ k)
    (h lo G Y td totalGap : ℝ) (hh : 1 ≤ h)
    (hYlo : 2 * lo + 2 ^ (k + 1) * (12 * h) ≤ Y)
    (hYhi : Y ≤ 2 * lo + 2 ^ (k + 1) * (12 * h) + 1)
    (hGlo : lo - 2 ≤ G) (hGhi : G ≤ lo - 2 + 12 * h)
    (herror : |totalGap - 2 * td| ≤ h) :
    16 * h ≤ movingProtectedTarget k Y G td totalGap ∧
      movingProtectedTarget k Y G td totalGap ≤ 32 * h := by
  have hp : (0 : ℝ) < 2 ^ k := by positivity
  have hp4 : (4 : ℝ) ≤ 2 ^ k := by
    have hh := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hk
    norm_num at hh
    exact hh
  have hph := mul_le_mul_of_nonneg_right hp4 (show 0 ≤ h by linarith)
  obtain ⟨herrlo, herrhi⟩ := abs_le.mp herror
  unfold movingProtectedTarget
  rw [le_div_iff₀ hp, div_le_iff₀ hp]
  rw [pow_succ] at hYlo hYhi
  constructor <;> nlinarith only [hYlo, hYhi, hGlo, hGhi, herrlo, herrhi, hph, hh]

end Ostmann

end OAI
