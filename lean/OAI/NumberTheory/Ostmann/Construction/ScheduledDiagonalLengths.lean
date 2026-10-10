import OAI.NumberTheory.Ostmann.Construction.ScheduledCellSteps
import OAI.NumberTheory.Ostmann.Arithmetic.MovingInitialDiagonalUniform

namespace OAI

/-! # The deterministic small-slot counts in the finite diagonal family -/
namespace Ostmann

noncomputable def scheduledTailLength (k n : ℕ) : ℕ := 6 + 4 * (k - (n + 1))

theorem scheduledTailLength_eq (cs : List ℕ) (k n : ℕ) (hlen : cs.length = k) :
    scheduledSmallLength (cs.drop (n + 1)) = scheduledTailLength k n := by
  rw [scheduledSmallLength_eq, List.length_drop, hlen]
  rfl

theorem scheduledTailLength_budget (k n : ℕ) (hn : n < k) (K : ℝ) (hK : 0 ≤ K)
    (hdepth : 40 * (K + 1) ≤ (k : ℝ) ^ 3) :
    4 * (K + 1) * scheduledTailLength k n ≤ (k : ℝ) ^ 4 := by
  have hk : 1 ≤ k := by omega
  have hr : scheduledTailLength k n ≤ 10 * k := by
    unfold scheduledTailLength
    omega
  have hkr : 1 ≤ (k : ℝ) := by exact_mod_cast hk
  have hrr : (scheduledTailLength k n : ℝ) ≤ 10 * k := by exact_mod_cast hr
  have hh := mul_le_mul_of_nonneg_right hdepth (show 0 ≤ (k : ℝ) by positivity)
  have hb := mul_le_mul_of_nonneg_left hrr (show 0 ≤ 4 * (K + 1) by linarith)
  nlinarith only [hh, hb]

end Ostmann

end OAI
