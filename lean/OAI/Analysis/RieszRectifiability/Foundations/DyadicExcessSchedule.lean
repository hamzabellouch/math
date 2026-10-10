import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.NormalizedTailDecay

namespace OAI

namespace RieszRectifiability

noncomputable section

open Filter Topology

theorem dyadic_excess_horizon_identity (b : ℝ) (j : ℕ) :
    (1 / 2 : ℝ) ^ j * b ^ (2 * j + 3) = b ^ 3 * (b ^ 2 / 2) ^ j := by
  rw [pow_add b (2 * j) 3, pow_mul b 2 j]
  have hp : (1 / 2 : ℝ) ^ j * (b ^ 2) ^ j = (b ^ 2 / 2) ^ j := by
    rw [← mul_pow]
    congr 1
    ring
  calc
    (1 / 2 : ℝ) ^ j * ((b ^ 2) ^ j * b ^ 3) =
        b ^ 3 * ((1 / 2 : ℝ) ^ j * (b ^ 2) ^ j) := by ring
    _ = _ := by rw [hp]

theorem dyadic_excess_horizon_tendsto_zero (b : ℝ) (hb : b ^ 2 < 2) :
    Tendsto (fun j : ℕ => (1 / 2 : ℝ) ^ j * b ^ (2 * j + 3)) atTop (𝓝 0) := by
  simp only [dyadic_excess_horizon_identity]
  simpa only [mul_zero] using!
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity : 0 ≤ b ^ 2 / 2)
      (by linarith : b ^ 2 / 2 < 1)).const_mul (b ^ 3)

theorem exists_shift_uniform_dyadic_excess_threshold (b κ : ℝ)
    (hb : b ^ 2 < 2) (hκ : 0 < κ) :
    ∃ J : ℕ, ∀ j : ℕ,
      (1 / 2 : ℝ) ^ (j + J) * b ^ (2 * (j + J) + 3) ≤ κ := by
  have he := (dyadic_excess_horizon_tendsto_zero b hb).eventually (gt_mem_nhds hκ)
  obtain ⟨J, hJ⟩ := eventually_atTop.mp he
  refine ⟨J, fun j => (hJ (j + J) (by omega)).le⟩

end

end RieszRectifiability

end OAI
