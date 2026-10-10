import OAI.NumberTheory.EgyptianFractions.DescentRecurrence
import OAI.NumberTheory.EgyptianFractions.DescentDecay

namespace OAI
noncomputable section
open Filter
open scoped Topology

namespace Problem337.DescentDecay

/-- Complete analytic endgame for backwards exceptional densities.
The residue and moment arguments must supply the displayed recurrence and depth bound. -/
theorem eventually_density_le_eighth (c K r α : ℝ)
    (hc : 0 < c) (hK : 0 ≤ K) (hr : 0 ≤ r)
    (hα0 : 0 < α) (hα1 : α < 1) (hαr : 1 / (1 - α) ≤ r) :
    ∀ᶠ S : ℝ in atTop, ∀ (m : ℝ) (d : ℕ) (δ : ℕ → ℝ),
      S / (2 * Real.log S) ≤ m → (d : ℝ) ≤ K * Real.log S →
      S ^ (-1 / 4 : ℝ) ≤ α ^ d →
      δ d = 0 → (∀ j ≤ d, 0 ≤ δ j) →
      (∀ j < d, δ j ≤ Real.exp (-(c * m)) +
        Real.exp (2 * S ^ (1 / 4 : ℝ)) * (δ (j + 1)) ^ α) →
      δ 0 ≤ 1 / 8 := by
  filter_upwards [eventually_descent_bound_le_eighth c K r hc hK hr,
    eventually_gt_atTop (1 : ℝ)] with S hdecay hS
  intro m d δ hm hd hdepth hδd hδ hstep
  have hS0 : 0 < S := by linarith
  have hlog : 0 < Real.log S := Real.log_pos hS
  have hm0 : 0 ≤ m := le_trans (by positivity) hm
  have hb0 : 0 ≤ c * m := mul_nonneg hc.le hm0
  have ha0 : 0 ≤ 2 * S ^ (1 / 4 : ℝ) := by positivity
  have ha : (2 * S ^ (1 / 4 : ℝ)) / (1 - α) ≤
      2 * r * S ^ (1 / 4 : ℝ) := by
    calc
      (2 * S ^ (1 / 4 : ℝ)) / (1 - α) =
          (2 * S ^ (1 / 4 : ℝ)) * (1 / (1 - α)) := by ring
      _ ≤ (2 * S ^ (1 / 4 : ℝ)) * r := mul_le_mul_of_nonneg_left hαr ha0
      _ = 2 * r * S ^ (1 / 4 : ℝ) := by ring
  have hb := mul_le_mul_of_nonneg_left hdepth hb0
  calc
    δ 0 ≤ (d : ℝ) * Real.exp
        ((2 * S ^ (1 / 4 : ℝ)) / (1 - α) - c * m * α ^ d) :=
      descent_recurrence_exp_bound δ d (2 * S ^ (1 / 4 : ℝ)) (c * m) α
        ha0 hb0 hα0 hα1 hδd hδ hstep
    _ ≤ (d : ℝ) * Real.exp
        (2 * r * S ^ (1 / 4 : ℝ) - c * m * S ^ (-1 / 4 : ℝ)) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (Nat.cast_nonneg d)
    _ ≤ 1 / 8 := hdecay m d hm (Nat.cast_nonneg d) hd

end Problem337.DescentDecay

end

end OAI
