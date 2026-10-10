import OAI.NumberTheory.Ostmann.Arithmetic.MovingFrequencyRateMonotone
import OAI.NumberTheory.Ostmann.Construction.ScheduledIterationThresholds

namespace OAI

/-! # Fixed gap constants and a common large depth for the constructed schedule -/
namespace Ostmann
open Filter

noncomputable def scheduledInitialRate : ℝ := 6 * Real.log 2 + 13

noncomputable def scheduledIterationRate : ℝ := scheduledInitialRate + 1

/-- Both gap constants are chosen before the depth and before any selected cells. -/
theorem scheduled_gap_parameters : ∃ Bs BD : ℝ,
    1 ≤ Bs ∧ Bs + 1 ≤ BD ∧
    2 * ((4 - 2 * Real.log (1 / 320000)) + 2 + 2 * Real.log 4 +
      (4 * (Real.log 2 + 2) + 2 * Real.log 2 + 4) + 3) ≤ Bs - 1 ∧
    (Bs + 1) + 2 * scheduledIterationRate +
      (Real.log 2 - Real.log (1 / 16000 : ℝ) + 5 / 4 + 1 + Real.log 12 + 1 + 1) + 6 ≤
      BD - 1 := by
  let gap := 2 * ((4 - 2 * Real.log (1 / 320000)) + 2 + 2 * Real.log 4 +
    (4 * (Real.log 2 + 2) + 2 * Real.log 2 + 4) + 3)
  let Bs := 1 + max 0 gap
  let E := Real.log 2 - Real.log (1 / 16000 : ℝ) + 5 / 4 + 1 + Real.log 12 + 1 + 1
  let BD := max (Bs + 2) (Bs + 2 * scheduledIterationRate + E + 9)
  have hBs : 1 ≤ Bs := by dsimp only [Bs]; linarith only [le_max_left (0 : ℝ) gap]
  have hBD := le_max_left (Bs + 2) (Bs + 2 * scheduledIterationRate + E + 9)
  have hBDE := le_max_right (Bs + 2) (Bs + 2 * scheduledIterationRate + E + 9)
  refine ⟨Bs, BD, hBs, ?_, ?_, ?_⟩
  · dsimp only [BD]
    linarith only [hBD]
  · dsimp only [Bs]
    change gap ≤ 1 + max 0 gap - 1
    linarith only [le_max_right 0 gap]
  · change Bs + 1 + 2 * scheduledIterationRate + E + 6 ≤ BD - 1
    dsimp only [BD]
    linarith only [hBDE]

theorem eventual_scheduled_depth_reserves (R : ℝ) :
    ∀ᶠ k : ℕ in atTop, 2 ≤ k ∧
      120 ≤ (k : ℝ) ^ 3 ∧
      14 * (64 * R + 3) ≤ (k : ℝ) ^ 3 ∧
      20480 * R + 720 ≤ (k : ℝ) ^ 4 ∧
      1024 * R + 52 ≤ (k : ℝ) ^ 4 := by
  have h₃ : Tendsto (fun k : ℕ => (k : ℝ) ^ 3) atTop atTop :=
    (tendsto_pow_atTop (by norm_num : (3 : ℕ) ≠ 0)).comp tendsto_natCast_atTop_atTop
  have h₄ : Tendsto (fun k : ℕ => (k : ℝ) ^ 4) atTop atTop :=
    (tendsto_pow_atTop (by norm_num : (4 : ℕ) ≠ 0)).comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop (2 : ℕ),
    h₃.eventually (eventually_ge_atTop (120 : ℝ)),
    h₃.eventually (eventually_ge_atTop (14 * (64 * R + 3))),
    h₄.eventually (eventually_ge_atTop (20480 * R + 720)),
    h₄.eventually (eventually_ge_atTop (1024 * R + 52))] with k hk h₁ h₂ h₃ h₄
  exact ⟨hk, h₁, h₂, h₃, h₄⟩

end Ostmann

end OAI
