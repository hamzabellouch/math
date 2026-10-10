import OAI.MathematicalPhysics.CriticalMixing.Comparison

namespace OAI

noncomputable section
open scoped BigOperators Topology NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter

namespace CriticalSK

theorem critical_two_clock_mixing (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n : ℕ => (disorderLaw n).real (twoClockMixingEvent n ε))
      atTop (𝓝 1) := by
  obtain ⟨β, hβ0, hβ1, hsmall⟩ := temperature_close_to_one hε
  obtain ⟨C, hC, hP⟩ := fixed_temperature_poincare β hβ0 hβ1
  have hl : Tendsto (fun n : ℕ => (disorderLaw n).real (poincareEvent n β C) -
      mixingReductionError n ε) atTop (𝓝 1) := by
    simpa only [sub_zero] using hP.sub (mixingReductionError_tendsto hε)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hl tendsto_const_nhds
    (mixingGapReduction_lower hε hβ1.le hsmall hC)
    (Filter.Eventually.of_forall (fun _ => measureReal_le_one))

theorem critical_mixing_bounds (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n : ℕ => (disorderLaw n {W |
      (n : ℝ) ^ ((2 : ℝ) / 3 - ε) ≤ continuousMixingTime W ∧
      continuousMixingTime W ≤ Real.exp (ε * n)}).toReal) atTop (𝓝 1) ∧
    Tendsto (fun n : ℕ => (disorderLaw n {W |
      (n : ℝ) ^ ((5 : ℝ) / 3 - ε) ≤ (discreteMixingTime W : ℝ) ∧
      (discreteMixingTime W : ℝ) ≤ Real.exp (ε * n)}).toReal) atTop (𝓝 1) := by
  have hp := critical_two_clock_mixing ε hε
  constructor
  · apply tendsto_of_tendsto_of_tendsto_of_le_of_le hp tendsto_const_nhds
    · intro n
      refine measureReal_mono ?_
      intro W hW
      exact ⟨hW.1, hW.2.1⟩
    · intro n
      exact measureReal_le_one
  · apply tendsto_of_tendsto_of_tendsto_of_le_of_le hp tendsto_const_nhds
    · intro n
      refine measureReal_mono ?_
      intro W hW
      exact ⟨hW.2.2.1, hW.2.2.2⟩
    · intro n
      exact measureReal_le_one

end CriticalSK
end

end OAI
