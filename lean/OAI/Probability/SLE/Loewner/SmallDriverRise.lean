import OAI.Probability.SLE.Loewner.LoewnerSmallDriverHeight

namespace OAI

/-! A fixed small-driver neighborhood forces a vertical rise; the radius
does not depend on a choice of continuous capacity-two trace. -/
noncomputable section
open Set Filter
open scoped Topology NNReal

namespace SLEExactGauge

theorem exists_small_driver_rise (T : ℝ≥0) (H : ℝ)
    (hH : 0 ≤ H) (hHT : H < 2*Real.sqrt T) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (U : ℝ≥0 → ℝ) (γ : ℝ≥0 → ℂ)
      (G F : ℝ≥0 → ℂ → ℂ), IsCapacityTwoWitness U γ G F →
      (∀ t ∈ Icc 0 T, |U t| ≤ ε) → ∃ t ∈ Icc 0 T, H < (γ t).im := by
  classical
  by_contra! hbad
  let δ : ℕ → ℝ := fun n => 1/((n:ℝ)+1)
  have hδ (n : ℕ) : 0 < δ n := by dsimp [δ]; positivity
  choose U γ G F hw hU hheight using fun n => hbad (δ n) (hδ n)
  exact small_drivers_not_all_height_bounded U γ G F hw T H hH hHT δ
    tendsto_one_div_add_atTop_nhds_zero_nat hU hheight

end SLEExactGauge

end

end OAI
