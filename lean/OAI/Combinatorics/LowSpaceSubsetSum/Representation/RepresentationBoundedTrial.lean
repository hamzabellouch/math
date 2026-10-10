import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationFavorableTrial
import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationSamplingLoss

namespace OAI

/-! # Favorable representation trials survive the bounded sampler -/

noncomputable section

namespace LowSpaceSubsetSum.RepresentationSetup

variable {n : ℕ} (R : RepresentationSetup n)

/-- The finite bounded sampler retains enough probability for the manuscript's
round amplification, including the concrete full-execution work events. -/
theorem bounded_favorable_trial_probability (hn : 180000000 ≤ n)
    (hmean : meanDeficiency R.originalWeights Finset.univ R.halfSize <
      (153 / 20000 : ℝ) * n)
    (hden : (R.halfSize : ℝ) + 1 <
      (2 : ℝ) ^ ((1 / 1500 : ℝ) * R.halfSize))
    (hscale : Real.logb 2 (inputScale R.input : ℝ) ≤ (n : ℝ) / 1000000000) (B : ℕ) :
    let hlog := representation_log_budget (by omega : 10000 ≤ n)
      R.mixerSize_add_one_le_scale hscale
    1 / (inputScale R.input : ℝ) ^ 110 ≤
      (R.bucketHistoryCoupling (by omega)).boundedLaw.probability
        (fun h => ∃ x, h = some x ∧ R.FavorableTrial (by omega) hlog B x) := by
  dsimp only
  let hlog := representation_log_budget (by omega : 10000 ≤ n)
    R.mixerSize_add_one_le_scale hscale
  have hp := R.favorable_trial_probability hn hmean hden hscale B
  have hl := (R.bucketHistoryCoupling (by omega)).event_lower
    (R.FavorableTrial (by omega) hlog B)
  rw [R.bucketHistoryCoupling_uniform] at hl
  have hf := R.bucketHistoryCoupling_failure_guard (by omega) hscale
  let u : ℝ := inputScale R.input
  have hu : 2 ≤ u := by
    dsimp only [u]
    exact_mod_cast (show 2 ≤ inputScale R.input by unfold inputScale; omega)
  have hu0 : 0 < u := by linarith
  have hpow : 2 ≤ u ^ 10 := by
    have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hu 10
    norm_num at hh
    linarith
  have hmargin : 1 / u ^ 110 + (1 / 10 : ℝ) / u ^ 110 ≤ (3 / 5 : ℝ) / u ^ 100 := by
    have hsmall : (11 / 10 : ℝ) ≤ (3 / 5 : ℝ) * u ^ 10 := by linarith
    calc
      _ = (11 / 10 : ℝ) / u ^ 110 := by ring
      _ ≤ ((3 / 5 : ℝ) * u ^ 10) / u ^ 110 :=
        div_le_div_of_nonneg_right hsmall (by positivity)
      _ = _ := by
        rw [show u ^ 110 = u ^ 100 * u ^ 10 by ring]
        field_simp
  change 1 / u ^ 110 ≤ _
  change (3 / 5 : ℝ) / u ^ 100 ≤ _ at hp
  change _ ≤ (1 / 10 : ℝ) / u ^ 110 at hf
  linarith only [hp, hl, hf, hmargin]

end LowSpaceSubsetSum.RepresentationSetup

end

end OAI
