import OAI.NumberTheory.EgyptianFractions.SimultaneousSelection

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337.FourierFailureBounds

/-- Frequency union and second-moment Markov bound with the exact scales used
    in the random-product construction. -/
theorem failure_fraction_le_exp {Ω L : Type*} [Fintype Ω] [Nonempty Ω]
    [DecidableEq Ω] (freq : Finset L) (phase : Ω → L → ℂ) (m w : ℝ)
    (hfreq : (freq.card : ℝ) ≤ Real.exp (4 * m / 10000))
    (hmoment : ∀ l ∈ freq, (∑ ω, ‖phase ω l‖ ^ 2) ≤
      (Fintype.card Ω : ℝ) * Real.exp (-w / 100)) :
    ((Finset.univ.filter (fun ω => ∃ l ∈ freq,
      Real.exp (-3 * m / 10000) < ‖phase ω l‖)).card : ℝ) /
      Fintype.card Ω ≤ Real.exp (m / 1000 - w / 100) := by
  classical
  have hΩ : (0 : ℝ) < Fintype.card Ω := by exact_mod_cast Fintype.card_pos
  apply (div_le_iff₀ hΩ).2
  have hmarkov := card_exists_large_norm_le_of_moments Finset.univ freq phase
    (Real.exp (-3 * m / 10000))
    ((Fintype.card Ω : ℝ) * Real.exp (-w / 100)) (Real.exp_pos _) hmoment
  calc
    ((Finset.univ.filter (fun ω => ∃ l ∈ freq,
        Real.exp (-3 * m / 10000) < ‖phase ω l‖)).card : ℝ) ≤
        (freq.card : ℝ) * ((Fintype.card Ω : ℝ) * Real.exp (-w / 100)) /
          Real.exp (-3 * m / 10000) ^ 2 := hmarkov
    _ ≤ Real.exp (4 * m / 10000) *
        ((Fintype.card Ω : ℝ) * Real.exp (-w / 100)) /
          Real.exp (-3 * m / 10000) ^ 2 := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_right hfreq (by positivity)
    _ = Real.exp (m / 1000 - w / 100) * Fintype.card Ω := by
      have he : Real.exp (4 * m / 10000) * Real.exp (-w / 100) /
          Real.exp (-3 * m / 10000) ^ 2 = Real.exp (m / 1000 - w / 100) := by
        rw [sq, ← Real.exp_add, ← Real.exp_add, ← Real.exp_sub]
        congr 1
        ring
      calc
        _ = (Real.exp (4 * m / 10000) * Real.exp (-w / 100) /
          Real.exp (-3 * m / 10000) ^ 2) * Fintype.card Ω := by ring
        _ = _ := by rw [he]

/-- Throughout a middle level, the logarithmic range is at least
    `(1-10⁻⁴)m`, giving the uniform single-block failure budget `exp(-m/200)`. -/
theorem middle_failure_fraction_le {Ω L : Type*} [Fintype Ω] [Nonempty Ω]
    [DecidableEq Ω] (freq : Finset L) (phase : Ω → L → ℂ) (m w : ℝ)
    (hm : 0 ≤ m) (hw : (9999 / 10000 : ℝ) * m ≤ w)
    (hfreq : (freq.card : ℝ) ≤ Real.exp (4 * m / 10000))
    (hmoment : ∀ l ∈ freq, (∑ ω, ‖phase ω l‖ ^ 2) ≤
      (Fintype.card Ω : ℝ) * Real.exp (-w / 100)) :
    ((Finset.univ.filter (fun ω => ∃ l ∈ freq,
      Real.exp (-3 * m / 10000) < ‖phase ω l‖)).card : ℝ) /
      Fintype.card Ω ≤ Real.exp (-m / 200) := by
  apply (failure_fraction_le_exp freq phase m w hfreq hmoment).trans
  apply Real.exp_le_exp.mpr
  linarith

/-- At a terminal integer the same Fourier bound gives the power-law failure
    probability amplified by the one-thousand-block selection lemma. -/
theorem terminal_failure_fraction_le {Ω L : Type*} [Fintype Ω] [Nonempty Ω]
    [DecidableEq Ω] (freq : Finset L) (phase : Ω → L → ℂ) (u : ℝ)
    (hu : 1 ≤ u)
    (hfreq : (freq.card : ℝ) ≤ Real.exp (4 * Real.log u / 10000))
    (hmoment : ∀ l ∈ freq, (∑ ω, ‖phase ω l‖ ^ 2) ≤
      (Fintype.card Ω : ℝ) * Real.exp (-Real.log u / 100)) :
    ((Finset.univ.filter (fun ω => ∃ l ∈ freq,
      Real.exp (-3 * Real.log u / 10000) < ‖phase ω l‖)).card : ℝ) /
      Fintype.card Ω ≤ u ^ (-(1 / 200 : ℝ)) := by
  apply (failure_fraction_le_exp freq phase (Real.log u) (Real.log u) hfreq hmoment).trans
  have hupos : 0 < u := by linarith
  rw [Real.rpow_def_of_pos hupos]
  apply Real.exp_le_exp.mpr
  have hlog := Real.log_nonneg hu
  linarith

end Problem337.FourierFailureBounds

end

end OAI
