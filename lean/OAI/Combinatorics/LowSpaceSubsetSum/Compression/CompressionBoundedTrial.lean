import OAI.Combinatorics.LowSpaceSubsetSum.Compression.CompressionSamplerCoupling

namespace OAI

/-! # Actual compression acceptance after bounded fresh-word sampling -/

noncomputable section

namespace LowSpaceSubsetSum.CompressionData

variable {n : ℕ} (D : CompressionData n)

def AcceptedWithCompactTests (B : ℕ) (h : CompressionSetup.TrialHistory n) : Prop :=
  D.compactTests h.1 = true ∧ D.compressionTrial B h.1 h.2 = true

/-- Keep the actual seven compact-list tests in the successful event; later
resource bounds can use them without an independence premise. -/
theorem compact_acceptance_probability (B : ℕ) (hn : 168000000 ≤ n)
    (hsolve : Solvable D.input)
    (hmean : (153 / 20000 : ℝ) * n ≤
      meanDeficiency D.weights Finset.univ (compressionHalfSize n))
    (hlog : Real.logb 2 (inputScale D.input) ≤ (n : ℝ) / 1000000000) :
    (1 / 4 : ℝ) ≤ (D.trialLaw hn).probability (D.AcceptedWithCompactTests B) := by
  obtain ⟨S, hS⟩ := hsolve
  let R : CompressionSetup n := ⟨D.input, S, hS⟩
  apply (R.successful_probability hn hmean hlog).trans
  apply FiniteLaw.probability_mono
  intro h hh
  exact ⟨(R.compactTests_iff h.1).mpr hh.1, R.compressionTrial_true B h.1 h.2 hh.1 hh.2⟩

theorem bounded_compact_acceptance_probability (B : ℕ) (hn : 168000000 ≤ n)
    (hsolve : Solvable D.input)
    (hmean : (153 / 20000 : ℝ) * n ≤
      meanDeficiency D.weights Finset.univ (compressionHalfSize n))
    (hlog : Real.logb 2 (inputScale D.input) ≤ (n : ℝ) / 1000000000) :
    (1 / 8 : ℝ) ≤ (D.sampler hn).boundedLaw.probability
      (fun o => ∃ h, o = some h ∧ D.AcceptedWithCompactTests B h) := by
  have hp := D.compact_acceptance_probability B hn hsolve hmean hlog
  have hl := D.sampler_event hn (D.AcceptedWithCompactTests B)
  have he : 1 / (2 : ℝ) ^ n ≤ (1 / 8 : ℝ) := by
    have hh := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega : 3 ≤ n)
    norm_num at hh
    exact one_div_le_one_div_of_le (by norm_num) hh
  linarith

theorem bounded_compression_acceptance_probability (B : ℕ) (hn : 168000000 ≤ n)
    (hsolve : Solvable D.input)
    (hmean : (153 / 20000 : ℝ) * n ≤
      meanDeficiency D.weights Finset.univ (compressionHalfSize n))
    (hlog : Real.logb 2 (inputScale D.input) ≤ (n : ℝ) / 1000000000) :
    1 / (inputScale D.input : ℝ) ^ 110 ≤ (D.sampler hn).boundedLaw.probability
      (fun o => ∃ h, o = some h ∧ D.compressionTrial B h.1 h.2 = true) := by
  have hu : (2 : ℝ) ≤ inputScale D.input := by
    exact_mod_cast (show 2 ≤ inputScale D.input by unfold inputScale; omega)
  have hp : (8 : ℝ) ≤ (inputScale D.input : ℝ) ^ 110 := by
    calc
      _ ≤ (2 : ℝ) ^ 110 := by norm_num
      _ ≤ _ := pow_le_pow_left₀ (by norm_num) hu _
  apply (one_div_le_one_div_of_le (by norm_num) hp).trans
  apply (D.bounded_compact_acceptance_probability B hn hsolve hmean hlog).trans
  apply FiniteLaw.probability_mono
  rintro o ⟨h, ho, _, hh⟩
  exact ⟨h, ho, hh⟩

theorem sampled_acceptance_sound (B : ℕ) (_hn : 168000000 ≤ n)
    (o : Option (CompressionSetup.TrialHistory n))
    (h : ∃ h, o = some h ∧ D.compressionTrial B h.1 h.2 = true) : Solvable D.input := by
  obtain ⟨h, _, hh⟩ := h
  exact D.compressionTrial_sound B h.1 h.2 hh

end LowSpaceSubsetSum.CompressionData

end

end OAI
