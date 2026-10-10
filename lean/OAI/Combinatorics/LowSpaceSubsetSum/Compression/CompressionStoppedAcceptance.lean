import OAI.Combinatorics.LowSpaceSubsetSum.Compression.BudgetedCompressionTrial

namespace OAI

/-! # Bounded-sampler acceptance of the executed compression trial

The accepted event requires a completed shared-budget execution, from
array generation to the final residue. Watchdog failure returns false.
-/

noncomputable section

namespace LowSpaceSubsetSum.CompressionData

variable {n : ℕ} (D : CompressionData n)

def stoppedCompressionTrial (B : ℕ) (h : CompressionSetup.TrialHistory n) : Bool :=
  match (BudgetedCompressionTrial.run D h.1 h.2 B (2 * trialWatchdog D.input)).1 with
  | none => false
  | some (v, _) => v

theorem stoppedCompressionTrial_accepts (B : ℕ) (hn : 10000 ≤ n)
    (h : CompressionSetup.TrialHistory n) (hh : D.AcceptedWithCompactTests B h) :
    D.stoppedCompressionTrial B h = true := by
  obtain ⟨rest, he⟩ := BudgetedCompressionTrial.accepts_watchdog D h.1 h.2 B hn hh.1 hh.2
  simp only [stoppedCompressionTrial, he]

theorem stoppedCompressionTrial_sound (B : ℕ) (h : CompressionSetup.TrialHistory n)
    (hh : D.stoppedCompressionTrial B h = true) : Solvable D.input := by
  unfold stoppedCompressionTrial at hh
  cases he : (BudgetedCompressionTrial.run D h.1 h.2 B (2 * trialWatchdog D.input)).1 with
  | none => simp only [he, Bool.false_eq_true] at hh
  | some p =>
    rcases p with ⟨v, rest⟩
    simp only [he] at hh
    subst v
    exact BudgetedCompressionTrial.sound D h.1 h.2 B _ rest he

theorem bounded_stoppedCompression_probability (B : ℕ) (hn : 168000000 ≤ n)
    (hsolve : Solvable D.input)
    (hmean : (153 / 20000 : ℝ) * n ≤
      meanDeficiency D.weights Finset.univ (compressionHalfSize n))
    (hlog : Real.logb 2 (inputScale D.input) ≤ (n : ℝ) / 1000000000) :
    (1 / 8 : ℝ) ≤ (D.sampler hn).boundedLaw.probability
      (fun o => ∃ h, o = some h ∧ D.stoppedCompressionTrial B h = true) := by
  apply (D.bounded_compact_acceptance_probability B hn hsolve hmean hlog).trans
  apply FiniteLaw.probability_mono
  rintro o ⟨h, ho, hh⟩
  exact ⟨h, ho, D.stoppedCompressionTrial_accepts B (by omega) h hh⟩

end LowSpaceSubsetSum.CompressionData

end

end OAI
