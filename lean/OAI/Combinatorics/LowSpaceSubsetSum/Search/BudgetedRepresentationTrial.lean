import OAI.Combinatorics.LowSpaceSubsetSum.Search.BudgetedPreparedSchedule
import OAI.Combinatorics.LowSpaceSubsetSum.Separators.PreparedSeparatorExpectation
import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationCoreFavorable
import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationDomainSoundness

namespace OAI

/-! # The stopped representation trial on sampled input-only histories

The trial composes table construction with the residue schedule on a
sampled history and its coordinate arrays.
-/

noncomputable section

namespace LowSpaceSubsetSum.RepresentationData

variable {n : ℕ} (D : RepresentationData n)

abbrev sampledSchedule (hn : 10000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ) + 1) + 1 ≤ (n : ℝ) / 1000)
    (h : D.zeroSetup.BucketTrialHistory (by omega)) :=
  D.scheduleData h.1.1.1 h.1.1.2 hn hlog h.1.2.val
    (primeRange_prime h.1.2.property).pos

def sampledCodes (hn : 10000 ≤ n) (h : D.zeroSetup.BucketTrialHistory (by omega)) :=
  PreparedSeparatorExpectation.codes
    (RepresentationSetup.separatorParameters h.1.1.1.1.1.2 (by omega)) h.2

theorem sampledCodes_size (hn : 10000 ≤ n) (h : D.zeroSetup.BucketTrialHistory (by omega))
    (i : Fin 4) : (D.sampledCodes hn h i).size ≤ 11 * 2 ^ (2 * RepresentationSetup.blockHalf n 0) :=
  PreparedSeparatorExpectation.codes_size _ _ i

theorem sampledCodes_decode (hn : 10000 ≤ n) (h : D.zeroSetup.BucketTrialHistory (by omega)) :
    (fun i => (D.sampledCodes hn h i).map SeparatorStoredMasks.decode) =
      SeparatorCheck.sampledFamilies h.2 :=
  PreparedSeparatorExpectation.codes_decode _ _

def sampledSignMask (hn : 10000 ≤ n) (h : D.zeroSetup.BucketTrialHistory (by omega)) :=
  (IndexedMask.measuredDomain h.1.1.1.1.1.1.2).1

theorem sampledSignMask_value (hn : 10000 ≤ n) (h : D.zeroSetup.BucketTrialHistory (by omega)) :
    (D.sampledSignMask hn h).semantic = h.1.1.1.1.1.1.2 :=
  IndexedMask.measuredDomain_semantic _

def sampledRows (hn : 10000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ) + 1) + 1 ≤ (n : ℝ) / 1000)
    (h : D.zeroSetup.BucketTrialHistory (by omega)) :
    Fin 4 → Vector (Fin n) (2 * RepresentationSetup.blockHalf n 0) :=
  fun i => Vector.ofFn (fun j => (D.sampledSchedule hn hlog h).coordinates.index (i, j))

theorem sampledRows_value (hn : 10000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ) + 1) + 1 ≤ (n : ℝ) / 1000)
    (h : D.zeroSetup.BucketTrialHistory (by omega)) (i : Fin 4)
    (j : Fin (2 * RepresentationSetup.blockHalf n 0)) :
    (D.sampledRows hn hlog h i)[j] = (D.sampledSchedule hn hlog h).coordinates.index (i, j) := by
  simp [sampledRows]

def executeTrial (hn : 10000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ) + 1) + 1 ≤ (n : ℝ) / 1000)
    (B : ℕ) (h : D.zeroSetup.BucketTrialHistory (by omega)) (budget : ℕ) :=
  BudgetedPreparedSchedule.run (D.sampledSchedule hn hlog h) (D.sampledSignMask hn h)
    (D.sampledSignMask_value hn h) B (D.sampledRows hn hlog h)
    (D.sampledCodes hn h) (D.sampledCodes_size hn h) budget

theorem executeTrial_value (hn : 10000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ) + 1) + 1 ≤ (n : ℝ) / 1000)
    (B : ℕ) (h : D.zeroSetup.BucketTrialHistory (by omega)) (budget : ℕ)
    (v : Bool) (rest : ℕ) (he : (D.executeTrial hn hlog B h budget).1 = some (v, rest)) :
    v = D.sampledTrial hn hlog B h := by
  have hv := BudgetedPreparedSchedule.value (D.sampledSchedule hn hlog h)
    (D.sampledSignMask hn h) (D.sampledSignMask_value hn h) B (D.sampledRows hn hlog h)
    (D.sampledRows_value hn hlog h) (D.sampledCodes hn h) (D.sampledCodes_size hn h)
    budget v rest he
  rw [D.sampledCodes_decode] at hv
  exact hv

theorem executeTrial_account (hn : 10000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ) + 1) + 1 ≤ (n : ℝ) / 1000)
    (hscale : Real.logb 2 (inputScale D.input : ℝ) ≤ (n : ℝ) / 1000000000)
    (h : D.zeroSetup.BucketTrialHistory (by omega)) (budget : ℕ) :
    BudgetedSeparatorFlow.Account budget
      (D.executeTrial hn hlog (representationBufferCapacity n) h budget) := by
  apply BudgetedSeparatorFlow.bind_account
  · exact BudgetedIncidencePreparation.account _ _ _ _
  · intro blocks left _
    exact D.schedule_account h.1.1.1 h.1.1.2 hn hlog hscale h.1.2.val
      (primeRange_prime h.1.2.property).pos (D.sampledSignMask hn h)
      (D.sampledSignMask_value hn h) blocks left

theorem executeTrial_accepts_core (hn : 10000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ) + 1) + 1 ≤ (n : ℝ) / 1000)
    (B : ℕ) (h : D.zeroSetup.BucketTrialHistory (by omega))
    (hh : D.CoreFavorable hn hlog B h) :
    ∃ rest, (D.executeTrial hn hlog B h (2 * trialWatchdog D.input)).1 = some (true, rest) := by
  have hg : 2 * RepresentationSetup.blockHalf n 0 ≤ n := by
    simp only [RepresentationSetup.blockHalf, Matrix.cons_val_zero]
    omega
  have hw : 2 ^ (2 * (2 * RepresentationSetup.blockHalf n 0)) ≤ 2 ^ ((n + 1) / 2) := by
    apply Nat.pow_le_pow_right (by decide)
    simp only [RepresentationSetup.blockHalf, Matrix.cons_val_zero]
    omega
  apply BudgetedPreparedSchedule.accepts_of_core (D.sampledSchedule hn hlog h)
    (D.sampledSignMask hn h) (D.sampledSignMask_value hn h) B hn hg hw
    (D.sampledRows hn hlog h) (D.sampledRows_value hn hlog h)
    (D.sampledCodes hn h) (D.sampledCodes_size hn h)
  · rw [D.sampledCodes_decode]
    exact hh.2
  · rw [D.sampledCodes_decode]
    exact hh.1

def stoppedTrial (hn : 10000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ) + 1) + 1 ≤ (n : ℝ) / 1000)
    (B : ℕ) (h : D.zeroSetup.BucketTrialHistory (by omega)) : Bool :=
  match (D.executeTrial hn hlog B h (2 * trialWatchdog D.input)).1 with
  | some (v, _) => v
  | none => false

theorem stoppedTrial_of_core (hn : 10000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ) + 1) + 1 ≤ (n : ℝ) / 1000)
    (B : ℕ) (h : D.zeroSetup.BucketTrialHistory (by omega)) (hh : D.CoreFavorable hn hlog B h) :
    D.stoppedTrial hn hlog B h = true := by
  obtain ⟨rest, he⟩ := D.executeTrial_accepts_core hn hlog B h hh
  simp only [stoppedTrial, he]

theorem stoppedTrial_sound (hn : 10000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ) + 1) + 1 ≤ (n : ℝ) / 1000)
    (B : ℕ) (h : D.zeroSetup.BucketTrialHistory (by omega))
    (hh : D.stoppedTrial hn hlog B h = true) : Solvable D.input := by
  unfold stoppedTrial at hh
  cases he : (D.executeTrial hn hlog B h (2 * trialWatchdog D.input)).1 with
  | none => simp only [he, Bool.false_eq_true] at hh
  | some p =>
    obtain ⟨v, rest⟩ := p
    simp only [he] at hh
    have hv := D.executeTrial_value hn hlog B h _ v rest he
    rw [hh] at hv
    exact D.trial_sound h.1.1.1 h.1.1.2 hn hlog h.1.2.val
      (primeRange_prime h.1.2.property).pos B (SeparatorCheck.sampledFamilies h.2) hv.symm

end LowSpaceSubsetSum.RepresentationData

namespace LowSpaceSubsetSum.RepresentationSetup

variable {n : ℕ} (R : RepresentationSetup n)

/-- The bounded sampler reaches an actually completed accepting watchdog
execution with the same inverse-polynomial lower bound. -/
theorem bounded_stopped_probability (hn : 180000000 ≤ n)
    (hmean : meanDeficiency R.originalWeights Finset.univ R.halfSize <
      (153 / 20000 : ℝ) * n)
    (hden : (R.halfSize : ℝ) + 1 <
      (2 : ℝ) ^ ((1 / 1500 : ℝ) * R.halfSize))
    (hscale : Real.logb 2 (inputScale R.input : ℝ) ≤ (n : ℝ) / 1000000000) (B : ℕ) :
    let hlog := representation_log_budget (by omega : 10000 ≤ n)
      R.mixerSize_add_one_le_scale hscale
    1 / (inputScale R.input : ℝ) ^ 110 ≤
      (R.runtimeSampler (by omega)).boundedLaw.probability (fun o => ∃ h,
        o = some h ∧ R.runtimeData.stoppedTrial (by omega) hlog B h = true) := by
  dsimp only
  exact (R.bounded_runtime_core_probability hn hmean hden hscale B).trans
    (FiniteLaw.probability_mono _ (fun _ ⟨h, he, hh⟩ =>
      ⟨h, he, R.runtimeData.stoppedTrial_of_core (by omega) _ B h hh⟩))

end LowSpaceSubsetSum.RepresentationSetup

end

end OAI
