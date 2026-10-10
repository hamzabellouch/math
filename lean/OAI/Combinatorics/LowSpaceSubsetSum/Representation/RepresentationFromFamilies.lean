import OAI.Combinatorics.LowSpaceSubsetSum.Separators.SeparatorFamilyExecution
import OAI.Combinatorics.LowSpaceSubsetSum.Search.BudgetedRepresentationTrial

namespace OAI

/-! # Passing the executed family arrays into the stopped representation trial

The prefix history supplies layout, partitions, moduli and residues. The
last random stage constructs actual arrays, which are retained directly by
the incidence-table builder and the subsequent stopped residue schedule.
-/

noncomputable section

namespace LowSpaceSubsetSum.RepresentationFromFamilies

variable {n : ℕ}

abbrev width (n : ℕ) := 2 * RepresentationSetup.blockHalf n 0

def schedule (D : RepresentationData n) (hn : 10000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ) + 1) + 1 ≤ (n : ℝ) / 1000)
    (h : D.zeroSetup.ExtraTrialHistory) :=
  D.scheduleData h.1.1 h.1.2 hn hlog h.2.val (primeRange_prime h.2.property).pos

def parameters (D : RepresentationData n) (hn : 10000 ≤ n)
    (h : D.zeroSetup.ExtraTrialHistory) :=
  RepresentationSetup.separatorParameters h.1.1.1.1.2 (by omega : 2200 ≤ n)

def run (D : RepresentationData n) (hn : 10000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ) + 1) + 1 ≤ (n : ℝ) / 1000)
    (h : D.zeroSetup.ExtraTrialHistory) (F : IndexedMask n)
    (hF : F.semantic = (schedule D hn hlog h).signs)
    (rows : Fin 4 → Vector (Fin n) (width n))
    (s : ((parameters D hn h).samplerCoupling n).Seed) (budget : ℕ) :
    BudgetedSeparatorCall.Outcome Bool :=
  let packed := SeparatorFamilyExecution.Application.run (parameters D hn h) n s
  match hp : packed.1 with
  | none => (none, packed.2 + 1)
  | some families =>
    let out := BudgetedPreparedSchedule.run (schedule D hn hlog h) F hF
      (representationBufferCapacity n) rows families
      (SeparatorFamilyExecution.Application.sizes (parameters D hn h) n s families hp) budget
    (out.1, packed.2 + out.2 + 1)

theorem value (D : RepresentationData n) (hn : 10000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ) + 1) + 1 ≤ (n : ℝ) / 1000)
    (h : D.zeroSetup.ExtraTrialHistory) (F : IndexedMask n)
    (hF : F.semantic = (schedule D hn hlog h).signs)
    (rows : Fin 4 → Vector (Fin n) (width n))
    (hrows : ∀ i j, (rows i)[j] = (schedule D hn hlog h).coordinates.index (i, j))
    (s : ((parameters D hn h).samplerCoupling n).Seed) (budget rest : ℕ) (v : Bool)
    (hy : (run D hn hlog h F hF rows s budget).1 = some (v, rest)) :
    ∃ draws, ((parameters D hn h).samplerCoupling n).bounded s = some draws ∧
      v = D.sampledTrial hn hlog (representationBufferCapacity n) ⟨h, draws⟩ := by
  simp only [run] at hy
  split at hy
  · contradiction
  next families hp =>
    have hv := SeparatorFamilyExecution.Application.value (parameters D hn h) n s
    rw [hp] at hv
    obtain ⟨draws, hd, he⟩ := Option.map_eq_some_iff.mp hv.symm
    have hb : ((parameters D hn h).samplerCoupling n).bounded s = some draws := by
      rw [← ((parameters D hn h).samplerExecution n).value_eq]
      exact hd
    refine ⟨draws, hb, ?_⟩
    have ht := BudgetedPreparedSchedule.value (schedule D hn hlog h) F hF
      (representationBufferCapacity n) rows hrows families
      (SeparatorFamilyExecution.Application.sizes (parameters D hn h) n s families hp)
      budget v rest hy
    rw [← he, PreparedSeparatorExpectation.codes_decode] at ht
    exact ht

theorem work (D : RepresentationData n) (hn : 10000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ) + 1) + 1 ≤ (n : ℝ) / 1000)
    (hscale : Real.logb 2 (inputScale D.input : ℝ) ≤ (n : ℝ) / 1000000000)
    (h : D.zeroSetup.ExtraTrialHistory) (F : IndexedMask n)
    (hF : F.semantic = (schedule D hn hlog h).signs)
    (rows : Fin 4 → Vector (Fin n) (width n))
    (s : ((parameters D hn h).samplerCoupling n).Seed) (budget : ℕ) :
    (run D hn hlog h F hF rows s budget).2 ≤
      44 * 2 ^ width n * (width n * n ^ 3 + 32 * (width n + 1) ^ 3 + 4) + 21 + budget + 2 := by
  have hp := SeparatorFamilyExecution.Application.work (parameters D hn h) n s
  dsimp only [width] at hp ⊢
  simp only [run]
  split
  · dsimp only; omega
  next families hf =>
    have ha : BudgetedSeparatorFlow.Account budget
        (BudgetedPreparedSchedule.run (schedule D hn hlog h) F hF
          (representationBufferCapacity n) rows families
          (SeparatorFamilyExecution.Application.sizes (parameters D hn h) n s families hf) budget) := by
      apply BudgetedSeparatorFlow.bind_account
      · exact BudgetedIncidencePreparation.account _ _ _ _
      · intro blocks left _
        exact D.schedule_account h.1.1 h.1.2 hn hlog hscale h.2.val
          (primeRange_prime h.2.property).pos F hF blocks left
    change _ + _ + 1 ≤ _
    have hb := ha.1
    omega

theorem accepts (D : RepresentationData n) (hn : 10000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ) + 1) + 1 ≤ (n : ℝ) / 1000)
    (h : D.zeroSetup.ExtraTrialHistory) (F : IndexedMask n)
    (hF : F.semantic = (schedule D hn hlog h).signs)
    (rows : Fin 4 → Vector (Fin n) (width n))
    (hrows : ∀ i j, (rows i)[j] = (schedule D hn hlog h).coordinates.index (i, j))
    (s : ((parameters D hn h).samplerCoupling n).Seed)
    (draws : D.zeroSetup.SeparatorDraws h.1.1 (by omega))
    (hs : ((parameters D hn h).samplerCoupling n).bounded s = some draws)
    (hh : D.CoreFavorable hn hlog (representationBufferCapacity n) ⟨h, draws⟩) :
    ∃ rest, (run D hn hlog h F hF rows s (2 * trialWatchdog D.input)).1 =
      some (true, rest) := by
  have hp := SeparatorFamilyExecution.Application.value (parameters D hn h) n s
  rw [((parameters D hn h).samplerExecution n).value_eq, hs] at hp
  have hp' : (SeparatorFamilyExecution.Application.run (parameters D hn h) n s).1 =
      some (PreparedSeparatorExpectation.codes (parameters D hn h) draws) := hp
  have hdecode : (fun i =>
      (PreparedSeparatorExpectation.codes (parameters D hn h) draws i).map
        SeparatorStoredMasks.decode) = SeparatorCheck.sampledFamilies draws :=
    PreparedSeparatorExpectation.codes_decode (parameters D hn h) draws
  have hg : width n ≤ n := by
    simp only [width, RepresentationSetup.blockHalf, Matrix.cons_val_zero]
    omega
  have hw : 2 ^ (2 * width n) ≤ 2 ^ ((n + 1) / 2) := by
    apply Nat.pow_le_pow_right (by decide)
    simp only [width, RepresentationSetup.blockHalf, Matrix.cons_val_zero]
    omega
  obtain ⟨rest, hr⟩ := BudgetedPreparedSchedule.accepts_of_core (schedule D hn hlog h)
    F hF (representationBufferCapacity n) hn hg hw rows hrows
    (PreparedSeparatorExpectation.codes (parameters D hn h) draws)
    (PreparedSeparatorExpectation.codes_size (parameters D hn h) draws)
    (by rw [hdecode]; exact hh.2)
    (by rw [hdecode]; exact hh.1)
  refine ⟨rest, ?_⟩
  unfold run
  dsimp only
  split
  · rename_i he
    rw [hp'] at he
    contradiction
  · rename_i families he
    have heq := Option.some.inj (he.symm.trans hp')
    subst families
    exact hr

theorem sound (D : RepresentationData n) (hn : 10000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ) + 1) + 1 ≤ (n : ℝ) / 1000)
    (h : D.zeroSetup.ExtraTrialHistory) (F : IndexedMask n)
    (hF : F.semantic = (schedule D hn hlog h).signs)
    (rows : Fin 4 → Vector (Fin n) (width n))
    (hrows : ∀ i j, (rows i)[j] = (schedule D hn hlog h).coordinates.index (i, j))
    (s : ((parameters D hn h).samplerCoupling n).Seed) (budget rest : ℕ)
    (hy : (run D hn hlog h F hF rows s budget).1 = some (true, rest)) :
    Solvable D.input := by
  obtain ⟨draws, _, hyes⟩ := value D hn hlog h F hF rows hrows s budget rest true hy
  exact D.trial_sound h.1.1 h.1.2 hn hlog h.2.val
    (primeRange_prime h.2.property).pos (representationBufferCapacity n)
    (SeparatorCheck.sampledFamilies draws) hyes.symm

end LowSpaceSubsetSum.RepresentationFromFamilies

end

end OAI
