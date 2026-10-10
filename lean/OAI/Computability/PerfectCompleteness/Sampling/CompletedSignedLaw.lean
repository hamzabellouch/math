import OAI.Computability.PerfectCompleteness.Reduction.FinitePreliminaryCompletion
import OAI.Computability.PerfectCompleteness.Reduction.SignedCompletionSchedule
import OAI.Computability.PerfectCompleteness.Sampling.MetadataFreeLaw

namespace OAI

section

namespace PerfectCompleteness.CompletedSignedLaw

open MetadataFreeSampler MetadataFreeLaw
open UniqueGamesTheorem.Foundations.Games
open CompletionSoundness CompletionSoundness.LegalProjectionGame
open scoped BigOperators Classical

noncomputable section

variable {branch : Nat → Nat} {n t v m : Nat}
  (clauses : Fin m → SourceClause.NormalizedClause v) (rows repeats : Nat → Nat)

local notation "locationCount" => TreeCanonical.locationCount branch n t
local notation "hq" δ => CanonicalLocalCompletion.alphabet_positive locationCount δ
local notation "large" δ => CanonicalLocalCompletion.partitionWidth_le_alphabet locationCount δ

local notation "F" => FinitePreliminaryCompletion.blockFamily clauses branch n t rows repeats

local instance leftVertex_fintype : Fintype (CanonicalGame.LeftVertex F) := Fintype.ofFinite _

local instance rightVertex_fintype : Fintype (CanonicalGame.RightVertex F) := Fintype.ofFinite _

local instance leftLabel_fintype (x : CanonicalGame.LeftVertex F) :
    Fintype (CanonicalGame.LeftLabel F x) := Fintype.ofFinite _

local instance rightLabel_fintype (y : CanonicalGame.RightVertex F) :
    Fintype (CanonicalGame.RightLabel F y) := Fintype.ofFinite _

abbrev SignedCompleted (δ : ℚ) :=
  Σ source : PreliminarySampler.Questions branch n t m,
    SignedCompletionSchedule.Completed (rows := rows) (repeats := repeats)
      (hq δ) (large δ) (sourceSigns clauses source)

variable [NeZero m] (hn : 0 < n) (hbranch : ∀ k < n, 0 < branch k)
  (hrows : ∀ k, 0 < rows (k + 1)) (δ : ℚ)

abbrev Completed :=
  Σ raw : PreliminarySampler.Raw clauses branch n t rows repeats,
    Fin ((FinitePreliminaryCompletion.actualFamily (t := t)
      clauses rows repeats hn hbranch hrows δ).size raw)

theorem size_eq_active (e : PreliminarySampler.Raw clauses branch n t rows repeats) :
    (FinitePreliminaryCompletion.actualFamily (t := t)
      clauses rows repeats hn hbranch hrows δ).size e =
        SignedCompletionSchedule.active (hq δ) (large δ)
      (sourceSigns clauses e.1.1) (encodeOutcome clauses rows repeats e) := rfl

def completedEquiv :
    Completed (t := t) clauses rows repeats hn hbranch hrows δ ≃
      SignedCompleted (branch := branch) (n := n) (t := t) clauses rows repeats δ :=
  (Equiv.sigmaCongrLeft
    (β := fun y : (Σ source : PreliminarySampler.Questions branch n t m,
      SignedOutcome (sourceSigns clauses source) rows repeats) =>
        Fin (SignedCompletionSchedule.active (hq δ) (large δ)
          (sourceSigns clauses y.1) y.2))
    (rawEquiv clauses rows repeats)).trans
    (Equiv.sigmaAssoc (fun source outcome =>
      Fin (SignedCompletionSchedule.active (hq δ) (large δ)
        (sourceSigns clauses source) outcome)))

@[simp] theorem completedEquiv_apply
    (e : PreliminarySampler.Raw clauses branch n t rows repeats)
    (seed : Fin ((FinitePreliminaryCompletion.actualFamily (t := t)
      clauses rows repeats hn hbranch hrows δ).size e)) :
    completedEquiv (t := t) clauses rows repeats hn hbranch hrows δ ⟨e, seed⟩ =
      ⟨e.1.1, encodeOutcome clauses rows repeats e, seed⟩ := rfl

@[simp] theorem completedEquiv_source
    (e : Completed (t := t) clauses rows repeats hn hbranch hrows δ) :
    (completedEquiv (t := t) clauses rows repeats hn hbranch hrows δ e).1 = e.1.1.1 := rfl

theorem completedEquiv_symm_source
    (e : SignedCompleted (branch := branch) (n := n) (t := t) clauses rows repeats δ) :
    ((completedEquiv (t := t) clauses rows repeats hn hbranch hrows δ).symm e).1.1.1 = e.1 := by
  have h := congrArg Sigma.fst
    ((completedEquiv (t := t) clauses rows repeats hn hbranch hrows δ).apply_symm_apply e)
  exact h

theorem descriptorTable_eq_map
    (e : Completed (t := t) clauses rows repeats hn hbranch hrows δ)
    (a : Fin (2 * FinitePreliminaryCompletion.alphabet branch n t δ)) :
    SignedCompletionSchedule.descriptorTable (hq δ) (large δ)
        ⟨sourceSigns clauses (completedEquiv (t := t) clauses rows repeats hn hbranch hrows δ e).1,
          (completedEquiv (t := t) clauses rows repeats hn hbranch hrows δ e).2⟩ a =
      (FinitePreliminaryCompletion.actualFamily (t := t)
        clauses rows repeats hn hbranch hrows δ).map e.1 e.2 a := rfl

def law : FiniteDistribution
    (SignedCompleted (branch := branch) (n := n) (t := t) clauses rows repeats δ) :=
  sigmaLaw PreliminarySampler.questionsLaw (fun source =>
    SignedCompletionSchedule.law (rows := rows) (repeats := repeats)
      (hq δ) (large δ) hn hbranch hrows (sourceSigns clauses source))

theorem completed_weight (e : Completed (t := t) clauses rows repeats hn hbranch hrows δ) :
    (FinitePreliminaryCompletion.actualFamily (t := t)
      clauses rows repeats hn hbranch hrows δ).game.occurrences.weight e =
      (law (t := t) clauses rows repeats hn hbranch hrows δ).weight
        (completedEquiv (t := t) clauses rows repeats hn hbranch hrows δ e) := by
  rcases e with ⟨raw, seed⟩
  change (PreliminarySampler.law (t := t) clauses rows repeats hn hbranch hrows).weight raw *
      (1 / (Fintype.card (Fin ((FinitePreliminaryCompletion.actualFamily (t := t)
        clauses rows repeats hn hbranch hrows δ).size raw)) : ℝ)) =
    (1 / (Fintype.card (PreliminarySampler.Questions branch n t m) : ℝ)) *
      (SignedCompletionSchedule.law (rows := rows) (repeats := repeats)
        (hq δ) (large δ) hn hbranch hrows
        (sourceSigns clauses raw.1.1)).weight
          ⟨encodeOutcome clauses rows repeats raw, seed⟩
  rw [Fintype.card_fin, raw_weight_eq, SignedCompletionSchedule.law_weight]
  rw [size_eq_active (t := t) clauses rows repeats hn hbranch hrows δ raw]
  simp only [div_eq_mul_inv, one_mul, mul_assoc]

theorem actualcompletedLaw_transport :
    (FinitePreliminaryCompletion.actualFamily (t := t)
      clauses rows repeats hn hbranch hrows δ).game.occurrences.transport
        (completedEquiv (t := t) clauses rows repeats hn hbranch hrows δ) =
      sigmaLaw PreliminarySampler.questionsLaw (fun source =>
        SignedCompletionSchedule.law (rows := rows) (repeats := repeats)
          (hq δ) (large δ) hn hbranch hrows
          (sourceSigns clauses source)) := by
  apply FiniteDistribution.eq_of_weight_eq
  intro e
  change (FinitePreliminaryCompletion.actualFamily (t := t)
      clauses rows repeats hn hbranch hrows δ).game.occurrences.weight
      ((completedEquiv (t := t) clauses rows repeats hn hbranch hrows δ).symm e) =
    (law (t := t) clauses rows repeats hn hbranch hrows δ).weight e
  simpa only [Equiv.apply_symm_apply] using
    completed_weight (t := t) clauses rows repeats hn hbranch hrows δ
      ((completedEquiv (t := t) clauses rows repeats hn hbranch hrows δ).symm e)

theorem probability_reindex
    (event : SignedCompleted (branch := branch) (n := n) (t := t) clauses rows repeats δ → Bool) :
    (FinitePreliminaryCompletion.actualFamily (t := t)
      clauses rows repeats hn hbranch hrows δ).game.occurrences.probability
        (fun e => event (completedEquiv (t := t) clauses rows repeats hn hbranch hrows δ e)) =
      (law (t := t) clauses rows repeats hn hbranch hrows δ).probability event := by
  rw [← FiniteDistribution.probability_transport]
  rw [actualcompletedLaw_transport]
  rfl

theorem probability_eq
    (event : Completed (t := t) clauses rows repeats hn hbranch hrows δ → Bool) :
    (FinitePreliminaryCompletion.actualFamily (t := t)
      clauses rows repeats hn hbranch hrows δ).game.occurrences.probability event =
      (law (t := t) clauses rows repeats hn hbranch hrows δ).probability
        (fun e => event ((completedEquiv (t := t) clauses rows repeats hn hbranch hrows δ).symm e)) := by
  simpa only [Equiv.symm_apply_apply] using
    probability_reindex (t := t) clauses rows repeats hn hbranch hrows δ
      (fun e => event ((completedEquiv (t := t) clauses rows repeats hn hbranch hrows δ).symm e))

theorem probability_iterated
    (event : Completed (t := t) clauses rows repeats hn hbranch hrows δ → Bool) :
    (FinitePreliminaryCompletion.actualFamily (t := t)
      clauses rows repeats hn hbranch hrows δ).game.occurrences.probability event =
      PreliminarySampler.questionsLaw.expectation (fun source =>
        (SignedCompletionSchedule.law (rows := rows) (repeats := repeats)
          (hq δ) (large δ) hn hbranch hrows
          (sourceSigns clauses source)).probability (fun outcome =>
            event ((completedEquiv (t := t) clauses rows repeats hn hbranch hrows δ).symm
              ⟨source, outcome⟩))) := by
  rw [probability_eq]
  exact sigmaLaw_probability _ _ _

theorem probability_schedule
    (event : Completed (t := t) clauses rows repeats hn hbranch hrows δ → Bool) :
    (FinitePreliminaryCompletion.actualFamily (t := t)
      clauses rows repeats hn hbranch hrows δ).game.occurrences.probability event =
      PreliminarySampler.questionsLaw.expectation (fun source =>
        (((SignedCompletionSchedule.schedule (rows := rows) (repeats := repeats)
          (hq δ) (large δ) hn hbranch hrows
          (sourceSigns clauses source)).filter (fun outcome =>
            event ((completedEquiv (t := t) clauses rows repeats hn hbranch hrows δ).symm
              ⟨source, outcome⟩))).length : ℝ) /
          (SignedCompletionSchedule.schedule (rows := rows) (repeats := repeats)
            (hq δ) (large δ) hn hbranch hrows
            (sourceSigns clauses source)).length) := by
  rw [probability_iterated]
  congr 1
  funext source
  exact (SignedCompletionSchedule.schedule_acceptance (hq δ) (large δ) hn hbranch hrows
    (sourceSigns clauses source) (fun outcome =>
      event ((completedEquiv (t := t) clauses rows repeats hn hbranch hrows δ).symm
        ⟨source, outcome⟩))).symm

end
end PerfectCompleteness.CompletedSignedLaw

end

end OAI
