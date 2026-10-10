import OAI.Computability.PerfectCompleteness.Foundations.ExactConditionalOutput
import OAI.Computability.PerfectCompleteness.Foundations.RawOccurrenceOrderLemmas
import OAI.Computability.PerfectCompleteness.Machines.FiniteConstraintMachine

namespace OAI


namespace PerfectCompleteness.SignedCompletionSchedule


open MetadataFreeSampler MetadataFreeLaw
open UniqueGamesTheorem.Foundations.Games
open Turing UniqueGamesTheorem.Foundations.Complexity
open scoped BigOperators Classical

noncomputable section

variable {branch : Nat → Nat} {n t q : Nat} {rows repeats : Nat → Nat}
  (hq : 0 < q)
  (large : CanonicalKeyEncoding.partitionWidth (TreeCanonical.locationCount branch n t) ≤ q)

def result (signs : SignTuple branch n t) (e : SignedOutcome signs rows repeats) :
    LocalCompletionFamily.Result q := FiniteConstraintMachine.result hq large ⟨signs, e⟩

def active (signs : SignTuple branch n t) (e : SignedOutcome signs rows repeats) : Nat :=
  LocalCompletionFamily.activeCount (result (rows := rows) (repeats := repeats) hq large signs e)

theorem active_positive (signs : SignTuple branch n t) (e : SignedOutcome signs rows repeats) :
    0 < active (rows := rows) (repeats := repeats) hq large signs e := LocalCompletionFamily.activeCount_positive _

theorem active_le (signs : SignTuple branch n t) (e : SignedOutcome signs rows repeats) :
    active (rows := rows) (repeats := repeats) hq large signs e ≤ 2 * q := LocalCompletionFamily.activeCount_le _

abbrev Completed (signs : SignTuple branch n t) :=
  Σ e : SignedOutcome signs rows repeats, Fin (active (rows := rows) (repeats := repeats) hq large signs e)

abbrev Descriptor := Σ signs : SignTuple branch n t, Completed (rows := rows) (repeats := repeats) hq large signs

def descriptorTable (descriptor : Descriptor (rows := rows) (repeats := repeats) hq large) : Fin (2 * q) → Fin q :=
  LocalCompletionFamily.table (result (rows := rows) (repeats := repeats) hq large descriptor.1 descriptor.2.1) descriptor.2.2

theorem descriptorTable_eq_parsed (signs : SignTuple branch n t)
    (e : Completed (rows := rows) (repeats := repeats) hq large signs) (a : Fin (2 * q)) :
    descriptorTable (rows := rows) (repeats := repeats) hq large ⟨signs, e⟩ a =
      (LocalCompletionSerialization.projection
        (FiniteConstraintMachine.result_correct (rows := rows) (repeats := repeats) hq large ⟨signs, e.1⟩) e.2).images[a] :=
  (FiniteConstraintMachine.parsed_projection (rows := rows) (repeats := repeats) hq large ⟨signs, e.1⟩ e.2 a).symm

def seedLaw (signs : SignTuple branch n t) (e : SignedOutcome signs rows repeats) :
    FiniteDistribution (Fin (active (rows := rows) (repeats := repeats) hq large signs e)) := by
  letI : Nonempty (Fin (active (rows := rows) (repeats := repeats) hq large signs e)) := ⟨⟨0, active_positive (rows := rows) (repeats := repeats) hq large signs e⟩⟩
  exact FiniteDistribution.uniform _

variable (hn : 0 < n) (hbranch : ∀ k < n, 0 < branch k)
  (hrows : ∀ k, 0 < rows (k + 1))

def law (signs : SignTuple branch n t) : FiniteDistribution (Completed (rows := rows) (repeats := repeats) hq large signs) :=
  CompletionSoundness.sigmaLaw (signedLaw signs rows repeats hn hbranch hrows)
    (seedLaw (rows := rows) (repeats := repeats) hq large signs)

theorem law_weight (signs : SignTuple branch n t) (e : Completed (rows := rows) (repeats := repeats) hq large signs) :
    (law (rows := rows) (repeats := repeats) hq large hn hbranch hrows signs).weight e =
      (signedLaw signs rows repeats hn hbranch hrows).weight e.1 /
        active (rows := rows) (repeats := repeats) hq large signs e.1 := by
  change (signedLaw signs rows repeats hn hbranch hrows).weight e.1 *
    (1 / (Fintype.card (Fin (active (rows := rows) (repeats := repeats) hq large signs e.1)) : ℝ)) = _
  simp only [Fintype.card_fin, div_eq_mul_inv, one_mul]

def count (signs : SignTuple branch n t) (e : Completed (rows := rows) (repeats := repeats) hq large signs) : Nat :=
  ExactSeedMultiplicity.perSeed (2 * q) (active (rows := rows) (repeats := repeats) hq large signs e.1)
    (SignedMultiplicity.baseCopies branch n t rows repeats hn hbranch hrows signs e.1)

theorem count_positive (signs : SignTuple branch n t) (e : Completed (rows := rows) (repeats := repeats) hq large signs) :
    0 < count (rows := rows) (repeats := repeats) hq large hn hbranch hrows signs e :=
  ExactSeedMultiplicity.perSeed_positive (active_positive (rows := rows) (repeats := repeats) hq large signs e.1)
    (active_le (rows := rows) (repeats := repeats) hq large signs e.1)
    (SignedMultiplicity.baseCopies_positive branch n t rows repeats hn hbranch hrows signs e.1)

theorem count_total (signs : SignTuple branch n t) :
    (∑ e, count (rows := rows) (repeats := repeats) hq large hn hbranch hrows signs e) =
      SignedMultiplicity.denominator branch n t rows repeats hn hbranch hrows q :=
  ExactSeedMultiplicity.sum_multiplicity
    (SignedMultiplicity.baseCopies branch n t rows repeats hn hbranch hrows signs)
    (active (rows := rows) (repeats := repeats) hq large signs) (active_positive (rows := rows) (repeats := repeats) hq large signs) (active_le (rows := rows) (repeats := repeats) hq large signs)
    (SignedMultiplicity.baseCopies_total branch n t rows repeats hn hbranch hrows signs)

theorem count_ratio (signs : SignTuple branch n t) (e : Completed (rows := rows) (repeats := repeats) hq large signs) :
    (count (rows := rows) (repeats := repeats) hq large hn hbranch hrows signs e : ℚ) /
        SignedMultiplicity.denominator branch n t rows repeats hn hbranch hrows q =
      SignedMultiplicity.weights branch n t rows repeats hn hbranch hrows signs e.1 /
        active (rows := rows) (repeats := repeats) hq large signs e.1 := by
  change (ExactSeedMultiplicity.perSeed (2 * q) (active (rows := rows) (repeats := repeats) hq large signs e.1)
      (SignedMultiplicity.baseCopies branch n t rows repeats hn hbranch hrows signs e.1) : ℚ) /
    ExactSeedMultiplicity.denominator
      (SignedMultiplicity.baseDenominator branch n t rows repeats hn hbranch hrows) (2 * q) = _
  rw [ExactSeedMultiplicity.perSeed_ratio
    (SignedMultiplicity.baseDenominator_positive branch n t rows repeats hn hbranch hrows)
    (active_positive (rows := rows) (repeats := repeats) hq large signs e.1) (active_le (rows := rows) (repeats := repeats) hq large signs e.1),
    SignedMultiplicity.baseCopies_ratio]

theorem count_mass (signs : SignTuple branch n t) (e : Completed (rows := rows) (repeats := repeats) hq large signs) :
    (count (rows := rows) (repeats := repeats) hq large hn hbranch hrows signs e : ℝ) /
        SignedMultiplicity.denominator branch n t rows repeats hn hbranch hrows q =
      (law (rows := rows) (repeats := repeats) hq large hn hbranch hrows signs).weight e := by
  have h := congrArg (fun z : ℚ => (z : ℝ)) (count_ratio (rows := rows) (repeats := repeats) hq large hn hbranch hrows signs e)
  simp only [Rat.cast_div, Rat.cast_natCast] at h
  rw [law_weight, (signedRationalLaw signs rows repeats hn hbranch hrows).cast_weight]
  exact h

def schedule (signs : SignTuple branch n t) : List (Completed (rows := rows) (repeats := repeats) hq large signs) :=
  ExactConditionalOutput.copies (count (rows := rows) (repeats := repeats) hq large hn hbranch hrows) signs

theorem schedule_length (signs : SignTuple branch n t) :
    (schedule (rows := rows) (repeats := repeats) hq large hn hbranch hrows signs).length =
      SignedMultiplicity.denominator branch n t rows repeats hn hbranch hrows q := by
  rw [schedule, ExactConditionalOutput.copies_length, count_total]

theorem schedule_nonempty (signs : SignTuple branch n t) :
    schedule (rows := rows) (repeats := repeats) hq large hn hbranch hrows signs ≠ [] := by
  intro hempty
  have h := schedule_length (rows := rows) (repeats := repeats) hq large hn hbranch hrows signs
  rw [hempty, List.length_nil] at h
  exact (Nat.ne_of_gt
    (SignedMultiplicity.denominator_positive branch n t rows repeats hn hbranch hrows q)) h.symm

theorem schedule_acceptance (signs : SignTuple branch n t)
    (accepts : Completed (rows := rows) (repeats := repeats) hq large signs → Bool) :
    (((schedule (rows := rows) (repeats := repeats) hq large hn hbranch hrows signs).filter accepts).length : ℝ) /
        (schedule (rows := rows) (repeats := repeats) hq large hn hbranch hrows signs).length =
      (law (rows := rows) (repeats := repeats) hq large hn hbranch hrows signs).probability accepts := by
  rw [schedule_length]
  change (((ExactConditionalOutput.copies (count (rows := rows) (repeats := repeats) hq large hn hbranch hrows) signs).filter
    accepts).length : ℝ) / _ = _
  rw [ExactConditionalOutput.copies_filter_length, Nat.cast_sum, Finset.sum_div,
    FiniteDistribution.probability]
  apply Finset.sum_congr rfl
  intro e _
  cases accepts e <;> simp [count_mass]

def descriptorEnum : Descriptor (rows := rows) (repeats := repeats) hq large ≃ Fin (Fintype.card (Descriptor (rows := rows) (repeats := repeats) hq large)) :=
  Fintype.equivFin _

def descriptorBits (descriptor : Descriptor (rows := rows) (repeats := repeats) hq large) : List Bool :=
  FiniteBlockMachine.word (descriptorEnum (rows := rows) (repeats := repeats) hq large) descriptor

@[simp] theorem descriptorBits_length (descriptor : Descriptor (rows := rows) (repeats := repeats) hq large) :
    (descriptorBits (rows := rows) (repeats := repeats) hq large descriptor).length = Fintype.card (Descriptor (rows := rows) (repeats := repeats) hq large) :=
  FiniteBlockMachine.word_length _ _

def outputBits (signs : SignTuple branch n t) : List Bool :=
  (schedule (rows := rows) (repeats := repeats) hq large hn hbranch hrows signs).flatMap
    (fun e => descriptorBits (rows := rows) (repeats := repeats) hq large ⟨signs, e⟩)

def signsEnum (branch : Nat → Nat) (n t : Nat) :
    SignTuple branch n t ≃ Fin (Fintype.card (SignTuple branch n t)) := Fintype.equivFin _

def inputBits (signs : SignTuple branch n t) : List Bool :=
  FiniteBlockMachine.word (signsEnum branch n t) signs

def computation :
    TM2ComputableInPolyTime (inputBits (branch := branch) (n := n) (t := t))
      id (outputBits (rows := rows) (repeats := repeats) hq large hn hbranch hrows) :=
  FiniteWordMachine.computation (signsEnum branch n t) (fun _ _ => (false, false, false))
    (outputBits (rows := rows) (repeats := repeats) hq large hn hbranch hrows)

def machine_output (signs : SignTuple branch n t) :
    TM2OutputsInTime (computation (rows := rows) (repeats := repeats) hq large hn hbranch hrows).tm (inputBits signs)
      (some (outputBits (rows := rows) (repeats := repeats) hq large hn hbranch hrows signs)) 1 := by
  have h := (computation (rows := rows) (repeats := repeats) hq large hn hbranch hrows).outputsFun signs
  change TM2OutputsInTime (computation (rows := rows) (repeats := repeats) hq large hn hbranch hrows).tm
    ((inputBits signs).map id) (some ((outputBits (rows := rows) (repeats := repeats) hq large hn hbranch hrows signs).map id))
    ((1 : Polynomial Nat).eval _) at h
  rw [Polynomial.eval_one] at h
  exact Eq.mp (congrArg₂
    (fun (i o : List Bool) =>
      TM2OutputsInTime (computation (rows := rows) (repeats := repeats) hq large hn hbranch hrows).tm i (some o) 1)
    (List.map_id (inputBits signs))
    (List.map_id (outputBits (rows := rows) (repeats := repeats) hq large hn hbranch hrows signs))) h

theorem workAlphabet_finite (tape : (computation (rows := rows) (repeats := repeats) hq large hn hbranch hrows).tm.K) :
    Finite ((computation (rows := rows) (repeats := repeats) hq large hn hbranch hrows).tm.Γ tape) := by
  change Finite Bool
  infer_instance

end
end PerfectCompleteness.SignedCompletionSchedule

end OAI
