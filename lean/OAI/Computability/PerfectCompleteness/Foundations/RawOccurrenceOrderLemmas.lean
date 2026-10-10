import Mathlib.Data.List.Nodup
import Mathlib.Data.List.ProdSigma
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import OAI.Computability.PerfectCompleteness.Construction.SourceQuestionOrderLemmas
import OAI.Computability.PerfectCompleteness.Foundations.DummyEliminationLemmas
import OAI.Computability.PerfectCompleteness.Sampling.MetadataFreeLaw

namespace OAI


namespace PerfectCompleteness.RawOccurrenceOrder

open MetadataFreeSampler MetadataFreeLaw
open scoped BigOperators Classical

noncomputable section

variable {branch : Nat → Nat} {n t v m : Nat}

def signedOrder (signs : SignTuple branch n t) (rows repeats : Nat → Nat) :
    List (SignedOutcome signs rows repeats) :=
  List.ofFn (Fintype.equivFin (SignedOutcome signs rows repeats)).symm

@[simp] theorem signedOrder_length (signs : SignTuple branch n t) (rows repeats : Nat → Nat) :
    (signedOrder signs rows repeats).length = Fintype.card (SignedOutcome signs rows repeats) := by
  simp only [signedOrder, List.length_ofFn]

theorem signedOrder_nodup (signs : SignTuple branch n t) (rows repeats : Nat → Nat) :
    (signedOrder signs rows repeats).Nodup :=
  List.nodup_ofFn.mpr (Fintype.equivFin (SignedOutcome signs rows repeats)).symm.injective

theorem mem_signedOrder (signs : SignTuple branch n t) (rows repeats : Nat → Nat)
    (outcome : SignedOutcome signs rows repeats) : outcome ∈ signedOrder signs rows repeats := by
  apply List.mem_ofFn.mpr
  exact ⟨Fintype.equivFin _ outcome, Equiv.symm_apply_apply _ _⟩

def rawOrder (clauses : Fin m → SourceClause.NormalizedClause v)
    (branch : Nat → Nat) (n t : Nat) (rows repeats : Nat → Nat) :
    List (PreliminarySampler.Raw clauses branch n t rows repeats) :=
  (SourceQuestionOrder.sourceOrder branch n t m).flatMap fun source =>
    (signedOrder (sourceSigns clauses source) rows repeats).map fun outcome =>
      (rawEquiv clauses rows repeats).symm ⟨source, outcome⟩

theorem mem_rawOrder (clauses : Fin m → SourceClause.NormalizedClause v)
    (branch : Nat → Nat) (n t : Nat) (rows repeats : Nat → Nat)
    (e : PreliminarySampler.Raw clauses branch n t rows repeats) :
    e ∈ rawOrder clauses branch n t rows repeats := by
  apply List.mem_flatMap.mpr
  refine ⟨e.1.1, SourceQuestionOrder.mem_sourceOrder e.1.1, ?_⟩
  apply List.mem_map.mpr
  refine ⟨encodeOutcome clauses rows repeats e,
    mem_signedOrder _ rows repeats (encodeOutcome clauses rows repeats e), ?_⟩
  exact (rawEquiv clauses rows repeats).symm_apply_apply e

theorem rawOrder_eq_map_sigma (clauses : Fin m → SourceClause.NormalizedClause v)
    (branch : Nat → Nat) (n t : Nat) (rows repeats : Nat → Nat) :
    rawOrder clauses branch n t rows repeats =
      ((SourceQuestionOrder.sourceOrder branch n t m).sigma
        (fun source => signedOrder (sourceSigns clauses source) rows repeats)).map
          (rawEquiv clauses rows repeats).symm := by
  simp only [rawOrder, List.sigma, List.map_flatMap, List.map_map, Function.comp_def]

theorem rawOrder_nodup (clauses : Fin m → SourceClause.NormalizedClause v)
    (branch : Nat → Nat) (n t : Nat) (rows repeats : Nat → Nat) :
    (rawOrder clauses branch n t rows repeats).Nodup := by
  rw [rawOrder_eq_map_sigma]
  apply List.Nodup.map (rawEquiv clauses rows repeats).symm.injective
  exact (SourceQuestionOrder.sourceOrder_nodup branch n t m).sigma
    (fun source => signedOrder_nodup (sourceSigns clauses source) rows repeats)

theorem rawOrder_length (clauses : Fin m → SourceClause.NormalizedClause v)
    (branch : Nat → Nat) (n t : Nat) (rows repeats : Nat → Nat) :
    (rawOrder clauses branch n t rows repeats).length =
      ∑ source : PreliminarySampler.Questions branch n t m,
        Fintype.card (SignedOutcome (sourceSigns clauses source) rows repeats) := by
  simp only [rawOrder, List.length_flatMap, List.length_map, signedOrder_length]
  exact SourceQuestionOrder.sum_map_sourceOrder _

def fiberBound (branch : Nat → Nat) (n t : Nat) (rows repeats : Nat → Nat) : Nat :=
  ∑ signs : SignTuple branch n t, Fintype.card (SignedOutcome signs rows repeats)

theorem signed_card_le_fiberBound (signs : SignTuple branch n t) (rows repeats : Nat → Nat) :
    Fintype.card (SignedOutcome signs rows repeats) ≤ fiberBound branch n t rows repeats := by
  unfold fiberBound
  exact Finset.single_le_sum
    (fun signs _ => Nat.zero_le (Fintype.card (SignedOutcome signs rows repeats)))
    (Finset.mem_univ signs)

theorem rawOrder_length_le (clauses : Fin m → SourceClause.NormalizedClause v)
    (branch : Nat → Nat) (n t : Nat) (rows repeats : Nat → Nat) :
    (rawOrder clauses branch n t rows repeats).length ≤
      fiberBound branch n t rows repeats * m ^ TreeCanonical.locationCount branch n t := by
  rw [rawOrder_length]
  calc
    (∑ source : PreliminarySampler.Questions branch n t m,
        Fintype.card (SignedOutcome (sourceSigns clauses source) rows repeats)) ≤
        ∑ _source : PreliminarySampler.Questions branch n t m,
          fiberBound branch n t rows repeats :=
      Finset.sum_le_sum (fun source _ => signed_card_le_fiberBound
        (sourceSigns clauses source) rows repeats)
    _ = fiberBound branch n t rows repeats * m ^ TreeCanonical.locationCount branch n t := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        Fintype.card_congr (SourceQuestionOrder.questionTupleEquiv branch n t m)]
      simp only [Fintype.card_fun, Fintype.card_fin, Nat.cast_id, Nat.mul_comm]

end

end PerfectCompleteness.RawOccurrenceOrder


namespace PerfectCompleteness.SignedMultiplicity

open RecursiveSpaces MetadataFreeSampler MetadataFreeLaw
open UniqueGamesTheorem.Foundations.Games
open scoped BigOperators Classical

noncomputable section

variable (branch : Nat → Nat) (n t : Nat) (rows repeats : Nat → Nat)
    (hn : 0 < n) (hbranch : ∀ k < n, 0 < branch k) (hrows : ∀ k, 0 < rows (k + 1))

def weights (signs : SignTuple branch n t) : SignedOutcome signs rows repeats → ℚ :=
  (signedRationalLaw signs rows repeats hn hbranch hrows).weights

theorem weights_positive (signs : SignTuple branch n t) (e : SignedOutcome signs rows repeats) :
    0 < weights branch n t rows repeats hn hbranch hrows signs e :=
  (signedRationalLaw signs rows repeats hn hbranch hrows).positive e

theorem weights_total (signs : SignTuple branch n t) :
    (∑ e, weights branch n t rows repeats hn hbranch hrows signs e) = 1 :=
  (signedRationalLaw signs rows repeats hn hbranch hrows).total

def baseDenominator : Nat :=
  ExactRationalMultiplicity.commonDenominator (weights branch n t rows repeats hn hbranch hrows)

def baseCopies (signs : SignTuple branch n t) (e : SignedOutcome signs rows repeats) : Nat :=
  ExactRationalMultiplicity.multiplicity (weights branch n t rows repeats hn hbranch hrows) signs e

theorem baseDenominator_positive : 0 < baseDenominator branch n t rows repeats hn hbranch hrows :=
  ExactRationalMultiplicity.commonDenominator_pos _

theorem baseCopies_positive (signs : SignTuple branch n t) (e : SignedOutcome signs rows repeats) :
    0 < baseCopies branch n t rows repeats hn hbranch hrows signs e :=
  ExactRationalMultiplicity.multiplicity_pos _
    (weights_positive branch n t rows repeats hn hbranch hrows) signs e

theorem baseCopies_total (signs : SignTuple branch n t) :
    (∑ e, baseCopies branch n t rows repeats hn hbranch hrows signs e) =
      baseDenominator branch n t rows repeats hn hbranch hrows :=
  ExactRationalMultiplicity.multiplicity_sum _
    (weights_positive branch n t rows repeats hn hbranch hrows)
    (weights_total branch n t rows repeats hn hbranch hrows) signs

theorem baseCopies_ratio (signs : SignTuple branch n t) (e : SignedOutcome signs rows repeats) :
    (baseCopies branch n t rows repeats hn hbranch hrows signs e : ℚ) /
        baseDenominator branch n t rows repeats hn hbranch hrows =
      weights branch n t rows repeats hn hbranch hrows signs e :=
  ExactRationalMultiplicity.multiplicity_div _
    (weights_positive branch n t rows repeats hn hbranch hrows) signs e

def denominator (q : Nat) : Nat :=
  ExactSeedMultiplicity.denominator (baseDenominator branch n t rows repeats hn hbranch hrows) (2 * q)

theorem denominator_positive (q : Nat) :
    0 < denominator branch n t rows repeats hn hbranch hrows q :=
  ExactSeedMultiplicity.denominator_positive
    (baseDenominator_positive branch n t rows repeats hn hbranch hrows) (2 * q)

variable {v m : Nat} (clauses : Fin m → SourceClause.NormalizedClause v)

def rawCopies (e : PreliminarySampler.Raw clauses branch n t rows repeats) : Nat :=
  baseCopies branch n t rows repeats hn hbranch hrows (sourceSigns clauses e.1.1)
    (encodeOutcome clauses rows repeats e)

theorem rawCopies_total :
    (∑ e, rawCopies branch n t rows repeats hn hbranch hrows clauses e) =
      Fintype.card (PreliminarySampler.Questions branch n t m) *
        baseDenominator branch n t rows repeats hn hbranch hrows := by
  let f : (Σ source : PreliminarySampler.Questions branch n t m,
      SignedOutcome (sourceSigns clauses source) rows repeats) → Nat :=
    fun e => baseCopies branch n t rows repeats hn hbranch hrows
      (sourceSigns clauses e.1) e.2
  have hreindex := (rawEquiv (t := t) clauses rows repeats).sum_comp f
  change (∑ e, f (rawEquiv clauses rows repeats e)) = _
  rw [hreindex, Fintype.sum_sigma]
  simp only [f, baseCopies_total, Finset.sum_const, Finset.card_univ, Nat.nsmul_eq_mul]

variable {q : Nat}
    (count : PreliminarySampler.Raw clauses branch n t rows repeats → Nat)
    (positive : ∀ e, 0 < count e) (bounded : ∀ e, count e ≤ 2 * q)

def completedCopies (e : ExactSeedMultiplicity.Seeded count) : Nat :=
  ExactSeedMultiplicity.perSeed (2 * q) (count e.1)
    (rawCopies branch n t rows repeats hn hbranch hrows clauses e.1)

include positive bounded

theorem completedCopies_positive (e : ExactSeedMultiplicity.Seeded count) :
    0 < completedCopies (q := q) branch n t rows repeats hn hbranch hrows clauses count e :=
  ExactSeedMultiplicity.perSeed_positive (positive e.1) (bounded e.1)
    (baseCopies_positive branch n t rows repeats hn hbranch hrows _ _)

theorem completedCopies_total :
    (∑ e, completedCopies (q := q) branch n t rows repeats hn hbranch hrows clauses count e) =
      Fintype.card (PreliminarySampler.Questions branch n t m) *
        denominator branch n t rows repeats hn hbranch hrows q := by
  have h := ExactSeedMultiplicity.sum_multiplicity
    (rawCopies branch n t rows repeats hn hbranch hrows clauses) count positive bounded
    (rawCopies_total branch n t rows repeats hn hbranch hrows clauses)
  change (∑ e, completedCopies (q := q) branch n t rows repeats hn hbranch hrows clauses count e) =
    (Fintype.card (PreliminarySampler.Questions branch n t m) *
      baseDenominator branch n t rows repeats hn hbranch hrows) *
      ExactSeedMultiplicity.factor (2 * q) at h
  exact h.trans (Nat.mul_assoc _ _ _)

theorem completedCopies_polynomial_total :
    (∑ e, completedCopies (q := q) branch n t rows repeats hn hbranch hrows clauses count e) =
      denominator branch n t rows repeats hn hbranch hrows q *
        m ^ (t * Fintype.card (Slots branch n)) := by
  rw [completedCopies_total branch n t rows repeats hn hbranch hrows clauses count positive bounded,
    Fintype.card_eq_nat_card, TreeCardinality.source_questions_card]
  exact Nat.mul_comm _ _

theorem completedCopies_conditional_ratio (e : ExactSeedMultiplicity.Seeded count) :
    (completedCopies (q := q) branch n t rows repeats hn hbranch hrows clauses count e : ℚ) /
        denominator branch n t rows repeats hn hbranch hrows q =
      weights branch n t rows repeats hn hbranch hrows (sourceSigns clauses e.1.1.1)
        (encodeOutcome clauses rows repeats e.1) / count e.1 := by
  change (ExactSeedMultiplicity.perSeed (2 * q) (count e.1)
      (rawCopies branch n t rows repeats hn hbranch hrows clauses e.1) : ℚ) /
    ExactSeedMultiplicity.denominator
      (baseDenominator branch n t rows repeats hn hbranch hrows) (2 * q) = _
  rw [ExactSeedMultiplicity.perSeed_ratio
    (baseDenominator_positive branch n t rows repeats hn hbranch hrows)
    (positive e.1) (bounded e.1)]
  change ((baseCopies branch n t rows repeats hn hbranch hrows
    (sourceSigns clauses e.1.1.1) (encodeOutcome clauses rows repeats e.1) : ℚ) / _) / _ = _
  rw [baseCopies_ratio]

theorem completedCopies_mass [NeZero m] (e : ExactSeedMultiplicity.Seeded count) :
    (completedCopies (q := q) branch n t rows repeats hn hbranch hrows clauses count e : ℝ) /
        (Fintype.card (PreliminarySampler.Questions branch n t m) *
          denominator branch n t rows repeats hn hbranch hrows q : Nat) =
      (PreliminarySampler.law clauses rows repeats hn hbranch hrows).weight e.1 /
        count e.1 := by
  have h := congrArg (fun x : ℚ => (x : ℝ))
    (completedCopies_conditional_ratio branch n t rows repeats hn hbranch hrows
      clauses count positive bounded e)
  simp only [Rat.cast_div, Rat.cast_natCast] at h
  rw [raw_weight_rational clauses rows repeats hn hbranch hrows e.1]
  change (_ : ℝ) = (1 / _) *
    (weights branch n t rows repeats hn hbranch hrows (sourceSigns clauses e.1.1.1)
      (encodeOutcome clauses rows repeats e.1) : ℝ) / _
  rw [Nat.cast_mul, mul_comm
    (Fintype.card (PreliminarySampler.Questions branch n t m) : ℝ), ← div_div, h]
  ring

end
end PerfectCompleteness.SignedMultiplicity

end OAI
