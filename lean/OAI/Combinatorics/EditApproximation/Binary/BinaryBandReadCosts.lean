import OAI.Combinatorics.EditApproximation.Binary.BinaryReadCostBounds
import OAI.Combinatorics.EditApproximation.Binary.BinaryBandReads
import OAI.Combinatorics.EditApproximation.Binary.BinaryRoundedReads
import OAI.Combinatorics.EditApproximation.Binary.BinaryUnskippedReads

namespace OAI

/-! A finite-buffer lookup multiplies local band-loop work by a fixed
linear factor. Every comparison uses the same actual band and output. -/

namespace EditApproximation
namespace BinaryFraction

theorem wideMinimumReadWithWork_factor {n M : ℕ} (r : TargetInterval n)
    (read : Fin M → TargetInterval n → BinaryFraction × ℕ)
    (actions : List (Fin M → TargetInterval n)) (hne : actions ≠ [])
    (R : ℕ) (hr : ∀ action ∈ actions, ∀ i, (read i (action i)).2 ≤ R) :
    (wideMinimumReadWithWork r read actions hne).2 ≤
      (wideMinimumWithWork r (fun i q => (read i q).1) actions hne).2 * tableReadFactor R := by
  have hm := arithmeticMapWithWork_factor
    (endpointScoreReadWithWork r read) (endpointScoreWithWork r (fun i q => (read i q).1))
    actions (tableReadFactor R) (tableReadFactor_pos R)
    (fun action _ => endpointScoreReadWithWork_eq r read action)
    (fun action ha => endpointScoreReadWithWork_factor r read action R (hr action ha))
  have hf := endpointScoreReadWithWork_factor r read (actions.head hne) R
    (hr _ (List.head_mem hne))
  have hc := Nat.add_le_add hf hm.2
  rw [← Nat.add_mul] at hc
  apply cost_replace_factor _ _ _ _ _ hc (tableReadFactor_pos R)
  · unfold wideMinimumWithWork
    dsimp only
    omega
  · unfold wideMinimumReadWithWork wideMinimumWithWork
    dsimp only
    rw [hm.1, endpointScoreReadWithWork_eq]
    omega

theorem prefixMinimumReadWithWork_factor {nx n M : ℕ} (parent : TargetInterval nx)
    (r : TargetInterval n) (actions : List (Fin M → TargetInterval n)) (hne : actions ≠ [])
    (read : Fin M → TargetInterval n → BinaryFraction × ℕ) (j : ℕ) (p : BinaryFraction)
    (R : ℕ) (hr : ∀ action ∈ actions, ∀ i, (read i (action i)).2 ≤ R) :
    (prefixMinimumReadWithWork parent r actions hne read j p).2 ≤
      (prefixMinimumWithWork parent r actions hne (fun i q => (read i q).1) j p).2 *
        tableReadFactor R := by
  have hm := arithmeticMapWithWork_factor
    (fun action => prefixReadWithWork parent r action read j p)
    (fun action => prefixWithWork parent r action (fun i q => (read i q).1) j p)
    actions (tableReadFactor R) (tableReadFactor_pos R)
    (fun action _ => prefixReadWithWork_eq parent r action read j p)
    (fun action ha => prefixReadWithWork_factor parent r action read j p R (hr action ha))
  have hf := prefixReadWithWork_factor parent r (actions.head hne) read j p R
    (hr _ (List.head_mem hne))
  have hc := Nat.add_le_add hf hm.2
  rw [← Nat.add_mul] at hc
  apply cost_replace_factor _ _ _ _ _ hc (tableReadFactor_pos R)
  · unfold prefixMinimumWithWork
    dsimp only
    omega
  · unfold prefixMinimumReadWithWork prefixMinimumWithWork
    dsimp only
    rw [hm.1, prefixReadWithWork_eq]
    omega

theorem cutGuardReadWithWork_factor {nx n M : ℕ} (parent : TargetInterval nx)
    (r : TargetInterval n) (actions : List (Fin M → TargetInterval n)) (hne : actions ≠ [])
    (read : Fin M → TargetInterval n → BinaryFraction × ℕ) (states : Fin M → TargetInterval n)
    (velocity tolerance : BinaryFraction) (j : Fin M) (R : ℕ)
    (hr : ∀ action ∈ actions, ∀ i, (read i (action i)).2 ≤ R) :
    (cutGuardReadWithWork parent r actions hne read states velocity tolerance j).2 ≤
      (cutGuardWithWork parent r actions hne (fun i q => (read i q).1) states velocity tolerance j).2 *
        tableReadFactor R := by
  unfold cutGuardReadWithWork cutGuardWithWork
  split_ifs
  · simpa only [Nat.one_mul] using tableReadFactor_pos R
  · have h := prefixMinimumReadWithWork_factor parent r actions hne read j.val
      (subWithWork (nat (states j).lo) (nat (sourceChild parent j).lo)).1 R hr
    dsimp only
    rw [prefixMinimumReadWithWork_eq]
    apply cost_replace_factor _ _ _ _ _ h (tableReadFactor_pos R)
    · omega
    · omega

theorem bandPredicateReadWithWork_factor {nx n M : ℕ} (parent : TargetInterval nx)
    (r : TargetInterval n) (b : ℕ) (tau theta velocity : BinaryFraction)
    (actions : List (Fin M → TargetInterval n)) (hne : actions ≠ [])
    (read : Fin M → TargetInterval n → BinaryFraction × ℕ) (states : Fin M → TargetInterval n)
    (R : ℕ) (hr : ∀ action ∈ actions, ∀ i, (read i (action i)).2 ≤ R) :
    (bandPredicateReadWithWork parent r b tau theta velocity actions hne read states).2 ≤
      (bandPredicateWithWork parent r b tau theta velocity actions hne (fun i q => (read i q).1) states).2 *
        tableReadFactor R := by
  have hc := allWithWork_factor
    (cutGuardReadWithWork parent r actions hne read states velocity (bandToleranceWithWork tau theta b M).1)
    (cutGuardWithWork parent r actions hne (fun i q => (read i q).1) states velocity
      (bandToleranceWithWork tau theta b M).1)
    (List.finRange M) (tableReadFactor R) (tableReadFactor_pos R)
    (fun j _ => cutGuardReadWithWork_eq parent r actions hne read states velocity _ j)
    (fun j _ => cutGuardReadWithWork_factor parent r actions hne read states velocity _ j R hr)
  apply cost_replace_factor _ _ _ _ _ hc.2 (tableReadFactor_pos R)
  · unfold bandPredicateWithWork
    dsimp only
    omega
  · unfold bandPredicateReadWithWork bandPredicateWithWork
    dsimp only
    omega

theorem bandFromActionsReadWithWork_factor {nx n M : ℕ} (parent : TargetInterval nx)
    (r : TargetInterval n) (b : ℕ) (tau theta velocity : BinaryFraction)
    (read : Fin M → TargetInterval n → BinaryFraction × ℕ)
    (actions : List (Fin M → TargetInterval n)) (hne : actions ≠ [])
    (R : ℕ) (hr : ∀ action ∈ actions, ∀ i, (read i (action i)).2 ≤ R) :
    (bandFromActionsReadWithWork parent r b tau theta velocity read actions hne).2 ≤
      (bandFromActionsWithWork parent r b tau theta velocity (fun i q => (read i q).1) actions hne).2 *
        tableReadFactor R := by
  have hf := filterWithWork_factor
    (bandPredicateReadWithWork parent r b tau theta velocity actions hne read)
    (bandPredicateWithWork parent r b tau theta velocity actions hne (fun i q => (read i q).1))
    actions (tableReadFactor R) (tableReadFactor_pos R)
    (fun action _ => (bandPredicateReadWithWork_eq_cost parent r b tau theta velocity actions hne
      read action R hr).1)
    (fun action _ => bandPredicateReadWithWork_factor parent r b tau theta velocity actions hne
      read action R hr)
  unfold bandFromActionsReadWithWork bandFromActionsWithWork
  dsimp only
  split_ifs
  · apply cost_replace_factor _ _ _ _ _ hf.2 (tableReadFactor_pos R)
    · omega
    · omega
  · exact Nat.le_mul_of_pos_right _ (by have := tableReadFactor_pos R; omega)

theorem representativeFromActionsReadWithWork_factor {nx n M : ℕ} (parent : TargetInterval nx)
    (r : TargetInterval n) (sourceLength b : ℕ) (tau theta : BinaryFraction)
    (read : Fin M → TargetInterval n → BinaryFraction × ℕ)
    (actions : List (Fin M → TargetInterval n)) (R : ℕ)
    (hr : ∀ action ∈ actions, ∀ i, (read i (action i)).2 ≤ R) :
    (representativeFromActionsReadWithWork parent r sourceLength b tau theta read actions).2 ≤
      (representativeFromActionsWithWork parent r sourceLength b tau theta
        (fun i q => (read i q).1) actions).2 * tableReadFactor R := by
  unfold representativeFromActionsReadWithWork representativeFromActionsWithWork
  by_cases hne : actions = []
  · simp only [dite_eq_left hne]
    simpa only [Nat.one_mul] using tableReadFactor_pos R
  · simp only [dite_eq_right hne]
    have hz := wideMinimumReadWithWork_factor r read actions hne R hr
    rw [wideMinimumReadWithWork_eq]
    split_ifs
    · have hb := bandFromActionsReadWithWork_factor parent r b tau theta
        (divWithWork (stateGapWithWork sourceLength r).1
          (wideMinimumWithWork r (fun i q => (read i q).1) actions hne).1).1 read actions hne R hr
      have hc := Nat.add_le_add hz hb
      rw [← Nat.add_mul] at hc
      apply cost_replace_factor _ _ _ _ _ hc (tableReadFactor_pos R) <;> omega
    · apply cost_replace_factor _ _ _ _ _ hz (tableReadFactor_pos R) <;> omega

theorem preparedRepresentativeReadWithWork_factor {nx n M : ℕ} (parent : TargetInterval nx)
    (r : TargetInterval n) (sourceLength b P : ℕ) (tau theta : BinaryFraction)
    (read : Fin M → TargetInterval n → BinaryFraction × ℕ) (R : ℕ)
    (hr : ∀ i q, (read i q).2 ≤ R) :
    (preparedRepresentativeReadWithWork parent r sourceLength b P tau theta read).2 ≤
      (preparedRepresentativeWithWork parent r sourceLength b P tau theta
        (fun i q => (read i q).1)).2 * tableReadFactor R := by
  have h := representativeFromActionsReadWithWork_factor parent r sourceLength b tau theta read
    ((wideActionGridWithWork M parent r b P).1.map Vector.get) R (fun _ _ i => hr i _)
  unfold preparedRepresentativeReadWithWork preparedRepresentativeWithWork
  dsimp only
  apply cost_replace_factor _ _ _ _ _ h (tableReadFactor_pos R) <;> omega

theorem envelopeVectorReadWithWork_factor {n M : ℕ} (b : ℕ)
    (band : List (Fin M → TargetInterval n))
    (read : Fin M → TargetInterval n → BinaryFraction × ℕ) (R : ℕ)
    (hr : ∀ i q, (read i q).2 ≤ R) :
    (envelopeVectorReadWithWork b band read).2 ≤
      (envelopeVectorWithWork b band (fun i q => (read i q).1)).2 * tableReadFactor R := by
  exact (vectorMapWithWork_factor M
    (bandEnvelopeReadWithWork b band read)
    (bandEnvelopeWithWork b band (fun i q => (read i q).1))
    (tableReadFactor R) (tableReadFactor_pos R)
    (fun i => bandEnvelopeReadWithWork_eq b band read i)
    (fun i => bandEnvelopeReadWithWork_factor b band read i R (fun _ _ => hr i _))).2

theorem roundedBandReadWithWork_factor {n M : ℕ} (exponent b : ℕ)
    (band : List (Fin M → TargetInterval n)) (hne : band ≠ [])
    (read : Fin M → TargetInterval n → BinaryFraction × ℕ) (R : ℕ)
    (hr : ∀ i q, (read i q).2 ≤ R) :
    (roundedBandReadWithWork exponent b band hne read).2 ≤
      (roundedBandWithWork exponent b band hne (fun i q => (read i q).1)).2 * tableReadFactor R := by
  apply (vectorMapWithWork_factor M _ _ (tableReadFactor R) (tableReadFactor_pos R) ?_ ?_).2
  · intro i
    simp only [bandEnvelopeReadWithWork_eq]
  · intro i
    have h := bandEnvelopeReadWithWork_factor b band read i R (fun _ _ => hr i _)
    dsimp only
    simp only [bandEnvelopeReadWithWork_eq]
    apply cost_replace_factor _ _ _ _ _ h (tableReadFactor_pos R) <;> omega

theorem unskippedGuardReadWithWork_factor {nx n M : ℕ} (parent : TargetInterval nx)
    (r : TargetInterval n) (b exponent : ℕ) (F : BinaryFraction)
    (band wide : List (Fin M → TargetInterval n)) (hne : band ≠ [])
    (read : Fin M → TargetInterval n → BinaryFraction × ℕ) (R : ℕ)
    (hr : ∀ i q, (read i q).2 ≤ R) :
    (unskippedGuardReadWithWork parent r b exponent F band wide hne read).2 ≤
      (unskippedGuardWithWork parent r b exponent F band wide hne
        (fun i q => (read i q).1)).2 * tableReadFactor R := by
  have he := envelopeVectorReadWithWork_factor b band read R hr
  have heq := (envelopeVectorReadWithWork_eq_cost b band read R hr).1
  have hrnd := roundedBandReadWithWork_factor exponent b band hne read R hr
  have hrndq := (roundedBandReadWithWork_eq_cost exponent b band hne read R hr).1
  have h := Nat.add_le_add he hrnd
  rw [← Nat.add_mul] at h
  unfold unskippedGuardReadWithWork unskippedGuardWithWork
  dsimp only
  rw [heq, hrndq]
  apply cost_replace_factor _ _ _ _ _ h (tableReadFactor_pos R) <;> omega

theorem preparedUnskippedReadWithWork_factor {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (b P exponent : ℕ) (hb : 0 < b) (hP : 0 < P)
    (tau F : BinaryFraction)
    (read initial : Fin M → TargetInterval target.length → BinaryFraction × ℕ)
    (R : ℕ) (hr : ∀ i q, (read i q).2 ≤ R) (hi : ∀ i q, (initial i q).2 ≤ R)
    (center : TargetInterval target.length) :
    (preparedUnskippedReadWithWork source target parent b P exponent hb hP tau F
      read initial R R hr hi center).2 ≤
      (preparedUnskippedCandidateWithWork source target parent b P exponent hb hP tau F
        (fun i q => (read i q).1) (fun i q => (initial i q).1) center).2 * tableReadFactor R := by
  have hband := preparedRepresentativeReadWithWork_factor parent center (parent.hi - parent.lo)
    b P tau (inversePowerTwo exponent) read R hr
  have hbandq := (preparedRepresentativeReadWithWork_eq_cost parent center (parent.hi - parent.lo)
    b P tau (inversePowerTwo exponent) read R hr).1
  unfold preparedUnskippedReadWithWork preparedUnskippedCandidateWithWork
  dsimp only
  simp only [hbandq]
  by_cases hempty : (preparedRepresentativeWithWork parent center (parent.hi - parent.lo)
      b P tau (inversePowerTwo exponent) (fun i q => (read i q).1)).1 = []
  · simp only [dite_eq_left hempty]
    apply cost_replace_factor _ _ _ _ _ hband (tableReadFactor_pos R) <;> omega
  · simp only [dite_eq_right hempty]
    have hg := unskippedGuardReadWithWork_factor parent center b exponent F
      (preparedRepresentativeWithWork parent center (parent.hi - parent.lo) b P
        tau (inversePowerTwo exponent) (fun i q => (read i q).1)).1
      ((wideActionGridWithWork M parent center b P).1.map Vector.get) hempty initial R hi
    have hgq := (unskippedGuardReadWithWork_eq_cost parent center b exponent F
      (preparedRepresentativeWithWork parent center (parent.hi - parent.lo) b P
        tau (inversePowerTwo exponent) (fun i q => (read i q).1)).1
      ((wideActionGridWithWork M parent center b P).1.map Vector.get) hempty initial R hi).1
    simp only [hgq]
    have h := Nat.add_le_add hband hg
    rw [← Nat.add_mul] at h
    split_ifs <;> apply cost_replace_factor _ _ _ _ _ h (tableReadFactor_pos R) <;> omega

end BinaryFraction
end EditApproximation

end OAI
