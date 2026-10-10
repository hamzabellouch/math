import OAI.Combinatorics.EditApproximation.Binary.BinaryReductionSpace
import OAI.Combinatorics.EditApproximation.Binary.BinaryScoreReads
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! Endpoint geometry and actual finite score/minimum scans retain
all arithmetic scratch and all callback read invocations. -/

namespace EditApproximation.BinaryFraction



theorem distanceAllocation_le_work (a b : BinaryFraction) :
    distanceAllocation a b ≤ (distanceWithWork a b).2 := by
  have h := subAllocation_le_work a b
  unfold distanceAllocation distanceWithWork
  dsimp only
  omega



theorem connectionTermsAllocation_le_work {n : ℕ} (start finish : BinaryFraction)
    (states : List (TargetInterval n)) :
    connectionTermsAllocation start states finish ≤ (connectionTermsWithWork start states finish).2 := by
  induction states generalizing start with
  | nil =>
    have h := distanceAllocation_le_work start finish
    unfold connectionTermsAllocation connectionTermsWithWork
    dsimp only
    exact Nat.add_le_add h (by decide : 1 ≤ 2)
  | cons state rest ih =>
    have hc := distanceAllocation_le_work start (nat state.lo)
    have ht := ih (nat state.hi)
    unfold connectionTermsAllocation connectionTermsWithWork
    dsimp only
    exact Nat.add_le_add
      (Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add hc ht) _) _)
      (by decide : 3 ≤ 6)



theorem connectionAllocation_le_work {n : ℕ} (start finish : BinaryFraction)
    (states : List (TargetInterval n)) :
    connectionAllocation start finish states ≤ (connectionWithWork start finish states).2 := by
  have ht := connectionTermsAllocation_le_work start finish states
  have hs := sumListAllocation_le_work (connectionTermsWithWork start states finish).1
  unfold connectionAllocation connectionWithWork
  dsimp only
  omega



theorem endpointDistanceAllocation_le_work {n : ℕ} (q r : TargetInterval n) :
    endpointDistanceAllocation q r ≤ (endpointDistanceWithWork q r).2 := by
  have hl := distanceAllocation_le_work (nat q.lo) (nat r.lo)
  have hr := distanceAllocation_le_work (nat q.hi) (nat r.hi)
  have ha := canonicalAddAllocation_le_work (distanceWithWork (nat q.lo) (nat r.lo)).1
    (distanceWithWork (nat q.hi) (nat r.hi)).1
  unfold endpointDistanceAllocation endpointDistanceWithWork
  dsimp only
  omega



theorem endpointConnectionAllocation_le_work {n M : ℕ} (r : TargetInterval n)
    (states : Fin M → TargetInterval n) :
    endpointConnectionAllocation r states ≤ (endpointConnectionWithWork r states).2 := by
  have h := connectionAllocation_le_work (nat r.lo) (nat r.hi) (List.ofFn states)
  unfold endpointConnectionAllocation endpointConnectionWithWork
  dsimp only
  omega



theorem stateGapAllocation_le_work {n : ℕ} (sourceLength : ℕ) (r : TargetInterval n) :
    stateGapAllocation sourceLength r ≤ (stateGapWithWork sourceLength r).2 := by
  have h1 := subAllocation_le_work (nat r.hi) (nat r.lo)
  have h2 := subAllocation_le_work (subWithWork (nat r.hi) (nat r.lo)).1 (nat sourceLength)
  unfold stateGapAllocation stateGapWithWork
  dsimp only
  omega



theorem endpointScoreReadAllocation_le_work {n M : ℕ} (r : TargetInterval n)
    (read : Fin M → TargetInterval n → BinaryFraction × ℕ)
    (footprint : Fin M → TargetInterval n → ℕ) (states : Fin M → TargetInterval n)
    (h : ∀ i, footprint i (states i) ≤ (read i (states i)).2) :
    endpointScoreReadAllocation r read footprint states ≤ (endpointScoreReadWithWork r read states).2 := by
  have hw := arithmeticMapAllocation_le_work (fun i => read i (states i))
    (fun i => footprint i (states i)) (List.finRange M) (fun i _ => h i)
  have hc := endpointConnectionAllocation_le_work r states
  let words := (arithmeticMapWithWork (fun i => read i (states i)) (List.finRange M)).1
  have hs := sumListAllocation_le_work words
  have ha := canonicalAddAllocation_le_work (endpointConnectionWithWork r states).1 (sumListWithWork words).1
  unfold endpointScoreReadAllocation endpointScoreReadWithWork
  dsimp only
  dsimp only [words] at hs ha
  omega



theorem wideMinimumReadAllocation_le_work {n M : ℕ} (r : TargetInterval n)
    (read : Fin M → TargetInterval n → BinaryFraction × ℕ)
    (footprint : Fin M → TargetInterval n → ℕ)
    (actions : List (Fin M → TargetInterval n)) (hne : actions ≠ [])
    (h : ∀ action ∈ actions, ∀ i, footprint i (action i) ≤ (read i (action i)).2) :
    wideMinimumReadAllocation r read footprint actions hne ≤ (wideMinimumReadWithWork r read actions hne).2 := by
  have hf := endpointScoreReadAllocation_le_work r read footprint (actions.head hne) (h _ (List.head_mem hne))
  have hs := arithmeticMapAllocation_le_work (endpointScoreReadWithWork r read)
    (endpointScoreReadAllocation r read footprint) actions
    (fun action ha => endpointScoreReadAllocation_le_work r read footprint action (h action ha))
  have hm := minimumAllocation_le_work (endpointScoreReadWithWork r read (actions.head hne)).1
    (arithmeticMapWithWork (endpointScoreReadWithWork r read) actions).1
  unfold wideMinimumReadAllocation wideMinimumReadWithWork
  dsimp only
  omega

def distanceInvocations (a b : BinaryFraction) : ℕ := subInvocations a b + 1

theorem distanceInvocations_le_work (a b : BinaryFraction) :
    distanceInvocations a b ≤ (distanceWithWork a b).2 := by
  have h := subInvocations_le_work a b
  unfold distanceInvocations distanceWithWork
  dsimp only
  omega

def connectionTermsInvocations {n : ℕ} (start : BinaryFraction) :
    List (TargetInterval n) → BinaryFraction → ℕ
  | [], finish => distanceInvocations start finish + 1
  | state :: rest, finish => distanceInvocations start (nat state.lo) +
    connectionTermsInvocations (nat state.hi) rest finish + 1

theorem connectionTermsInvocations_le_work {n : ℕ} (start finish : BinaryFraction)
    (states : List (TargetInterval n)) :
    connectionTermsInvocations start states finish ≤ (connectionTermsWithWork start states finish).2 := by
  induction states generalizing start with
  | nil =>
    have h := distanceInvocations_le_work start finish
    unfold connectionTermsInvocations connectionTermsWithWork
    dsimp only
    omega
  | cons state rest ih =>
    have hc := distanceInvocations_le_work start (nat state.lo)
    have ht := ih (nat state.hi)
    unfold connectionTermsInvocations connectionTermsWithWork
    dsimp only
    omega

def connectionInvocations {n : ℕ} (start finish : BinaryFraction)
    (states : List (TargetInterval n)) : ℕ :=
  connectionTermsInvocations start states finish +
    sumListInvocations (connectionTermsWithWork start states finish).1 + 1

theorem connectionInvocations_le_work {n : ℕ} (start finish : BinaryFraction)
    (states : List (TargetInterval n)) :
    connectionInvocations start finish states ≤ (connectionWithWork start finish states).2 := by
  have ht := connectionTermsInvocations_le_work start finish states
  have hs := sumListInvocations_le_work (connectionTermsWithWork start states finish).1
  unfold connectionInvocations connectionWithWork
  dsimp only
  omega

def endpointDistanceInvocations {n : ℕ} (q r : TargetInterval n) : ℕ :=
  distanceInvocations (nat q.lo) (nat r.lo) + distanceInvocations (nat q.hi) (nat r.hi) +
    canonicalAddInvocations (distanceWithWork (nat q.lo) (nat r.lo)).1
      (distanceWithWork (nat q.hi) (nat r.hi)).1 + 1

theorem endpointDistanceInvocations_le_work {n : ℕ} (q r : TargetInterval n) :
    endpointDistanceInvocations q r ≤ (endpointDistanceWithWork q r).2 := by
  have hl := distanceInvocations_le_work (nat q.lo) (nat r.lo)
  have hr := distanceInvocations_le_work (nat q.hi) (nat r.hi)
  have ha := canonicalAddInvocations_le_work (distanceWithWork (nat q.lo) (nat r.lo)).1
    (distanceWithWork (nat q.hi) (nat r.hi)).1
  unfold endpointDistanceInvocations endpointDistanceWithWork
  dsimp only
  omega

def endpointConnectionInvocations {n M : ℕ} (r : TargetInterval n)
    (states : Fin M → TargetInterval n) : ℕ :=
  connectionInvocations (nat r.lo) (nat r.hi) (List.ofFn states) + 1

theorem endpointConnectionInvocations_le_work {n M : ℕ} (r : TargetInterval n)
    (states : Fin M → TargetInterval n) :
    endpointConnectionInvocations r states ≤ (endpointConnectionWithWork r states).2 := by
  have h := connectionInvocations_le_work (nat r.lo) (nat r.hi) (List.ofFn states)
  unfold endpointConnectionInvocations endpointConnectionWithWork
  dsimp only
  omega

def stateGapInvocations {n : ℕ} (sourceLength : ℕ) (r : TargetInterval n) : ℕ :=
  subInvocations (nat r.hi) (nat r.lo) +
    subInvocations (subWithWork (nat r.hi) (nat r.lo)).1 (nat sourceLength) + 1

theorem stateGapInvocations_le_work {n : ℕ} (sourceLength : ℕ) (r : TargetInterval n) :
    stateGapInvocations sourceLength r ≤ (stateGapWithWork sourceLength r).2 := by
  have h1 := subInvocations_le_work (nat r.hi) (nat r.lo)
  have h2 := subInvocations_le_work (subWithWork (nat r.hi) (nat r.lo)).1 (nat sourceLength)
  unfold stateGapInvocations stateGapWithWork
  dsimp only
  omega

def endpointScoreReadInvocations {n M : ℕ} (r : TargetInterval n)
    (read : Fin M → TargetInterval n → BinaryFraction × ℕ)
    (footprint : Fin M → TargetInterval n → ℕ) (states : Fin M → TargetInterval n) : ℕ :=
  let words := (arithmeticMapWithWork (fun i => read i (states i)) (List.finRange M)).1
  arithmeticMapInvocations (fun i => footprint i (states i)) (List.finRange M) +
    endpointConnectionInvocations r states + sumListInvocations words +
    canonicalAddInvocations (endpointConnectionWithWork r states).1 (sumListWithWork words).1 + 1

theorem endpointScoreReadInvocations_le_work {n M : ℕ} (r : TargetInterval n)
    (read : Fin M → TargetInterval n → BinaryFraction × ℕ)
    (footprint : Fin M → TargetInterval n → ℕ) (states : Fin M → TargetInterval n)
    (h : ∀ i, footprint i (states i) ≤ (read i (states i)).2) :
    endpointScoreReadInvocations r read footprint states ≤ (endpointScoreReadWithWork r read states).2 := by
  have hw := arithmeticMapInvocations_le_work (fun i => read i (states i))
    (fun i => footprint i (states i)) (List.finRange M) (fun i _ => h i)
  have hc := endpointConnectionInvocations_le_work r states
  let words := (arithmeticMapWithWork (fun i => read i (states i)) (List.finRange M)).1
  have hs := sumListInvocations_le_work words
  have ha := canonicalAddInvocations_le_work (endpointConnectionWithWork r states).1 (sumListWithWork words).1
  unfold endpointScoreReadInvocations endpointScoreReadWithWork
  dsimp only
  dsimp only [words] at hs ha
  omega

def wideMinimumReadInvocations {n M : ℕ} (r : TargetInterval n)
    (read : Fin M → TargetInterval n → BinaryFraction × ℕ)
    (footprint : Fin M → TargetInterval n → ℕ)
    (actions : List (Fin M → TargetInterval n)) (hne : actions ≠ []) : ℕ :=
  let fallback := (endpointScoreReadWithWork r read (actions.head hne)).1
  let scores := (arithmeticMapWithWork (endpointScoreReadWithWork r read) actions).1
  endpointScoreReadInvocations r read footprint (actions.head hne) +
    arithmeticMapInvocations (endpointScoreReadInvocations r read footprint) actions +
    minimumInvocations fallback scores + 1

theorem wideMinimumReadInvocations_le_work {n M : ℕ} (r : TargetInterval n)
    (read : Fin M → TargetInterval n → BinaryFraction × ℕ)
    (footprint : Fin M → TargetInterval n → ℕ)
    (actions : List (Fin M → TargetInterval n)) (hne : actions ≠ [])
    (h : ∀ action ∈ actions, ∀ i, footprint i (action i) ≤ (read i (action i)).2) :
    wideMinimumReadInvocations r read footprint actions hne ≤ (wideMinimumReadWithWork r read actions hne).2 := by
  have hf := endpointScoreReadInvocations_le_work r read footprint (actions.head hne) (h _ (List.head_mem hne))
  have hs := arithmeticMapInvocations_le_work (endpointScoreReadWithWork r read)
    (endpointScoreReadInvocations r read footprint) actions
    (fun action ha => endpointScoreReadInvocations_le_work r read footprint action (h action ha))
  have hm := minimumInvocations_le_work (endpointScoreReadWithWork r read (actions.head hne)).1
    (arithmeticMapWithWork (endpointScoreReadWithWork r read) actions).1
  unfold wideMinimumReadInvocations wideMinimumReadWithWork
  dsimp only
  omega

end EditApproximation.BinaryFraction

end OAI
