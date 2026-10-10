import OAI.Combinatorics.EditApproximation.Binary.BinaryRepresentativeKernel
import OAI.Combinatorics.EditApproximation.Geometry.PrefixBitEnvelope

namespace OAI

/-! Bounds for the executed representative scores and velocity. They use
only the widths of actual stored inputs, and apply on every seed. -/

namespace EditApproximation
namespace BinaryFraction

open Finset

def endpointDistanceWordBudget (B : ℕ) : ℕ := 64 * B + 54

def endpointDistanceBitBudget (B : ℕ) : ℕ :=
  2 * (6000 * (B + 1) ^ 2 + 2) + 6000 * (8 * B + 7) ^ 2 + 4 * B + 3

theorem endpointDistanceWithWork_bounds {n : ℕ} (q r : TargetInterval n) (B : ℕ)
    (hql : Nat.size q.lo + 2 ≤ B) (hqh : Nat.size q.hi + 2 ≤ B)
    (hrl : Nat.size r.lo + 2 ≤ B) (hrh : Nat.size r.hi + 2 ≤ B) :
    (endpointDistanceWithWork q r).1.width ≤ endpointDistanceWordBudget B ∧
      (endpointDistanceWithWork q r).2 ≤ endpointDistanceBitBudget B := by
  have hlw := distanceWithWork_width (nat q.lo) (nat r.lo) B
    ((nat_width_le _).trans hql) ((nat_width_le _).trans hrl)
  have hhw := distanceWithWork_width (nat q.hi) (nat r.hi) B
    ((nat_width_le _).trans hqh) ((nat_width_le _).trans hrh)
  have hlc := distanceWithWork_cost (nat q.lo) (nat r.lo) B
    ((nat_width_le _).trans hql) ((nat_width_le _).trans hrl)
  have hhc := distanceWithWork_cost (nat q.hi) (nat r.hi) B
    ((nat_width_le _).trans hqh) ((nat_width_le _).trans hrh)
  have hw := canonicalAddWithWork_width (distanceWithWork (nat q.lo) (nat r.lo)).1
    (distanceWithWork (nat q.hi) (nat r.hi)).1 (8 * B + 6) hlw hhw
  have hc := canonicalAddWithWork_cost (distanceWithWork (nat q.lo) (nat r.lo)).1
    (distanceWithWork (nat q.hi) (nat r.hi)).1 (8 * B + 6) hlw hhw
  constructor
  · change (canonicalAddWithWork (distanceWithWork (nat q.lo) (nat r.lo)).1
      (distanceWithWork (nat q.hi) (nat r.hi)).1).1.width ≤ endpointDistanceWordBudget B
    unfold endpointDistanceWordBudget
    omega
  · change _ + _ + _ + _ + _ + _ + _ + 3 ≤ _
    simp only [Nat.add_assoc, Nat.reduceAdd] at hc
    unfold endpointDistanceBitBudget
    omega

def endpointScoreWordBudget (M B : ℕ) : ℕ :=
  8 * (connectionWordBudget M B + bandMassTotalStorageBudget M B) + 6

def endpointScoreBitBudget (M B : ℕ) : ℕ :=
  connectionBitBudget M B + 2 * B + M + 2 + storedSumBitBudget M B + 6 * M +
    6000 * (connectionWordBudget M B + bandMassTotalStorageBudget M B + 1) ^ 2 + 2

theorem endpointScoreWithWork_bounds {n M : ℕ} (r : TargetInterval n)
    (child : Fin M → TargetInterval n → BinaryFraction) (states : Fin M → TargetInterval n)
    (B : ℕ) (hrl : Nat.size r.lo + 2 ≤ B) (hrh : Nat.size r.hi + 2 ≤ B)
    (he : ∀ i, Nat.size (states i).lo + 2 ≤ B ∧ Nat.size (states i).hi + 2 ≤ B)
    (hv : ∀ i, (child i (states i)).width ≤ B) :
    (endpointScoreWithWork r child states).1.width ≤ endpointScoreWordBudget M B ∧
      (endpointScoreWithWork r child states).2 ≤ endpointScoreBitBudget M B := by
  have hlist : ∀ s ∈ List.ofFn states, Nat.size s.lo + 2 ≤ B ∧ Nat.size s.hi + 2 ≤ B := by
    intro s hs
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hs
    exact he i
  have hcw := connectionWithWork_width (nat r.lo) (nat r.hi) (List.ofFn states) B
    ((nat_width_le _).trans hrl) ((nat_width_le _).trans hrh) hlist
  have hcc := connectionWithWork_cost (nat r.lo) (nat r.hi) (List.ofFn states) B
    ((nat_width_le _).trans hrl) ((nat_width_le _).trans hrh) hlist
  simp only [List.length_ofFn] at hcw hcc
  have hew : (endpointConnectionWithWork r states).1.width ≤ connectionWordBudget M B := hcw
  have hec : (endpointConnectionWithWork r states).2 ≤ connectionBitBudget M B + 2 * B + M + 2 := by
    change _ + Nat.size r.lo + Nat.size r.hi + M + 2 ≤ _
    omega
  have hvlist : ∀ a ∈ List.ofFn (fun i => child i (states i)), a.width ≤ B := by
    intro a ha
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
    exact hv i
  have hsw := sumListWithWork_width _ B hvlist
  have hsc := sumListWithWork_cost _ B hvlist
  simp only [List.length_ofFn] at hsw hsc
  have htw := canonicalAddWithWork_width (endpointConnectionWithWork r states).1
    (sumListWithWork (List.ofFn fun i => child i (states i))).1
    (connectionWordBudget M B + bandMassTotalStorageBudget M B) (by omega) (by omega)
  have htc := canonicalAddWithWork_cost (endpointConnectionWithWork r states).1
    (sumListWithWork (List.ofFn fun i => child i (states i))).1
    (connectionWordBudget M B + bandMassTotalStorageBudget M B) (by omega) (by omega)
  refine ⟨htw, ?_⟩
  change _ + _ + _ + 2 ≤ _
  unfold endpointScoreBitBudget
  omega

def wideMinimumBitBudget (M n B : ℕ) : ℕ :=
  endpointScoreBitBudget M B + n * (endpointScoreBitBudget M B + 3) +
    (1 + n * (1000 * (endpointScoreWordBudget M B + 1) ^ 2 + 2)) + 2

theorem wideMinimumWithWork_bounds {n M : ℕ} (r : TargetInterval n)
    (child : Fin M → TargetInterval n → BinaryFraction)
    (actions : List (Fin M → TargetInterval n)) (hne : actions ≠ []) (B : ℕ)
    (hrl : Nat.size r.lo + 2 ≤ B) (hrh : Nat.size r.hi + 2 ≤ B)
    (he : ∀ states ∈ actions, ∀ i, Nat.size (states i).lo + 2 ≤ B ∧ Nat.size (states i).hi + 2 ≤ B)
    (hv : ∀ states ∈ actions, ∀ i, (child i (states i)).width ≤ B) :
    (wideMinimumWithWork r child actions hne).1.width ≤ endpointScoreWordBudget M B ∧
      (wideMinimumWithWork r child actions hne).2 ≤ wideMinimumBitBudget M actions.length B := by
  have hf := endpointScoreWithWork_bounds r child (actions.head hne) B hrl hrh
    (he _ (List.head_mem hne)) (hv _ (List.head_mem hne))
  let scores := arithmeticMapWithWork (endpointScoreWithWork r child) actions
  have hs : ∀ value ∈ scores.1, value.width ≤ endpointScoreWordBudget M B := by
    intro value hvalue
    simp only [scores, arithmeticMapWithWork_value] at hvalue
    obtain ⟨states, hstates, heq⟩ := List.mem_map.mp hvalue
    subst value
    exact (endpointScoreWithWork_bounds r child states B hrl hrh (he states hstates) (hv states hstates)).1
  have hlen : scores.1.length = actions.length := by
    simp only [scores, arithmeticMapWithWork_value, List.length_map]
  have hsc := arithmeticMapWithWork_cost (endpointScoreWithWork r child) actions
    (endpointScoreBitBudget M B) (fun states hstates =>
      (endpointScoreWithWork_bounds r child states B hrl hrh (he states hstates) (hv states hstates)).2)
  have hmw := minimumWithWork_width (endpointScoreWithWork r child (actions.head hne)).1
    scores.1 (endpointScoreWordBudget M B) hf.1 hs
  have hmc := minimumWithWork_cost (endpointScoreWithWork r child (actions.head hne)).1
    scores.1 (endpointScoreWordBudget M B) hf.1 hs
  rw [hlen] at hmc
  refine ⟨hmw, ?_⟩
  change (endpointScoreWithWork r child (actions.head hne)).2 + scores.2 +
    (minimumWithWork (endpointScoreWithWork r child (actions.head hne)).1 scores.1).2 + 2 ≤ _
  change scores.2 ≤ _ at hsc
  unfold wideMinimumBitBudget
  omega

def stateGapWordBudget (B : ℕ) : ℕ := 64 * B + 54

def stateGapBitBudget (B : ℕ) : ℕ :=
  (6000 * (B + 1) ^ 2 + 1) + (6000 * (8 * B + 7) ^ 2 + 1) + 3 * B + 2

theorem stateGapWithWork_bounds {n : ℕ} (sourceLength : ℕ) (r : TargetInterval n) (B : ℕ)
    (hs : Nat.size sourceLength + 2 ≤ B) (hrl : Nat.size r.lo + 2 ≤ B)
    (hrh : Nat.size r.hi + 2 ≤ B) :
    (stateGapWithWork sourceLength r).1.width ≤ stateGapWordBudget B ∧
      (stateGapWithWork sourceLength r).2 ≤ stateGapBitBudget B := by
  have htw := subWithWork_width (nat r.hi) (nat r.lo) B
    ((nat_width_le _).trans hrh) ((nat_width_le _).trans hrl)
  have htc := subWithWork_cost (nat r.hi) (nat r.lo) B
    ((nat_width_le _).trans hrh) ((nat_width_le _).trans hrl)
  have hsw : (nat sourceLength).width ≤ 8 * B + 6 := (nat_width_le _).trans (by omega)
  have hrw := subWithWork_width (subWithWork (nat r.hi) (nat r.lo)).1 (nat sourceLength)
    (8 * B + 6) htw hsw
  have hrc := subWithWork_cost (subWithWork (nat r.hi) (nat r.lo)).1 (nat sourceLength)
    (8 * B + 6) htw hsw
  constructor
  · change (subWithWork (subWithWork (nat r.hi) (nat r.lo)).1 (nat sourceLength)).1.width ≤ stateGapWordBudget B
    unfold stateGapWordBudget
    omega
  · change _ + _ + _ + _ + _ + 2 ≤ _
    simp only [Nat.add_assoc, Nat.reduceAdd] at hrc
    unfold stateGapBitBudget
    omega

end BinaryFraction
end EditApproximation

end OAI
