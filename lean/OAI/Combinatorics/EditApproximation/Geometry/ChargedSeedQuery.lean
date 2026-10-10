import OAI.Combinatorics.EditApproximation.Geometry.ChargedPhysicalRequest
import OAI.Combinatorics.EditApproximation.Refinement.PhysicalMedianQuery
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! A pass-zero seed read requests a cached coarse entry. Later seed reads
request the previous pass's final table value in each distinct copy.
Thus neither kind of seed value enters the charged program as a free oracle. -/

namespace EditApproximation







theorem chargedSeedQuery_value {M J ny passes copies T S : ℕ} (N : ℕ) (multiplier : ℕ → ℕ)
    (parent : {r : PhysicalTableRequest M J ny // r.Bounded passes copies T S})
    (q : TargetInterval ny) (answer : ChargedPhysicalRequest M J ny passes copies T S → ℚ) :
    (chargedSeedQuery N multiplier parent (parent.val.node, q)).value (fun child => answer child.val) =
    if parent.val.pass = 0 then answer (Sum.inl (parent.val.node, q)) else
      (min N (upperMedian (List.ofFn fun copy : Fin copies =>
        ⌈(multiplier (parent.val.pass - 1) : ℚ) *
          answer (Sum.inr (chargedPreviousPass parent q copy))⌉₊)) : ℕ) := by
  unfold chargedSeedQuery
  rw [dite_eq_left rfl]
  split_ifs with hp
  · rfl
  · rw [FiniteQuery.collect_value]
    simp only [chargedPreviousRead, FiniteQuery.value, List.map_map,
      List.ofFn_eq_map, Function.comp_def]

theorem chargedSeedQuery_cost {M J ny passes copies T S : ℕ} (N : ℕ) (multiplier : ℕ → ℕ)
    (parent : {r : PhysicalTableRequest M J ny // r.Bounded passes copies T S})
    (state : PhysicalEntry M J ny)
    (oracle : {child : ChargedPhysicalRequest M J ny passes copies T S //
      child.rank < ChargedPhysicalRequest.rank (Sum.inr parent)} → ℚ) :
    (chargedSeedQuery N multiplier parent state).cost oracle (fun _ => 1) =
      if state.1 = parent.val.node then if parent.val.pass = 0 then 1 else copies else 0 := by
  unfold chargedSeedQuery
  split_ifs with hnode hpass
  · rfl
  · rw [FiniteQuery.cost_collect]
    simp only [chargedPreviousRead, FiniteQuery.cost, Nat.add_zero, List.map_const',
      List.length_finRange, List.sum_replicate, smul_eq_mul, Nat.mul_one]
  · rfl

end EditApproximation

end OAI
