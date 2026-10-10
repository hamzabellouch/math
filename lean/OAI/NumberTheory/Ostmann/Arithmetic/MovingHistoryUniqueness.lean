import OAI.NumberTheory.Ostmann.Arithmetic.MovingFrequencyCoefficient

namespace OAI

/-! # Rigidity of the actual moving-giant histories at fixed samples -/

namespace Ostmann
open scoped Classical BigOperators

/-- Frequencies stored in the slot data do not enter the products, bounds,
or child slots in the rigidity predicate. They may be replaced by one fixed
template before comparing two histories. -/
theorem movingValidHistory_build_iff {σ : Type*}
    (value : σ → ℕ) (childBound pivotBound : ℕ → ℕ) (n : ℕ)
    (t u v : FrequencyTree ℤ n) (small bulk : TreeLeafTuple (List σ) n)
    (a : MovingSampleSlots σ n) (XL XR : ℕ) :
    ValidTransferHistory (movingSlotSystem value childBound pivotBound) n
      ⟨n, buildMovingSlotData n t small bulk a, XL, XR⟩ v ↔
    ValidTransferHistory (movingSlotSystem value childBound pivotBound) n
      ⟨n, buildMovingSlotData n u small bulk a, XL, XR⟩ v := by
  induction a generalizing XL XR with
  | leaf => rfl
  | @node n a l r ihL ihR =>
    let U := movingCompensationSlots n a
    let sys := movingSlotSystem value childBound pivotBound
    let x : MovingSlotState σ := ⟨n + 1, buildMovingSlotData (n + 1) t small bulk (.node a l r), XL, XR⟩
    change (∃ P, ValidTransferNode sys x v.1 (frequencyRoot n v.2.1) (frequencyRoot n v.2.2) P ∧
      ValidTransferHistory sys n
        ⟨n, buildMovingSlotData n t.2.1 (appendMovingSlotLeaves n U small.1) bulk.1 l,
          P / MovingSlotReversal.naturalProduct value (flattenMovingSlots n U), XL⟩ v.2.1 ∧
      ValidTransferHistory sys n
        ⟨n, buildMovingSlotData n t.2.2 (appendMovingSlotLeaves n U small.2) bulk.2 r,
          P / MovingSlotReversal.naturalProduct value (flattenMovingSlots n U), XR⟩ v.2.2) ↔ _
    have hn (P : ℕ) : ValidTransferNode sys x v.1 (frequencyRoot n v.2.1) (frequencyRoot n v.2.2) P ↔
        ValidTransferNode sys
          ⟨n + 1, buildMovingSlotData (n + 1) u small bulk (.node a l r), XL, XR⟩
          v.1 (frequencyRoot n v.2.1) (frequencyRoot n v.2.2) P := by
      constructor <;> intro h <;> exact
        ⟨h.root_ne_zero, h.root_unit, h.relation, h.pivot_pos, h.pivot_bound,
          h.left_bound, h.right_bound, h.range_gap, h.pivot_unit⟩
    constructor
    · rintro ⟨P, hP, hL, hR⟩
      exact ⟨P, (hn P).mp hP,
        (ihL t.2.1 u.2.1 v.2.1 (appendMovingSlotLeaves n U small.1) bulk.1 _ XL).mp hL,
        (ihR t.2.2 u.2.2 v.2.2 (appendMovingSlotLeaves n U small.2) bulk.2 _ XR).mp hR⟩
    · rintro ⟨P, hP, hL, hR⟩
      exact ⟨P, (hn P).mpr hP,
        (ihL t.2.1 u.2.1 v.2.1 (appendMovingSlotLeaves n U small.1) bulk.1 _ XL).mpr hL,
        (ihR t.2.2 u.2.2 v.2.2 (appendMovingSlotLeaves n U small.2) bulk.2 _ XR).mpr hR⟩

/-- Original support forces a unique full frequency history when all actual
internal samples, top primes and the root frequency have been fixed. -/
theorem movingRecursiveWeight_history_unique {σ : Type*}
    (value : σ → ℕ) (childBound pivotBound : ℕ → ℕ)
    (F : MovingSlotState σ → ℤ → ℂ) (E : MovingSlotState σ → ℤ → ℤ → ℤ → ℝ)
    (n : ℕ) (t u : FrequencyTree ℤ n) (small bulk : TreeLeafTuple (List σ) n)
    (a : MovingSampleSlots σ n) (XL XR : ℕ)
    (ht : recursiveTransferWeight (movingSlotSystem value childBound pivotBound) F
      (movingSlotCutoff value childBound pivotBound E) n
      ⟨n, buildMovingSlotData n t small bulk a, XL, XR⟩ t ≠ 0)
    (hu : recursiveTransferWeight (movingSlotSystem value childBound pivotBound) F
      (movingSlotCutoff value childBound pivotBound E) n
      ⟨n, buildMovingSlotData n u small bulk a, XL, XR⟩ u ≠ 0)
    (hroot : frequencyRoot n t = frequencyRoot n u) : t = u := by
  have htv := recursiveTransferWeight_nonzero_valid _ _ _ _ _ _ ht
  have huv := recursiveTransferWeight_nonzero_valid _ _ _ _ _ _ hu
  have huv' := (movingValidHistory_build_iff value childBound pivotBound n u t u small bulk a XL XR).mp huv
  exact validTransferHistory_unique _ n _ t u htv huv' hroot

end Ostmann

end OAI
