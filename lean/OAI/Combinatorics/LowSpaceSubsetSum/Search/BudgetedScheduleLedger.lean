import OAI.Combinatorics.LowSpaceSubsetSum.Search.BudgetedBucketScale
import OAI.Combinatorics.LowSpaceSubsetSum.Search.BudgetedSchedule
import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationScheduleLedger

namespace OAI

namespace LowSpaceSubsetSum.RepresentationParentData

variable {n : ℕ}

theorem taskStarts_positive (D : RepresentationParentData n) (B : ℕ)
    (order : List (Fin n)) (P : MaskRestriction n) : 1 ≤ D.taskStarts B order P := by
  cases order with
  | nil => exact le_rfl
  | cons i order =>
    rw [taskStarts]
    split <;> omega

theorem local_queries_le_prefix (D : RepresentationParentData n) (B : ℕ)
    (order : List (Fin n)) (P : MaskRestriction n) :
    ({D with maskRestriction := P}.collect B).state.queries ≤
      (D.prefixLedger B order P).queries := by
  cases order with
  | nil => exact le_rfl
  | cons i order =>
    rw [prefixLedger]
    split <;> simp only [CompressionLedger.add, localLedger] <;> omega

theorem local_copies_le_prefix (D : RepresentationParentData n) (B : ℕ)
    (order : List (Fin n)) (P : MaskRestriction n) :
    ({D with maskRestriction := P}.collect B).state.copies ≤
      (D.prefixLedger B order P).copies := by
  cases order with
  | nil => exact le_rfl
  | cons i order =>
    rw [prefixLedger]
    split <;> simp only [CompressionLedger.add, localLedger] <;> omega

end LowSpaceSubsetSum.RepresentationParentData

namespace LowSpaceSubsetSum.BudgetedScheduleLedger

open scoped BigOperators

variable {n g : ℕ}

theorem bucket_units (D : RepresentationScheduleData n g) (B z : ℕ)
    (families : Fin 4 → Array (Finset (Fin g))) :
    BudgetedBucketScale.units (D.bucket z) B families ≤
      4 * ((D.capacity + 1) *
        ((D.parentData 0 z).taskStarts B D.topOrder MaskRestriction.empty +
          (D.parentData 1 z).taskStarts B D.topOrder MaskRestriction.empty) +
        ((D.parentData 0 z).prefixLedger B D.topOrder MaskRestriction.empty).queries +
        ((D.parentData 1 z).prefixLedger B D.topOrder MaskRestriction.empty).queries +
        B * ((D.parentData 0 z).prefixLedger B D.topOrder MaskRestriction.empty).copies +
        B * ((D.parentData 1 z).prefixLedger B D.topOrder MaskRestriction.empty).copies +
        D.coordinates.totalScans families D.target ((D.bucket z).checkList B)) := by
  have hq := (D.parentData 0 z).local_queries_le_prefix B D.topOrder MaskRestriction.empty
  have hc := (D.parentData 0 z).local_copies_le_prefix B D.topOrder MaskRestriction.empty
  change ((D.parentData 0 z).collect B).state.queries ≤ _ at hq
  change ((D.parentData 0 z).collect B).state.copies ≤ _ at hc
  have hbc := Nat.mul_le_mul_left B hc
  have ht := (D.parentData 0 z).taskStarts_positive B D.topOrder MaskRestriction.empty
  have hsetup : D.capacity + 1 ≤ (D.capacity + 1) *
      (D.parentData 0 z).taskStarts B D.topOrder MaskRestriction.empty :=
    Nat.le_mul_of_pos_right _ (by omega)
  have hR : (D.capacity + D.capacity + 3) *
      (D.parentData 1 z).taskStarts B D.topOrder MaskRestriction.empty ≤
      3 * ((D.capacity + 1) *
        (D.parentData 1 z).taskStarts B D.topOrder MaskRestriction.empty) := by
    have h := Nat.mul_le_mul_right
      ((D.parentData 1 z).taskStarts B D.topOrder MaskRestriction.empty)
      (show D.capacity + D.capacity + 3 ≤ 3 * (D.capacity + 1) by omega)
    simpa only [Nat.mul_assoc] using h
  change D.capacity + 1 + (D.capacity + D.capacity + 3) *
      (D.parentData 1 z).taskStarts B D.topOrder MaskRestriction.empty +
      ((D.parentData 0 z).collect B).state.queries +
      ((D.parentData 1 z).prefixLedger B D.topOrder MaskRestriction.empty).queries +
      B * ((D.parentData 0 z).collect B).state.copies +
      B * ((D.parentData 1 z).prefixLedger B D.topOrder MaskRestriction.empty).copies +
      D.coordinates.totalScans families D.target ((D.bucket z).checkList B) + 1 ≤ _
  simp only [Nat.mul_add]
  omega

theorem units_sum (D : RepresentationScheduleData n g) (B : ℕ)
    (families : Fin 4 → Array (Finset (Fin g))) :
    (∑ z : Fin D.q, BudgetedBucketScale.units (D.bucket z.val) B families) ≤
      4 * D.coreUnits B families := by
  have hs := Finset.sum_le_sum (fun (z : Fin D.q) (_ : z ∈ Finset.univ) =>
    bucket_units D B z.val families)
  rw [← Finset.mul_sum] at hs
  have he : (∑ z : Fin D.q,
      ((D.capacity + 1) *
        ((D.parentData 0 z.val).taskStarts B D.topOrder MaskRestriction.empty +
          (D.parentData 1 z.val).taskStarts B D.topOrder MaskRestriction.empty) +
        ((D.parentData 0 z.val).prefixLedger B D.topOrder MaskRestriction.empty).queries +
        ((D.parentData 1 z.val).prefixLedger B D.topOrder MaskRestriction.empty).queries +
        B * ((D.parentData 0 z.val).prefixLedger B D.topOrder MaskRestriction.empty).copies +
        B * ((D.parentData 1 z.val).prefixLedger B D.topOrder MaskRestriction.empty).copies +
        D.coordinates.totalScans families D.target ((D.bucket z.val).checkList B))) =
      D.setupUnits B + (D.joinLedger B).queries + B * (D.joinLedger B).copies +
        D.scanCount B families := by
    simp only [RepresentationScheduleData.setupUnits, RepresentationScheduleData.taskCount,
      RepresentationScheduleData.joinLedger, RepresentationScheduleData.scanCount,
      Fin.sum_univ_two, Finset.sum_add_distrib, Finset.mul_sum, Nat.mul_add]
    ring
  rw [he] at hs
  apply hs.trans
  apply Nat.mul_le_mul_left 4
  rw [RepresentationScheduleData.coreUnits, ← D.joinLedger_queries B]
  omega

theorem residue_overhead (D : RepresentationScheduleData n g) (B : ℕ)
    (families : Fin 4 → Array (Finset (Fin g))) :
    D.q + 1 ≤ D.coreUnits B families := by
  have hs := Finset.sum_le_sum (fun (z : Fin D.q) (_ : z ∈ Finset.univ) =>
    (D.parentData 0 z.val).taskStarts_positive B D.topOrder MaskRestriction.empty)
  have hq : D.q ≤ ∑ z : Fin D.q,
      (D.parentData 0 z.val).taskStarts B D.topOrder MaskRestriction.empty := by
    simpa using hs
  have ht : D.q ≤ D.taskCount B := by
    unfold RepresentationScheduleData.taskCount
    rw [Fin.sum_univ_two]
    omega
  have hsetup : D.taskCount B ≤ D.setupUnits B := by
    exact Nat.le_mul_of_pos_left _ (by omega)
  unfold RepresentationScheduleData.coreUnits
  omega

private theorem range_sum_fin (f : ℕ → ℕ) (count : ℕ) :
    ((List.range count).map f).sum = ∑ i : Fin count, f i.val := by
  induction count with
  | zero => simp
  | succ count ih =>
    rw [List.sum_range_succ, Fin.sum_univ_castSucc]
    simpa only [Fin.val_castSucc, Fin.val_last] using congrArg (· + f count) ih

theorem allowance_eq (D : RepresentationScheduleData n g) (F : IndexedMask n)
    (hF : F.semantic = D.signs) (B : ℕ)
    (families : Fin 4 → Array (Finset (Fin g))) :
    BudgetedSchedule.allowance D F hF B families = 4 * (D.q + 1) +
      ∑ z : Fin D.q,
        BudgetedPreparedBucket.allowance (D.bucket z.val) F F hF hF B families := by
  unfold BudgetedSchedule.allowance
  rw [BudgetedResidueLoop.allowance_eq]
  simp only [Nat.zero_add, range_sum_fin]

/-- Every bucket is paid from the original source ledger. The residue loop
itself contributes only a polynomial factor, including early stopping. -/
theorem allowance_scale (D : RepresentationScheduleData n g) (F : IndexedMask n)
    (hF : F.semantic = D.signs) (hn : 10000 ≤ n) (B : ℕ)
    (families : Fin 4 → Array (Finset (Fin g))) :
    BudgetedSchedule.allowance D F hF B families ≤
      inputScale D.input ^ 14 * D.coreUnits B families := by
  let u := inputScale D.input
  have hu : 10000 ≤ u := by unfold u inputScale; omega
  have hs := Finset.sum_le_sum (fun (z : Fin D.q) (_ : z ∈ Finset.univ) =>
    BudgetedBucketScale.allowance_scale (D.bucket z.val) F F hF hF rfl rfl hn B families)
  change (∑ z : Fin D.q,
    BudgetedPreparedBucket.allowance (D.bucket z.val) F F hF hF B families) ≤
      ∑ z : Fin D.q, u ^ 12 * BudgetedBucketScale.units (D.bucket z.val) B families at hs
  rw [← Finset.mul_sum] at hs
  have hsum := hs.trans (Nat.mul_le_mul_left (u ^ 12) (units_sum D B families))
  have hsum' : (∑ z : Fin D.q,
      BudgetedPreparedBucket.allowance (D.bucket z.val) F F hF hF B families) ≤
      4 * (u ^ 12 * D.coreUnits B families) := by
    simpa only [Nat.mul_left_comm] using hsum
  have hcore : D.coreUnits B families ≤ u ^ 12 * D.coreUnits B families :=
    Nat.le_mul_of_pos_left _ (pow_pos (by omega) _)
  have hover := Nat.mul_le_mul_left 4 ((residue_overhead D B families).trans hcore)
  have hcoef : 8 * u ^ 12 ≤ u ^ 14 := by
    have h8 : 8 ≤ u ^ 2 := (by omega : 8 ≤ u).trans (Nat.le_self_pow (by decide) u)
    calc
      _ ≤ u ^ 2 * u ^ 12 := Nat.mul_le_mul_right _ h8
      _ = _ := by ring
  rw [allowance_eq]
  calc
    _ ≤ 8 * (u ^ 12 * D.coreUnits B families) := by omega
    _ = (8 * u ^ 12) * D.coreUnits B families := by ring
    _ ≤ u ^ 14 * D.coreUnits B families := Nat.mul_le_mul_right _ hcoef

end LowSpaceSubsetSum.BudgetedScheduleLedger

end OAI
