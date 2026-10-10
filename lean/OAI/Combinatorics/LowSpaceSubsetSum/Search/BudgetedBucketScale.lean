import OAI.Combinatorics.LowSpaceSubsetSum.Search.BudgetedBucketLedger

namespace OAI

namespace LowSpaceSubsetSum.BudgetedBucketScale

variable {n g : ℕ}

theorem coefficients (I : Instance n) (hn : 10000 ≤ n) :
    2 * inputScale I ^ 9 + inputScale I ^ 3 + 16 ≤ inputScale I ^ 10 ∧
      StoredPrefixController.header n ≤ inputScale I ^ 10 ∧
      3 * inputScale I ^ 10 ≤ inputScale I ^ 11 := by
  let u := inputScale I
  have hnu : n + 1 ≤ u := by unfold u inputScale; omega
  have hu : 10000 ≤ u := by omega
  have h39 : u ^ 3 ≤ u ^ 9 := Nat.pow_le_pow_right (by omega) (by decide)
  have h16 : 16 ≤ u ^ 9 := (by omega : 16 ≤ u).trans (Nat.le_self_pow (by decide) u)
  have h4 : 4 * u ^ 9 ≤ u ^ 10 := by
    calc
      _ ≤ u * u ^ 9 := Nat.mul_le_mul_right _ (by omega)
      _ = _ := by ring
  have h2 : (n + 1) ^ 2 ≤ u ^ 2 := Nat.pow_le_pow_left hnu 2
  have hone : 1 ≤ u ^ 2 := Nat.one_le_pow _ _ (by omega)
  have h28 : 28 ≤ u ^ 2 := (by omega : 28 ≤ u).trans (Nat.le_self_pow (by decide) u)
  have h24 : 28 * u ^ 2 ≤ u ^ 4 := by
    calc
      _ ≤ u ^ 2 * u ^ 2 := Nat.mul_le_mul_right _ h28
      _ = _ := by ring
  have h410 : u ^ 4 ≤ u ^ 10 := Nat.pow_le_pow_right (by omega) (by decide)
  refine ⟨by change 2 * u ^ 9 + u ^ 3 + 16 ≤ u ^ 10; omega, ?_, ?_⟩
  · change StoredPrefixController.header n ≤ u ^ 10
    unfold StoredPrefixController.header
    have hm := Nat.mul_le_mul_left 20 h2
    omega
  · change 3 * u ^ 10 ≤ u ^ 11
    calc
      _ ≤ u * u ^ 10 := Nat.mul_le_mul_right _ (by omega)
      _ = _ := by ring

theorem prefix_charge (D : RepresentationBucketData n g) (hn : 10000 ≤ n)
    (B L C : ℕ) (hL : L ≤ C + 1) :
    BudgetedBucketLedger.prefixCharge D B L ≤ inputScale D.right.input ^ 11 *
      ((C + D.right.capacity + 3) * D.right.taskStarts B D.topOrder MaskRestriction.empty +
        (D.right.prefixLedger B D.topOrder MaskRestriction.empty).queries +
        B * (D.right.prefixLedger B D.topOrder MaskRestriction.empty).copies) := by
  let u := inputScale D.right.input
  let S := C + D.right.capacity + 3
  let A := 2 * u ^ 9 + u ^ 3 + 16
  have hu : 1 ≤ u := by unfold u inputScale; omega
  obtain ⟨hA, hh, h3⟩ := coefficients D.right.input hn
  change A ≤ u ^ 10 at hA
  change StoredPrefixController.header n ≤ u ^ 10 at hh
  change 3 * u ^ 10 ≤ u ^ 11 at h3
  have h6 : u ^ 6 ≤ u ^ 10 := Nat.pow_le_pow_right (by omega) (by decide)
  have h7 : u ^ 7 ≤ u ^ 11 := Nat.pow_le_pow_right (by omega) (by decide)
  have hone : 1 ≤ u ^ 11 := Nat.one_le_pow _ _ hu
  have ha := (Nat.mul_le_mul_right (D.right.capacity + 1) hA).trans
    (Nat.mul_le_mul_left (u ^ 10) (by unfold S; omega : D.right.capacity + 1 ≤ S))
  have hh' := hh.trans (Nat.le_mul_of_pos_right (u ^ 10) (by unfold S; omega : 0 < S))
  have hl := (Nat.mul_le_mul_right (L + D.right.capacity + 2) h6).trans
    (Nat.mul_le_mul_left (u ^ 10) (by unfold S; omega : L + D.right.capacity + 2 ≤ S))
  have hcoeff : A * (D.right.capacity + 1) + StoredPrefixController.header n +
      u ^ 6 * (L + D.right.capacity + 2) ≤ u ^ 11 * S := by
    have hmul := Nat.mul_le_mul_right S h3
    simp only [Nat.mul_assoc] at hmul
    omega
  have hT := Nat.mul_le_mul_right (D.right.taskStarts B D.topOrder MaskRestriction.empty) hcoeff
  have hQ := Nat.mul_le_mul_right
    (D.right.prefixLedger B D.topOrder MaskRestriction.empty).queries h7
  have hC := Nat.mul_le_mul_right
    (B * (D.right.prefixLedger B D.topOrder MaskRestriction.empty).copies) hone
  change _ ≤ u ^ 11 * (S * _ + _ + _)
  unfold BudgetedBucketLedger.prefixCharge
  change (A * (D.right.capacity + 1) + StoredPrefixController.header n) * _ +
    u ^ 7 * _ + B * _ + u ^ 6 * (L + D.right.capacity + 2) * _ ≤ _
  calc
    _ = (A * (D.right.capacity + 1) + StoredPrefixController.header n +
          u ^ 6 * (L + D.right.capacity + 2)) *
          D.right.taskStarts B D.topOrder MaskRestriction.empty +
        u ^ 7 * (D.right.prefixLedger B D.topOrder MaskRestriction.empty).queries +
        B * (D.right.prefixLedger B D.topOrder MaskRestriction.empty).copies := by ring
    _ ≤ u ^ 11 * S * D.right.taskStarts B D.topOrder MaskRestriction.empty +
        u ^ 11 * (D.right.prefixLedger B D.topOrder MaskRestriction.empty).queries +
        u ^ 11 * (B * (D.right.prefixLedger B D.topOrder MaskRestriction.empty).copies) := by omega
    _ = _ := by ring

theorem parent_bill (D : RepresentationParentData n) (hn : 10000 ≤ n)
    (B C : ℕ) (P : StoredRestriction n) :
    BudgetedParentCollector.bill D B C P ≤
      inputScale D.input ^ 10 * (C + 1) +
        inputScale D.input ^ 7 * ({D with maskRestriction := P.semantic}.collect B).state.queries +
        B * ({D with maskRestriction := P.semantic}.collect B).state.copies := by
  have h := Nat.mul_le_mul_right (C + 1) (coefficients D.input hn).1
  have ha : inputScale D.input ^ 3 + 16 ≤
      (inputScale D.input ^ 3 + 16) * (C + 1) := Nat.le_mul_of_pos_right _ (by omega)
  unfold BudgetedParentCollector.bill BudgetedPreparedParent.setupCharge
  simp only [Nat.add_mul] at h ha
  omega

noncomputable def units (D : RepresentationBucketData n g) (B : ℕ)
    (families : Fin 4 → Array (Finset (Fin g))) : ℕ :=
  (D.left.capacity + 1) + (D.left.capacity + D.right.capacity + 3) *
      D.right.taskStarts B D.topOrder MaskRestriction.empty +
    (D.left.collect B).state.queries +
    (D.right.prefixLedger B D.topOrder MaskRestriction.empty).queries +
    B * (D.left.collect B).state.copies +
    B * (D.right.prefixLedger B D.topOrder MaskRestriction.empty).copies +
    D.coordinates.totalScans families D.target (D.checkList B) + 1

theorem allowance_scale (D : RepresentationBucketData n g) (FL FR : IndexedMask n)
    (hFL : FL.semantic = D.left.signs) (hFR : FR.semantic = D.right.signs)
    (hleft : D.left.maskRestriction = MaskRestriction.empty)
    (hinput : D.left.input = D.right.input) (hn : 10000 ≤ n) (B : ℕ)
    (families : Fin 4 → Array (Finset (Fin g))) :
    BudgetedPreparedBucket.allowance D FL FR hFL hFR B families ≤
      inputScale D.right.input ^ 12 * units D B families := by
  let u := inputScale D.right.input
  let left := (ComputedParentExecution.run D.left FL StoredRestriction.empty hFL B).1.dictionary
  have hu : 8 ≤ u := by unfold u inputScale; omega
  have hU : 1 ≤ u ^ 12 := Nat.one_le_pow _ _ (by omega)
  have h8 : 8 ≤ u ^ 12 := hu.trans (Nat.le_self_pow (by decide) u)
  have h10 : u ^ 10 ≤ u ^ 12 := Nat.pow_le_pow_right (by omega) (by decide)
  have h11 : u ^ 11 ≤ u ^ 12 := Nat.pow_le_pow_right (by omega) (by decide)
  have h7 : u ^ 7 ≤ u ^ 12 := Nat.pow_le_pow_right (by omega) (by decide)
  have h6 : u ^ 6 ≤ u ^ 12 := Nat.pow_le_pow_right (by omega) (by decide)
  have hreset : {D.left with maskRestriction := MaskRestriction.empty} = D.left := by rw [← hleft]
  have hb := parent_bill D.left hn B D.left.capacity StoredRestriction.empty
  rw [StoredRestriction.empty_value, hreset, hinput] at hb
  change BudgetedParentCollector.bill D.left B D.left.capacity StoredRestriction.empty ≤
    u ^ 10 * (D.left.capacity + 1) + u ^ 7 * (D.left.collect B).state.queries +
      B * (D.left.collect B).state.copies at hb
  have hb' : BudgetedParentCollector.bill D.left B D.left.capacity StoredRestriction.empty ≤
      u ^ 12 * ((D.left.capacity + 1) + (D.left.collect B).state.queries +
        B * (D.left.collect B).state.copies) := by
    have hC := Nat.mul_le_mul_right (D.left.capacity + 1) h10
    have hQ := Nat.mul_le_mul_right (D.left.collect B).state.queries h7
    have hR := Nat.mul_le_mul_right (B * (D.left.collect B).state.copies) hU
    change _ ≤ u ^ 12 * _
    rw [Nat.mul_add, Nat.mul_add]
    simp only [Nat.one_mul] at hR
    omega
  have hsize : left.val.records.size ≤ D.left.capacity + 1 :=
    (RecordedDictionary.storage left.property).1
  have hp := prefix_charge D hn B left.val.records.size D.left.capacity hsize
  have hp' : BudgetedBucketLedger.prefixCharge D B left.val.records.size ≤
      u ^ 12 * ((D.left.capacity + D.right.capacity + 3) *
        D.right.taskStarts B D.topOrder MaskRestriction.empty +
        (D.right.prefixLedger B D.topOrder MaskRestriction.empty).queries +
        B * (D.right.prefixLedger B D.topOrder MaskRestriction.empty).copies) := by
    exact hp.trans (Nat.mul_le_mul_right _ h11)
  have hs := Nat.mul_le_mul_right
    (D.coordinates.totalScans families D.target (D.checkList B)) h6
  have hl := BudgetedBucketLedger.allowance_ledger D FL FR hFL hFR hleft B families
  change _ ≤ 8 + BudgetedParentCollector.bill D.left B D.left.capacity StoredRestriction.empty +
    BudgetedBucketLedger.prefixCharge D B left.val.records.size +
    u ^ 6 * D.coordinates.totalScans families D.target (D.checkList B) at hl
  calc
    _ ≤ 8 + BudgetedParentCollector.bill D.left B D.left.capacity StoredRestriction.empty +
        BudgetedBucketLedger.prefixCharge D B left.val.records.size +
        u ^ 6 * D.coordinates.totalScans families D.target (D.checkList B) := hl
    _ ≤ u ^ 12 +
        u ^ 12 * ((D.left.capacity + 1) + (D.left.collect B).state.queries +
          B * (D.left.collect B).state.copies) +
        u ^ 12 * ((D.left.capacity + D.right.capacity + 3) *
          D.right.taskStarts B D.topOrder MaskRestriction.empty +
          (D.right.prefixLedger B D.topOrder MaskRestriction.empty).queries +
          B * (D.right.prefixLedger B D.topOrder MaskRestriction.empty).copies) +
        u ^ 12 * D.coordinates.totalScans families D.target (D.checkList B) := by omega
    _ = _ := by unfold units; change _ = u ^ 12 * _; ring

end LowSpaceSubsetSum.BudgetedBucketScale

end OAI
