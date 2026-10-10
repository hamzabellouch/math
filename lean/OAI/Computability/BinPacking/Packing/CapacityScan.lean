import OAI.Computability.BinPacking.Search.SearchInitializeEncoding

namespace OAI

namespace BinPackingGap.CapacityScan

def step (label : Nat) (accumulator : Nat × Nat) (row : (Nat × Nat) × Nat) : Nat × Nat :=
  if row.2 = label then RawPacking.addFraction accumulator row.1 else accumulator

def scan (label : Nat) : RawInstance → List Nat → (Nat × Nat) → Bool
  | [], _, accumulator => decide (accumulator.1 ≤ accumulator.2)
  | _, [], accumulator => decide (accumulator.1 ≤ accumulator.2)
  | item :: items, assigned :: assignments, accumulator =>
      if accumulator.1 ≤ accumulator.2 then
        scan label items assignments (step label accumulator (item, assigned))
      else false

theorem scan_eq_true_iff (label : Nat) (items : RawInstance)
    (valid : items.Valid) (assignments : List Nat) (accumulator : Nat × Nat) :
    scan label items assignments accumulator = true ↔
      ((items.zip assignments).foldl (step label) accumulator).1 ≤
        ((items.zip assignments).foldl (step label) accumulator).2 := by
  induction items generalizing assignments accumulator with
  | nil => simp [scan]
  | cons item items ih =>
      have validTail : RawInstance.Valid items :=
        fun q mem => valid q (List.mem_cons_of_mem item mem)
      cases assignments with
      | nil => simp [scan]
      | cons assigned assignments =>
          by_cases accepted : accumulator.1 ≤ accumulator.2
          · simpa only [scan, ite_eq_left accepted, List.zip_cons_cons, List.foldl_cons] using
              ih validTail assignments (step label accumulator (item, assigned))
          · have overflow := FractionWidth.fold_overflow
              (item :: items) (assigned :: assignments) label accumulator valid
              (Nat.lt_of_not_ge accepted)
            have final_rejected :
                ¬(( (item :: items).zip (assigned :: assignments)).foldl
                    (step label) accumulator).1 ≤
                  (((item :: items).zip (assigned :: assignments)).foldl
                    (step label) accumulator).2 := by
              change (((item :: items).zip (assigned :: assignments)).foldl
                  (step label) accumulator).2 <
                (((item :: items).zip (assigned :: assignments)).foldl
                  (step label) accumulator).1 at overflow
              exact Nat.not_le_of_lt overflow
            simp only [scan, ite_eq_right accepted, Bool.false_eq_true, final_rejected]

theorem scan_initial_eq_capacityCheck (label : Nat) (items : RawInstance)
    (valid : items.Valid) (assignments : List Nat) :
    scan label items assignments (0, 1) =
      ExtensionCertificate.capacityCheck items assignments label := by
  apply Bool.eq_iff_iff.mpr
  rw [scan_eq_true_iff label items valid assignments,
    ExtensionCertificate.capacityCheck_eq_true_iff]
  rfl

theorem scan_initial_eq_true_iff_load (label : Nat) (items : RawInstance)
    (valid : items.Valid) (assignments : List Nat) :
    scan label items assignments (0, 1) = true ↔
      RawPacking.load items assignments label ≤ 1 := by
  rw [scan_initial_eq_capacityCheck label items valid assignments]
  exact ExtensionCertificate.capacityCheck_eq_true_iff_load items valid assignments label

end BinPackingGap.CapacityScan

end OAI
