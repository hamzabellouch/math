import OAI.Combinatorics.LowSpaceSubsetSum.Storage.StoredPrefixFilter
import OAI.Combinatorics.LowSpaceSubsetSum.Separators.SeparatorStoredMasks

namespace OAI

/-! # Executed construction of the separator's stored incidence lists

Sampled local masks are stored as bounded integer bit codes. Containment
and avoidance use bitwise intersection. Every table row scans the sampled
family in order and retains its occurrence indices, including duplicates.
-/

namespace LowSpaceSubsetSum.StoredIncidenceBuild

variable {g : ℕ}

theorem mem_decode (a : Fin (2 ^ g)) (i : Fin g) :
    i ∈ SeparatorStoredMasks.decode a ↔ a.val.testBit i.val = true := by
  simp only [SeparatorStoredMasks.decode, Finset.mem_filter, Finset.mem_univ, true_and,
    Nat.testBit_eq_decide_div_mod_eq, decide_eq_true_eq]
  change ((⟨a.val / 2 ^ i.val % 2, Nat.mod_lt _ (by decide)⟩ : Fin 2) == 1) = true ↔ _
  simp only [beq_iff_eq, Fin.ext_iff, Fin.val_one]

private theorem outside (a : Fin (2 ^ g)) (i : ℕ) (hi : g ≤ i) :
    a.val.testBit i = false :=
  Nat.testBit_eq_false_of_lt (a.isLt.trans_le (Nat.pow_le_pow_right (by decide) hi))

theorem subset_iff (a b : Fin (2 ^ g)) :
    SeparatorStoredMasks.decode a ⊆ SeparatorStoredMasks.decode b ↔ a.val &&& b.val = a.val := by
  constructor
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_and]
    by_cases hi : i < g
    · have himp : a.val.testBit i = true → b.val.testBit i = true := by
        intro ha
        exact (mem_decode b ⟨i, hi⟩).mp (h ((mem_decode a ⟨i, hi⟩).mpr ha))
      cases ha : a.val.testBit i <;> simp [ha, himp]
    · rw [outside a i (by omega)]
      rfl
  · intro h i hi
    have ha := (mem_decode a i).mp hi
    have hb := congrArg (fun v : ℕ => v.testBit i.val) h
    rw [Nat.testBit_and, ha, Bool.true_and] at hb
    exact (mem_decode b i).mpr hb

theorem disjoint_iff (a b : Fin (2 ^ g)) :
    Disjoint (SeparatorStoredMasks.decode a) (SeparatorStoredMasks.decode b) ↔
      a.val &&& b.val = 0 := by
  rw [Finset.disjoint_left]
  constructor
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_and, Nat.zero_testBit]
    by_cases hi : i < g
    · have himp : a.val.testBit i = true → b.val.testBit i = false := by
        intro ha
        apply Bool.eq_false_iff.mpr
        intro hb
        exact h ((mem_decode a ⟨i, hi⟩).mpr ha) ((mem_decode b ⟨i, hi⟩).mpr hb)
      cases ha : a.val.testBit i <;> simp [ha, himp]
    · rw [outside a i (by omega)]
      rfl
  · intro h i hi hj
    have ha := (mem_decode a i).mp hi
    have hb := (mem_decode b i).mp hj
    have hc := congrArg (fun v : ℕ => v.testBit i.val) h
    simp only [Nat.testBit_and, ha, hb, Bool.true_and, Nat.zero_testBit] at hc
    contradiction

def contains (a b : Fin (2 ^ g)) : Bool × ℕ := (decide (a.val &&& b.val = a.val), 2)

def avoids (a b : Fin (2 ^ g)) : Bool × ℕ := (decide (a.val &&& b.val = 0), 2)

theorem contains_value (a b : Fin (2 ^ g)) :
    (contains a b).1 = decide (SeparatorStoredMasks.decode a ⊆ SeparatorStoredMasks.decode b) := by
  simp only [contains, subset_iff]

theorem avoids_value (a b : Fin (2 ^ g)) :
    (avoids a b).1 = decide (Disjoint (SeparatorStoredMasks.decode a) (SeparatorStoredMasks.decode b)) := by
  simp only [avoids, disjoint_iff]

def row (test : Fin (2 ^ g) → Fin (2 ^ g) → Bool × ℕ)
    (family : Array (Fin (2 ^ g))) (mask : Fin (2 ^ g)) : Array ℕ × ℕ :=
  let out := MeasuredFilter.runAcc (fun j : Fin family.size => test mask family[j.val])
    (List.finRange family.size) [] 0
  ((out.1.map Fin.val).toArray, out.2 + 2 * out.1.length + family.size + 1)

theorem row_value (test : Fin (2 ^ g) → Fin (2 ^ g) → Bool × ℕ)
    (family : Array (Fin (2 ^ g))) (mask : Fin (2 ^ g)) :
    (row test family mask).1 =
      SeparatorIncidenceTable.table family (fun a b => (test a b).1) mask := by
  simp only [row, MeasuredFilter.runAcc_value, List.reverse_nil, List.nil_append,
    SeparatorIncidenceTable.table]

theorem row_work (test : Fin (2 ^ g) → Fin (2 ^ g) → Bool × ℕ) (K : ℕ)
    (ht : ∀ a b, (test a b).2 ≤ K)
    (family : Array (Fin (2 ^ g))) (mask : Fin (2 ^ g)) :
    (row test family mask).2 ≤ (K + 7) * family.size + 2 := by
  have h := MeasuredFilter.runAcc_work (fun j : Fin family.size => test mask family[j.val])
    K (fun j => ht mask family[j.val]) (List.finRange family.size) [] 0
  have hl := List.length_filter_le
    (fun j : Fin family.size => (test mask family[j.val]).1) (List.finRange family.size)
  simp only [row, MeasuredFilter.runAcc_value, List.reverse_nil, List.nil_append]
  simp only [List.length_finRange, List.length_nil, Nat.zero_add, Nat.add_zero] at h hl
  nlinarith only [h, hl]

private def mapAcc {α β : Type*} (f : α → β × ℕ) : List α → List β → ℕ → List β × ℕ
  | [], acc, work => (acc.reverse, work + acc.length + 1)
  | x :: xs, acc, work =>
    let out := f x
    mapAcc f xs (out.1 :: acc) (work + out.2 + 3)

private theorem mapAcc_value {α β : Type*} (f : α → β × ℕ)
    (xs : List α) (acc : List β) (work : ℕ) :
    (mapAcc f xs acc work).1 = acc.reverse ++ xs.map (fun x => (f x).1) := by
  induction xs generalizing acc work with
  | nil => simp [mapAcc]
  | cons x xs ih => simp [mapAcc, ih, List.reverse_cons, List.append_assoc]

private theorem mapAcc_work {α β : Type*} (f : α → β × ℕ) (K : ℕ)
    (hf : ∀ x, (f x).2 ≤ K) (xs : List α) (acc : List β) (work : ℕ) :
    (mapAcc f xs acc work).2 ≤ work + (K + 4) * xs.length + acc.length + 1 := by
  induction xs generalizing acc work with
  | nil => simp [mapAcc]
  | cons x xs ih =>
    have hi := ih ((f x).1 :: acc) (work + (f x).2 + 3)
    have hx := hf x
    simp only [mapAcc, List.length_cons, Nat.mul_add, Nat.mul_one] at *
    omega

def preprocess (test : Fin (2 ^ g) → Fin (2 ^ g) → Bool × ℕ)
    (family : Array (Fin (2 ^ g))) : Array (Array ℕ) × ℕ :=
  let out := mapAcc (row test family) (List.finRange (2 ^ g)) [] 0
  (out.1.toArray, out.2 + 2 * 2 ^ g + 1)

theorem preprocess_value (test : Fin (2 ^ g) → Fin (2 ^ g) → Bool × ℕ)
    (family : Array (Fin (2 ^ g))) :
    (preprocess test family).1 = SeparatorIncidenceTable.preprocess g family
      (fun a b => (test a b).1) := by
  apply Array.toList_inj.mp
  simp only [preprocess, mapAcc_value, List.reverse_nil, List.nil_append, row_value,
    SeparatorIncidenceTable.preprocess, List.toList_toArray, Array.toList_ofFn,
    List.ofFn_eq_map]

theorem preprocess_size (test : Fin (2 ^ g) → Fin (2 ^ g) → Bool × ℕ)
    (family : Array (Fin (2 ^ g))) : (preprocess test family).1.size = 2 ^ g := by
  rw [preprocess_value]
  simp only [SeparatorIncidenceTable.preprocess, Array.size_ofFn]

theorem preprocess_get (test : Fin (2 ^ g) → Fin (2 ^ g) → Bool × ℕ)
    (family : Array (Fin (2 ^ g))) (mask : Fin (2 ^ g)) :
    (preprocess test family).1[mask.val]'(by rw [preprocess_size]; exact mask.isLt) =
      SeparatorIncidenceTable.table family (fun a b => (test a b).1) mask := by
  simp only [preprocess_value, SeparatorIncidenceTable.preprocess, Array.getElem_ofFn]

theorem preprocess_work (test : Fin (2 ^ g) → Fin (2 ^ g) → Bool × ℕ) (K : ℕ)
    (ht : ∀ a b, (test a b).2 ≤ K) (family : Array (Fin (2 ^ g))) :
    (preprocess test family).2 ≤ ((K + 7) * family.size + 8) * 2 ^ g + 2 := by
  have h := mapAcc_work (row test family) ((K + 7) * family.size + 2)
    (fun x => row_work test K ht family x) (List.finRange (2 ^ g)) [] 0
  simp only [List.length_finRange, List.length_nil, Nat.zero_add, Nat.add_zero] at h
  change _ + 2 * 2 ^ g + 1 ≤ _
  nlinarith only [h]

def tables (family : Array (Fin (2 ^ g))) : (Array (Array ℕ) × Array (Array ℕ)) × ℕ :=
  let a := preprocess contains family
  let b := preprocess avoids family
  ((a.1, b.1), a.2 + b.2 + 2)

theorem tables_work (family : Array (Fin (2 ^ g))) :
    (tables family).2 ≤ 2 * (9 * family.size + 8) * 2 ^ g + 6 := by
  have ha := preprocess_work contains 2 (fun _ _ => le_rfl) family
  have hb := preprocess_work avoids 2 (fun _ _ => le_rfl) family
  change _ + _ + 2 ≤ _
  nlinarith only [ha, hb]

private theorem table_map {α β γ : Type*} (f : β → γ) (family : Array β)
    (compatible : α → γ → Bool) (mask : α) :
    SeparatorIncidenceTable.table (family.map f) compatible mask =
      SeparatorIncidenceTable.table family (fun a b => compatible a (f b)) mask := by
  apply Array.toList_inj.mp
  apply (SeparatorIncidenceTable.table_sorted _ _ _).eq_of_mem_iff
    (SeparatorIncidenceTable.table_sorted _ _ _)
  intro j
  rw [SeparatorIncidenceTable.table_mem, SeparatorIncidenceTable.table_mem]
  constructor
  · rintro ⟨h, hc⟩
    refine ⟨by simpa only [Array.size_map] using h, ?_⟩
    simpa only [Array.getElem_map] using hc
  · rintro ⟨h, hc⟩
    refine ⟨by simpa only [Array.size_map] using h, ?_⟩
    simpa only [Array.getElem_map] using hc

theorem containsStore_value (family : Array (Fin (2 ^ g))) :
    (preprocess contains family).1 =
      SeparatorStoredMasks.containsStore (family.map SeparatorStoredMasks.decode) := by
  simp only [preprocess_value, SeparatorStoredMasks.containsStore,
    SeparatorIncidenceTable.preprocess, contains_value]
  apply congrArg Array.ofFn
  funext mask
  exact (table_map SeparatorStoredMasks.decode family
    (fun a b => decide (SeparatorStoredMasks.decode a ⊆ b)) mask).symm

theorem avoidsStore_value (family : Array (Fin (2 ^ g))) :
    (preprocess avoids family).1 =
      SeparatorStoredMasks.avoidsStore (family.map SeparatorStoredMasks.decode) := by
  simp only [preprocess_value, SeparatorStoredMasks.avoidsStore,
    SeparatorIncidenceTable.preprocess, avoids_value]
  apply congrArg Array.ofFn
  funext mask
  exact (table_map SeparatorStoredMasks.decode family
    (fun a b => decide (Disjoint (SeparatorStoredMasks.decode a) b)) mask).symm

theorem tables_value (family : Array (Fin (2 ^ g))) :
    (tables family).1 =
      (SeparatorStoredMasks.containsStore (family.map SeparatorStoredMasks.decode),
        SeparatorStoredMasks.avoidsStore (family.map SeparatorStoredMasks.decode)) := by
  simp only [tables, containsStore_value, avoidsStore_value]

/-- The full preprocessing is below a constant times the stored table capacity. -/
theorem tables_work_of_size (family : Array (Fin (2 ^ g)))
    (hsize : family.size ≤ 11 * 2 ^ g) :
    (tables family).2 ≤ 220 * 2 ^ (2 * g) := by
  have h := tables_work family
  have hpow : 1 ≤ 2 ^ g := Nat.one_le_two_pow
  have hmul := Nat.mul_le_mul_right (2 ^ g) hsize
  have hp : 2 ^ g * 2 ^ g = 2 ^ (2 * g) := by rw [← pow_add]; congr 1; omega
  have hg := Nat.mul_le_mul_right (2 ^ g) hpow
  rw [hp] at hg
  nlinarith only [h, hmul, hg, hpow, hp]

end LowSpaceSubsetSum.StoredIncidenceBuild

end OAI
