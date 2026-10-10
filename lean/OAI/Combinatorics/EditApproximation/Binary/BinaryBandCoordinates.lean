import OAI.Combinatorics.EditApproximation.Binary.BinaryRoundedWork
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! Materialization of the online coordinate array includes its equality
tests and duplicate-removal scan. Endpoints and child indices are compared
by the verified binary natural comparator. -/

namespace EditApproximation



@[simp] theorem coordinateEqualWithWork_value {M n : ℕ} (a b : Fin M × TargetInterval n) :
    (coordinateEqualWithWork a b).1 = true ↔ a = b := by
  simp only [coordinateEqualWithWork, Bool.and_eq_true, naturalEqualWithWork_value]
  constructor
  · rintro ⟨⟨hc, hl⟩, hh⟩
    have hi : a.1 = b.1 := Fin.ext hc
    have hq : a.2 = b.2 := by
      rcases a with ⟨i, q⟩
      rcases b with ⟨j, r⟩
      cases q
      cases r
      cases hl
      cases hh
      rfl
    exact Prod.ext hi hq
  · intro h
    subst b
    exact ⟨⟨rfl, rfl⟩, rfl⟩

theorem coordinateEqualWithWork_cost {M n : ℕ} (a b : Fin M × TargetInterval n)
    (B : ℕ) (hM : Nat.size M ≤ B) (hn : Nat.size n ≤ B) :
    (coordinateEqualWithWork a b).2 ≤ 24 * B + 8 := by
  have hc := naturalEqualWithWork_cost a.1.val b.1.val B
    ((Nat.size_le_size a.1.isLt.le).trans hM) ((Nat.size_le_size b.1.isLt.le).trans hM)
  have hl := naturalEqualWithWork_cost a.2.lo b.2.lo B
    ((Nat.size_le_size (a.2.ordered.trans a.2.valid)).trans hn)
    ((Nat.size_le_size (b.2.ordered.trans b.2.valid)).trans hn)
  have hh := naturalEqualWithWork_cost a.2.hi b.2.hi B
    ((Nat.size_le_size a.2.valid).trans hn) ((Nat.size_le_size b.2.valid).trans hn)
  change _ + _ + _ + 2 ≤ _
  omega



theorem memberByWithWork_value {α : Type*} (equal : α → α → Bool × ℕ)
    (heq : ∀ a b, (equal a b).1 = true ↔ a = b) (a : α) (xs : List α) :
    (memberByWithWork equal a xs).1 = true ↔ a ∈ xs := by
  induction xs with
  | nil => simp only [memberByWithWork, Bool.false_eq_true, List.not_mem_nil]
  | cons b xs ih => simp only [memberByWithWork, Bool.or_eq_true, heq, ih, List.mem_cons]

theorem memberByWithWork_cost {α : Type*} (equal : α → α → Bool × ℕ)
    (C : ℕ) (hC : ∀ a b, (equal a b).2 ≤ C) (a : α) (xs : List α) :
    (memberByWithWork equal a xs).2 ≤ 1 + xs.length * (C + 1) := by
  induction xs with
  | nil => simp only [memberByWithWork, List.length_nil, Nat.zero_mul, Nat.add_zero, le_refl]
  | cons b xs ih =>
    have h := hC a b
    change _ + _ + 1 ≤ _
    simp only [List.length_cons, Nat.add_mul, Nat.one_mul]
    omega



theorem dedupByWithWork_value {α : Type*} [DecidableEq α] (equal : α → α → Bool × ℕ)
    (heq : ∀ a b, (equal a b).1 = true ↔ a = b) (xs : List α) :
    (dedupByWithWork equal xs).1 = xs.dedup := by
  induction xs with
  | nil => rfl
  | cons a rest ih =>
    have hm := memberByWithWork_value equal heq a rest
    have ht : (memberByWithWork equal a rest).1 = decide (a ∈ rest) :=
      Bool.eq_iff_iff.mpr (by simpa only [decide_eq_true_eq] using hm)
    simp only [dedupByWithWork, ht, ih, List.dedup_cons, decide_eq_true_eq]

theorem dedupByWithWork_cost {α : Type*} (equal : α → α → Bool × ℕ)
    (C : ℕ) (hC : ∀ a b, (equal a b).2 ≤ C) (xs : List α) :
    (dedupByWithWork equal xs).2 ≤ (xs.length + 1) ^ 2 * (C + 4) := by
  induction xs with
  | nil => simp only [dedupByWithWork, List.length_nil]; nlinarith
  | cons a rest ih =>
    have hm := memberByWithWork_cost equal C hC a rest
    change _ + _ + 2 ≤ _
    simp only [List.length_cons]
    nlinarith only [ih, hm, Nat.zero_le C, Nat.zero_le rest.length]

namespace BinaryFraction



@[simp] theorem bandCoordinatesWithWork_value {M n : ℕ} (band : List (Fin M → TargetInterval n)) :
    (bandCoordinatesWithWork band).1 = listedBandCoordinates band := by
  simp only [bandCoordinatesWithWork, dedupByWithWork_value _ coordinateEqualWithWork_value,
    arithmeticFlatMapWithWork_value, arithmeticMapWithWork_value, listedBandCoordinates,
    List.ofFn_eq_map]

def bandCoordinatesBitBudget (M vertices B : ℕ) : ℕ :=
  vertices * (5 * M + 3) + (vertices * M + 1) ^ 2 * (24 * B + 12) + 1

theorem bandCoordinatesWithWork_cost {M n : ℕ} (band : List (Fin M → TargetInterval n))
    (B : ℕ) (hM : Nat.size M ≤ B) (hn : Nat.size n ≤ B) :
    (bandCoordinatesWithWork band).2 ≤ bandCoordinatesBitBudget M band.length B := by
  let raw := arithmeticFlatMapWithWork (fun action : Fin M → TargetInterval n =>
    arithmeticMapWithWork (fun i : Fin M => ((i, action i), 1)) (List.finRange M)) band
  have hlength : raw.1.length = band.length * M := by
    dsimp only [raw]
    simp only [arithmeticFlatMapWithWork_value, arithmeticMapWithWork_value]
    induction band with
    | nil => simp
    | cons a rest ih =>
      simp only [List.flatMap_cons, List.length_append, List.length_map, List.length_finRange,
        List.length_cons, Nat.add_mul, Nat.one_mul]
      omega
  have hraw := arithmeticFlatMapWithWork_cost
    (fun action : Fin M → TargetInterval n =>
      arithmeticMapWithWork (fun i : Fin M => ((i, action i), 1)) (List.finRange M))
    band (4 * M) M (by
      intro action _
      have h := arithmeticMapWithWork_cost
        (fun i : Fin M => ((i, action i), 1)) (List.finRange M) 1 (by intros; rfl)
      simpa only [List.length_finRange, Nat.mul_comm] using h) (by
      intro action _
      simp only [arithmeticMapWithWork_value, List.length_map, List.length_finRange, le_refl])
  change raw.2 ≤ _ at hraw
  have hunique := dedupByWithWork_cost coordinateEqualWithWork (24 * B + 8)
    (fun a b => coordinateEqualWithWork_cost a b B hM hn) raw.1
  rw [hlength] at hunique
  change raw.2 + (dedupByWithWork coordinateEqualWithWork raw.1).2 + 1 ≤ _
  unfold bandCoordinatesBitBudget
  nlinarith only [hraw, hunique]

end BinaryFraction
end EditApproximation

end OAI
