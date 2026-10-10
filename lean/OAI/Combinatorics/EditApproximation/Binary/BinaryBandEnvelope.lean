import OAI.Combinatorics.EditApproximation.Binary.BinaryDyadicCeiling
import OAI.Combinatorics.EditApproximation.Binary.BinaryOnlineInputs
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! Literal Boolean construction of the child envelope of a finite band.
It scans the actual child values, compares with `b/M`, and runs the exact
bounded dyadic scan. Table reads are accounted for by the query program. -/

namespace EditApproximation
namespace BinaryFraction



theorem maxWithWork_value (a b : BinaryFraction) :
    (maxWithWork a b).1.value = max a.value b.value := by
  by_cases h : a.value < b.value
  · simp only [maxWithWork, (ltWithWork_value a b).mpr h, ↓reduceIte, max_eq_right h.le]
  · have hb : (a.ltWithWork b).1 = false := Bool.eq_false_iff.mpr (fun hh => h ((ltWithWork_value a b).mp hh))
    simp only [maxWithWork, hb, Bool.false_eq_true, ↓reduceIte, max_eq_left (le_of_not_gt h)]

theorem maxWithWork_width (a b : BinaryFraction) :
    (maxWithWork a b).1.width ≤ max a.width b.width := by
  unfold maxWithWork
  dsimp only
  split_ifs
  · exact le_max_right _ _
  · exact le_max_left _ _

theorem maxWithWork_cost (a b : BinaryFraction) (B : ℕ) (ha : a.width ≤ B) (hb : b.width ≤ B) :
    (maxWithWork a b).2 ≤ 1000 * (B + 1) ^ 2 + 1 :=
  Nat.add_le_add_right (ltWithWork_cost a b B ha hb) 1



theorem maximumWithWork_value (fallback : BinaryFraction) (values : List BinaryFraction) :
    (maximumWithWork fallback values).1.value = rationalMaximum fallback.value (values.map value) := by
  induction values with
  | nil => rfl
  | cons head rest ih =>
    simp only [maximumWithWork, maxWithWork_value, ih, List.map_cons, rationalMaximum]

theorem maximumWithWork_width (fallback : BinaryFraction) (values : List BinaryFraction)
    (B : ℕ) (hf : fallback.width ≤ B) (hvalues : ∀ a ∈ values, a.width ≤ B) :
    (maximumWithWork fallback values).1.width ≤ B := by
  induction values with
  | nil => exact hf
  | cons head rest ih =>
    exact (maxWithWork_width head (maximumWithWork fallback rest).1).trans
      (max_le (hvalues head List.mem_cons_self) (ih (fun a ha => hvalues a (List.mem_cons_of_mem _ ha))))

theorem maximumWithWork_cost (fallback : BinaryFraction) (values : List BinaryFraction)
    (B : ℕ) (hf : fallback.width ≤ B) (hvalues : ∀ a ∈ values, a.width ≤ B) :
    (maximumWithWork fallback values).2 ≤ 1 + values.length * (1000 * (B + 1) ^ 2 + 2) := by
  induction values with
  | nil => simp [maximumWithWork]
  | cons head rest ih =>
    have htail := ih (fun a ha => hvalues a (List.mem_cons_of_mem _ ha))
    have hw := maximumWithWork_width fallback rest B hf (fun a ha => hvalues a (List.mem_cons_of_mem _ ha))
    have hc := maxWithWork_cost head (maximumWithWork fallback rest).1 B
      (hvalues head List.mem_cons_self) hw
    change (maximumWithWork fallback rest).2 + (maxWithWork head (maximumWithWork fallback rest).1).2 + 1 ≤ _
    simp only [List.length_cons]
    rw [Nat.add_mul, Nat.one_mul]
    omega

def bandEnvelopeWithWork {M ny : ℕ} (b : ℕ)
    (band : List (Fin M → TargetInterval ny))
    (initial : Fin M → TargetInterval ny → BinaryFraction) (i : Fin M) : BinaryFraction × ℕ :=
  let floor := divWithWork (nat b) (nat M)
  let maximum := maximumWithWork zero (band.map fun action => initial i (action i))
  let input := maxWithWork floor.1 maximum.1
  let result := dyadicCeilingWithWork input.1
  (result.1, floor.2 + maximum.2 + input.2 + result.2 + band.length + 4)

theorem bandEnvelopeWithWork_value {M ny : ℕ} (b : ℕ)
    (band : List (Fin M → TargetInterval ny))
    (initial : Fin M → TargetInterval ny → BinaryFraction) (i : Fin M)
    (hb : 0 < b) :
    (bandEnvelopeWithWork b band initial i).1.value =
      bandChildEnvelope b band (fun j q => (initial j q).value) i := by
  have hM : 0 < M := Nat.pos_of_ne_zero (fun h => by cases h; exact Fin.elim0 i)
  have hfloor : (divWithWork (nat b) (nat M)).1.value = (b : ℚ) / M := by
    rw [divWithWork_value, ← representation_value (nat b), nat_representation,
      UnreducedRational.value_nat, ← representation_value (nat M), nat_representation,
      UnreducedRational.value_nat]
  have hp : 0 < (maxWithWork (divWithWork (nat b) (nat M)).1
      (maximumWithWork zero (band.map fun action => initial i (action i))).1).1.value := by
    rw [maxWithWork_value, hfloor]
    exact lt_of_lt_of_le (div_pos (by exact_mod_cast hb) (by exact_mod_cast hM)) (le_max_left _ _)
  change (dyadicCeilingWithWork _).1.value = _
  rw [dyadicCeilingWithWork_value _ hp, maxWithWork_value, hfloor, maximumWithWork_value]
  simp only [zero_representation, ← representation_value zero, UnreducedRational.value_zero,
    List.map_map, Function.comp_def, bandChildEnvelope]

def bandEnvelopeWordBudget (b M B : ℕ) : ℕ := B + Nat.size b + Nat.size M + 8

theorem bandEnvelopeWithWork_width {M ny : ℕ} (b : ℕ)
    (band : List (Fin M → TargetInterval ny))
    (initial : Fin M → TargetInterval ny → BinaryFraction) (i : Fin M)
    (B : ℕ) (hbits : ∀ action ∈ band, (initial i (action i)).width ≤ B) :
    (bandEnvelopeWithWork b band initial i).1.width ≤ 3 * bandEnvelopeWordBudget b M B + 1 := by
  let W := bandEnvelopeWordBudget b M B
  have hfloor := divWithWork_self_width (nat b) (nat M)
  rw [divWithWork_representation, nat_representation, nat_representation] at hfloor
  have hf := UnreducedRational.storageBits_div (UnreducedRational.nat b) (UnreducedRational.nat M)
  simp only [UnreducedRational.storageBits_nat] at hf
  have hfW : (divWithWork (nat b) (nat M)).1.width ≤ W := by
    dsimp only [W, bandEnvelopeWordBudget]
    omega
  have hmW := maximumWithWork_width zero (band.map fun action => initial i (action i)) W
    (by change 1 ≤ W; dsimp only [W, bandEnvelopeWordBudget]; omega)
    (by intro a ha; obtain ⟨action, haction, rfl⟩ := List.mem_map.mp ha
        exact (hbits action haction).trans (by dsimp only [W, bandEnvelopeWordBudget]; omega))
  have hin := (maxWithWork_width (divWithWork (nat b) (nat M)).1
    (maximumWithWork zero (band.map fun action => initial i (action i))).1).trans (max_le hfW hmW)
  have h := dyadicCeilingWithWork_width (maxWithWork (divWithWork (nat b) (nat M)).1
    (maximumWithWork zero (band.map fun action => initial i (action i))).1).1
  change (dyadicCeilingWithWork _).1.width ≤ _
  omega


def bandEnvelopeBitBudget (b M size B : ℕ) : ℕ :=
  let W := bandEnvelopeWordBudget b M B
  2100 * (Nat.size b + Nat.size M + 6) ^ 2 +
    (1 + size * (1000 * (W + 1) ^ 2 + 2)) + (1000 * (W + 1) ^ 2 + 1) +
    (1 + 2 * W * (1000 * (3 * W + 2) ^ 2 + 2) + 3 * W + 5) + size + 4

theorem bandEnvelopeWithWork_cost {M ny : ℕ} (b : ℕ)
    (band : List (Fin M → TargetInterval ny))
    (initial : Fin M → TargetInterval ny → BinaryFraction) (i : Fin M)
    (B : ℕ) (hbits : ∀ action ∈ band, (initial i (action i)).width ≤ B) :
    (bandEnvelopeWithWork b band initial i).2 ≤ bandEnvelopeBitBudget b M band.length B := by
  let W := bandEnvelopeWordBudget b M B
  let floor := (divWithWork (nat b) (nat M)).1
  let maximum := (maximumWithWork zero (band.map fun action => initial i (action i))).1
  let input := (maxWithWork floor maximum).1
  have hfloor := divWithWork_self_width (nat b) (nat M)
  rw [divWithWork_representation, nat_representation, nat_representation] at hfloor
  have hf := UnreducedRational.storageBits_div (UnreducedRational.nat b) (UnreducedRational.nat M)
  simp only [UnreducedRational.storageBits_nat] at hf
  have hfW : floor.width ≤ W := by
    dsimp only [W, bandEnvelopeWordBudget]
    change floor.width ≤ _ at hfloor
    omega
  have hmW : maximum.width ≤ W := maximumWithWork_width zero
    (band.map fun action => initial i (action i)) W
    (by change 1 ≤ W; dsimp only [W, bandEnvelopeWordBudget]; omega)
    (by intro a ha; obtain ⟨action, haction, rfl⟩ := List.mem_map.mp ha
        exact (hbits action haction).trans (by dsimp only [W, bandEnvelopeWordBudget]; omega))
  have hiW : input.width ≤ W := (maxWithWork_width floor maximum).trans (max_le hfW hmW)
  have hfc := divWithWork_cost (nat b) (nat M) (Nat.size b + Nat.size M + 4)
    ((nat_width_le b).trans (by omega)) ((nat_width_le M).trans (by omega))
  rw [show Nat.size b + Nat.size M + 4 + 2 = Nat.size b + Nat.size M + 6 by omega] at hfc
  have hmc := maximumWithWork_cost zero (band.map fun action => initial i (action i)) W
    (by change 1 ≤ W; dsimp only [W, bandEnvelopeWordBudget]; omega)
    (by intro a ha; obtain ⟨action, haction, rfl⟩ := List.mem_map.mp ha
        exact (hbits action haction).trans (by dsimp only [W, bandEnvelopeWordBudget]; omega))
  simp only [List.length_map] at hmc
  have hic := maxWithWork_cost floor maximum W hfW hmW
  have hdc := dyadicCeilingWithWork_cost_le input W hiW
  change (divWithWork (nat b) (nat M)).2 +
    (maximumWithWork zero (band.map fun action => initial i (action i))).2 +
    (maxWithWork floor maximum).2 + (dyadicCeilingWithWork input).2 + band.length + 4 ≤ _
  change _ ≤ 2100 * (Nat.size b + Nat.size M + 6) ^ 2 +
    (1 + band.length * (1000 * (W + 1) ^ 2 + 2)) + (1000 * (W + 1) ^ 2 + 1) +
    (1 + 2 * W * (1000 * (3 * W + 2) ^ 2 + 2) + 3 * W + 5) + band.length + 4
  omega

end BinaryFraction
end EditApproximation

end OAI
