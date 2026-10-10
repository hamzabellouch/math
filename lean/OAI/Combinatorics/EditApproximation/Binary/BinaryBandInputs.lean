import OAI.Combinatorics.EditApproximation.Binary.BinaryOptimizerWork
import OAI.Combinatorics.EditApproximation.Geometry.BandNumericalBits
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! Actual Boolean construction of the normalized band vertices.
The input masses are stored fractions; their sum and divisions use the
counted routines and no reduced-rational conversion is performed. -/

namespace EditApproximation
namespace BinaryFraction

open Finset

theorem value_abs_le_pow_width (a : BinaryFraction) : |a.value| ≤ (2 : ℚ) ^ a.width := by
  have hn := (bitWordValue_lt_pow_length a.numerator.bits).le
  have hw : a.numerator.bits.length ≤ a.width := le_max_left _ _
  have hn' : bitWordValue a.numerator.bits ≤ 2 ^ a.width :=
    hn.trans (Nat.pow_le_pow_right (by decide) hw)
  have hden : (1 : ℚ) ≤ bitWordValue a.denominator := by exact_mod_cast a.denominator_pos
  have habs : |(a.numerator.value : ℚ)| = bitWordValue a.numerator.bits := by
    cases h : a.numerator.negative <;> simp [SignedBinary.value, signedMagnitude, h]
  unfold value
  rw [abs_div, habs, abs_of_pos (lt_of_lt_of_le (by norm_num : (0 : ℚ) < 1) hden)]
  apply (div_le_iff₀ (lt_of_lt_of_le (by norm_num : (0 : ℚ) < 1) hden)).mpr
  have hnQ : (bitWordValue a.numerator.bits : ℚ) ≤ (2 : ℚ) ^ a.width := by exact_mod_cast hn'
  exact hnQ.trans (le_mul_of_one_le_right (by positivity) hden)



theorem bandMassTotalWithWork_value {M : ℕ} (mass : Vector BinaryFraction M) :
    (bandMassTotalWithWork mass).1.value = ∑ i, (mass.get i).value := by
  rw [bandMassTotalWithWork, ← representation_value, dotWithWork_representation,
    UnreducedRational.dot_value]
  simp [one_representation]

def bandMassTotalStorageBudget (M B : ℕ) : ℕ :=
  Nat.size M + B + 2 * (1 + M * (B + 1)) + 2

theorem bandMassTotalWithWork_storage {M : ℕ} (mass : Vector BinaryFraction M)
    (B : ℕ) (hmass : ∀ i, (mass.get i).width ≤ B) :
    (bandMassTotalWithWork mass).1.representation.storageBits ≤ bandMassTotalStorageBudget M B := by
  have hvalue (i : Fin M) : |(mass.get i).value| ≤ ((2 ^ B : ℕ) : ℚ) := by
    have h := (value_abs_le_pow_width (mass.get i)).trans
      (pow_le_pow_right₀ (by norm_num : (1 : ℚ) ≤ 2) (hmass i))
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using h
  have h := UnreducedRational.dotList_storageBits
    (mass.map representation) ((Vector.replicate M one).map representation)
    (List.finRange M) B 1 (2 ^ B) 1
    (by intro i _; simpa only [vector_map_get] using (representation_den_bits_le_width (mass.get i)).trans (hmass i))
    (by intro i _; simp [one_representation, UnreducedRational.one, UnreducedRational.ofRat])
    (by intro i _; simpa only [vector_map_get, representation_value] using hvalue i)
    (by intro i _; simp [one_representation])
  simp only [List.length_finRange, Nat.mul_one] at h
  have hsize := (natural_product_bit_length M (2 ^ B)).trans
    (Nat.add_le_add_left (by rw [Nat.size_pow] : Nat.size (2 ^ B) ≤ B + 1) M.size)
  rw [bandMassTotalWithWork, dotWithWork_representation]
  change (UnreducedRational.dotList (mass.map representation)
    ((Vector.replicate M one).map representation) (List.finRange M)).storageBits ≤ _
  unfold bandMassTotalStorageBudget
  omega

def bandVertexWordBudget (M B : ℕ) : ℕ := 2 * B + bandMassTotalStorageBudget M B + 3

def bandCoordinateWithWork {M : ℕ} {σ : Type*} [DecidableEq σ]
    (mass : Vector BinaryFraction M) (total : BinaryFraction)
    (action : Fin M → σ) (coordinate : Fin M × σ) : BinaryFraction × ℕ :=
  if coordinate.2 = action coordinate.1 then divWithWork (mass.get coordinate.1) total else (zero, 1)

theorem bandCoordinateWithWork_value {M : ℕ} {σ : Type*} [DecidableEq σ]
    (mass : Vector BinaryFraction M) (action : Fin M → σ) (coordinate : Fin M × σ) :
    (bandCoordinateWithWork mass (bandMassTotalWithWork mass).1 action coordinate).1.value =
      actionVector (fun i => (mass.get i).value) action coordinate := by
  unfold bandCoordinateWithWork actionVector
  split_ifs
  · rw [← representation_value, divWithWork_representation,
      UnreducedRational.value_div, representation_value, representation_value,
      bandMassTotalWithWork_value]
  · simp [zero, value, SignedBinary.value, signedMagnitude, bitWordValue]

theorem bandCoordinateWithWork_bounds {M : ℕ} {σ : Type*} [DecidableEq σ]
    (mass : Vector BinaryFraction M) (action : Fin M → σ) (coordinate : Fin M × σ)
    (B : ℕ) (hmass : ∀ i, (mass.get i).width ≤ B) (hpos : ∀ i, 0 < (mass.get i).value) :
    let output := (bandCoordinateWithWork mass (bandMassTotalWithWork mass).1 action coordinate).1
    output.width ≤ output.representation.storageBits ∧
      (0 ≤ output.value ∧ output.value ≤ 1) ∧
      output.representation.storageBits ≤ bandVertexWordBudget M B := by
  dsimp only
  have hvalues := actionVector_zero_one (fun i => (mass.get i).value) action coordinate hpos
  rw [← bandCoordinateWithWork_value mass action coordinate] at hvalues
  refine ⟨?_, hvalues, ?_⟩
  · unfold bandCoordinateWithWork
    split_ifs
    · exact divWithWork_self_width _ _
    · exact zero_width_le_storageBits
  · have ht := bandMassTotalWithWork_storage mass B hmass
    have hm := representation_storageBits_le (mass.get coordinate.1)
    have hi := hmass coordinate.1
    unfold bandCoordinateWithWork
    split_ifs
    · rw [divWithWork_representation]
      have hd := UnreducedRational.storageBits_div (mass.get coordinate.1).representation
        (bandMassTotalWithWork mass).1.representation
      unfold bandVertexWordBudget
      omega
    · change UnreducedRational.zero.storageBits ≤ _
      rw [UnreducedRational.storageBits_zero]
      unfold bandVertexWordBudget
      omega

def bandVerticesWithWork {M d : ℕ} {σ : Type*} [DecidableEq σ]
    (coordinates : Vector (Fin M × σ) d) (mass : Vector BinaryFraction M)
    (band : List (Fin M → σ)) : List (Vector BinaryFraction d) × ℕ :=
  let total := bandMassTotalWithWork mass
  let vertices := band.map fun action => vectorMapWithWork d fun i =>
    bandCoordinateWithWork mass total.1 action (coordinates.get i)
  (vertices.map Prod.fst, total.2 + (vertices.map Prod.snd).sum + 6 * band.length)

theorem bandVerticesWithWork_values {M d : ℕ} {σ : Type*} [DecidableEq σ]
    (coordinates : Vector (Fin M × σ) d) (mass : Vector BinaryFraction M)
    (band : List (Fin M → σ)) :
    (bandVerticesWithWork coordinates mass band).1.map (fun v i => (v.get i).value) =
      band.map (fun action i => actionVector (fun i => (mass.get i).value) action (coordinates.get i)) := by
  simp only [bandVerticesWithWork, List.map_map, Function.comp_def]
  apply List.map_congr_left
  intro action _
  funext i
  simp only [vectorMapWithWork_value, bandCoordinateWithWork_value]

theorem bandVerticesWithWork_input_bounds {M d : ℕ} {σ : Type*} [DecidableEq σ]
    (coordinates : Vector (Fin M × σ) d) (mass : Vector BinaryFraction M)
    (band : List (Fin M → σ)) (B : ℕ)
    (hmass : ∀ i, (mass.get i).width ≤ B) (hpos : ∀ i, 0 < (mass.get i).value)
    (v : Vector BinaryFraction d) (hv : v ∈ (bandVerticesWithWork coordinates mass band).1)
    (i : Fin d) :
    (v.get i).width ≤ (v.get i).representation.storageBits ∧
      (0 ≤ (v.get i).value ∧ (v.get i).value ≤ 1) ∧
      Nat.size (v.get i).representation.den ≤ bandVertexWordBudget M B ∧
      (v.get i).width ≤ bandVertexWordBudget M B := by
  simp only [bandVerticesWithWork, List.map_map, Function.comp_def] at hv
  obtain ⟨action, _, rfl⟩ := List.mem_map.mp hv
  simp only [vectorMapWithWork_value]
  have h := bandCoordinateWithWork_bounds mass action (coordinates.get i) B hmass hpos
  dsimp only at h
  refine ⟨h.1, h.2.1, ?_, h.1.trans h.2.2⟩
  apply le_trans ?_ h.2.2
  unfold UnreducedRational.storageBits
  omega

end BinaryFraction
end EditApproximation

end OAI
