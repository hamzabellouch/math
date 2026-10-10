import OAI.Combinatorics.EditApproximation.Binary.BinaryBandInputs

namespace OAI

/-! Bit-operation costs for preparing the actual stored band vertices.  The
large numerical values in the generic dot-product bound occur only inside
`Nat.size`; the resulting bound is polynomial in the stored word width. -/

namespace EditApproximation
namespace BinaryFraction

def storedSumWordBudget (n B : ℕ) : ℕ :=
  (B + 1) + Nat.size n + 2 * (B + 2) + 2 * (1 + n * ((B + 1) + (B + 1))) + 1

def storedSumBitBudget (n B : ℕ) : ℕ :=
  1 + n * (100000 * (storedSumWordBudget n B + 1) ^ 2)

theorem bandMassTotalWithWork_cost {M : ℕ} (mass : Vector BinaryFraction M)
    (B : ℕ) (hmass : ∀ i, (mass.get i).width ≤ B) :
    (bandMassTotalWithWork mass).2 ≤ storedSumBitBudget M B := by
  have hvalue (i : Fin M) : |(mass.get i).value| ≤ ((2 ^ (B + 1) : ℕ) : ℚ) := by
    have h := (value_abs_le_pow_width (mass.get i)).trans
      (pow_le_pow_right₀ (by norm_num : (1 : ℚ) ≤ 2)
        (show (mass.get i).width ≤ B + 1 by have := hmass i; omega))
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using h
  have honew : one.width ≤ B + 1 := by
    change 1 ≤ B + 1
    omega
  have hone : |one.value| ≤ ((2 ^ (B + 1) : ℕ) : ℚ) := by
    have hp : 1 ≤ 2 ^ (B + 1) := Nat.one_le_pow _ _ (by decide)
    rw [← representation_value one, one_representation, UnreducedRational.value_one, abs_one]
    exact_mod_cast hp
  have h := dotListWithWork_cost_in mass (Vector.replicate M one)
    (List.finRange M) M (B + 1) (2 ^ (B + 1)) (by simp)
    (by intro i _; have := hmass i; omega)
    (by intro i _; simpa using honew)
    (by intro i _; exact hvalue i)
    (by intro i _; simpa using hone)
  have hs1 := natural_product_bit_length (M * 2 ^ (B + 1)) (2 ^ (B + 1))
  have hs2 := natural_product_bit_length M (2 ^ (B + 1))
  have hp : Nat.size (2 ^ (B + 1)) = B + 2 := by rw [Nat.size_pow]
  have hword : dotWordBudget M (B + 1) (2 ^ (B + 1)) ≤ storedSumWordBudget M B := by
    unfold dotWordBudget storedSumWordBudget
    omega
  change (dotListWithWork mass (Vector.replicate M one) (List.finRange M)).2 ≤ _
  simp only [List.length_finRange] at h
  exact h.trans (Nat.add_le_add_left (Nat.mul_le_mul_left M
    (Nat.mul_le_mul_left 100000 (Nat.pow_le_pow_left (by omega) 2))) 1)

def bandCoordinateBitBudget (M B : ℕ) : ℕ :=
  2100 * (B + bandMassTotalStorageBudget M B + 2) ^ 2

theorem bandCoordinateWithWork_cost {M : ℕ} {σ : Type*} [DecidableEq σ]
    (mass : Vector BinaryFraction M) (action : Fin M → σ) (coordinate : Fin M × σ)
    (B : ℕ) (hmass : ∀ i, (mass.get i).width ≤ B) :
    (bandCoordinateWithWork mass (bandMassTotalWithWork mass).1 action coordinate).2 ≤
      bandCoordinateBitBudget M B := by
  have ht := (dotListWithWork_width_le_storageBits mass (Vector.replicate M one)
    (List.finRange M)).trans (bandMassTotalWithWork_storage mass B hmass)
  change (bandMassTotalWithWork mass).1.width ≤ bandMassTotalStorageBudget M B at ht
  unfold bandCoordinateWithWork
  split_ifs
  · exact divWithWork_cost _ _ (B + bandMassTotalStorageBudget M B)
      ((hmass coordinate.1).trans (Nat.le_add_right _ _)) (by omega)
  · unfold bandCoordinateBitBudget
    have hp : 1 ≤ (B + bandMassTotalStorageBudget M B + 2) ^ 2 := by
      exact Nat.one_le_pow _ _ (by omega)
    omega

def bandPreparationBitBudget (M d vertices B : ℕ) : ℕ :=
  storedSumBitBudget M B + vertices * (d * (bandCoordinateBitBudget M B + 6)) + 6 * vertices

theorem bandVerticesWithWork_cost {M d : ℕ} {σ : Type*} [DecidableEq σ]
    (coordinates : Vector (Fin M × σ) d) (mass : Vector BinaryFraction M)
    (band : List (Fin M → σ)) (B : ℕ) (hmass : ∀ i, (mass.get i).width ≤ B) :
    (bandVerticesWithWork coordinates mass band).2 ≤
      bandPreparationBitBudget M d band.length B := by
  have hc (action : Fin M → σ) :
      (vectorMapWithWork d (fun i => bandCoordinateWithWork mass
        (bandMassTotalWithWork mass).1 action (coordinates.get i))).2 ≤
        d * (bandCoordinateBitBudget M B + 6) :=
    vectorMapWithWork_cost_le d _ _ (fun i =>
      bandCoordinateWithWork_cost mass action (coordinates.get i) B hmass)
  have hs : ((band.map fun action => vectorMapWithWork d fun i =>
      bandCoordinateWithWork mass (bandMassTotalWithWork mass).1 action
        (coordinates.get i)).map Prod.snd).sum ≤
      band.length * (d * (bandCoordinateBitBudget M B + 6)) := by
    induction band with
    | nil => simp
    | cons action band ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      have ha := hc action
      rw [Nat.add_mul, Nat.one_mul]
      omega
  have ht := bandMassTotalWithWork_cost mass B hmass
  change (bandMassTotalWithWork mass).2 + _ + 6 * band.length ≤ _
  unfold bandPreparationBitBudget
  omega

end BinaryFraction
end EditApproximation

end OAI
