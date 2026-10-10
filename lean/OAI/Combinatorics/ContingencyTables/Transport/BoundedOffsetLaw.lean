import OAI.Combinatorics.ContingencyTables.Transport.RationalProducts
import OAI.Combinatorics.ContingencyTables.Machines.FairBits
import Mathlib.Data.Nat.Log

namespace OAI

/-! # Actual bounded scaling laws for the dense offsets -/

namespace ContingencyTables.FairBits

open scoped BigOperators
open ResidualMixture FirstSuccess

def scaledLaw (M k : ℕ) (hM : 0 < M) : RationalLaw (Fin M) where
  mass := fun β => outputMass M (2 ^ k) β.val
  nonnegative := fun β => outputMass_nonnegative _ _ _
  total := by
    rw [Fin.sum_univ_eq_sum_range]
    exact outputMass_total hM (pow_pos (by decide) _)

def uniformIntLaw (M : ℕ) (hM : 0 < M) : RationalLaw (Fin M) where
  mass := fun _ => 1 / (M : ℚ)
  nonnegative := fun _ => by positivity
  total := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    exact mul_one_div_cancel (by exact_mod_cast ne_of_gt hM)

theorem scaledLaw_variation (M k : ℕ) (hM : 0 < M) :
    variation (scaledLaw M k hM) (uniformIntLaw M hM) ≤ (M : ℚ) / (2 * (2 : ℚ) ^ k) := by
  have h := variation_bound hM (pow_pos (by decide : 0 < 2) k)
  change (1 / 2 : ℚ) * (∑ β ∈ Finset.range M, |outputMass M (2 ^ k) β - 1 / (M : ℚ)|) ≤ _ at h
  unfold variation
  simp only [scaledLaw, uniformIntLaw]
  have hs : (∑ β : Fin M, |outputMass M (2 ^ k) β.val - 1 / (M : ℚ)|) =
      ∑ β ∈ Finset.range M, |outputMass M (2 ^ k) β - 1 / (M : ℚ)| :=
    Fin.sum_univ_eq_sum_range (fun β => |outputMass M (2 ^ k) β - 1 / (M : ℚ)|) M
  rw [hs]
  simpa only [div_eq_mul_inv, mul_comm, Nat.cast_pow, Nat.cast_ofNat, one_mul] using h

def offsetBitLength (w h d : ℕ) : ℕ := Nat.clog 2 (w + 1) + 4 * (h + d)

/-- This law is the exact output law of multiplying the finite fair-bit
integer by w and taking the integer quotient. -/
theorem dense_scaled_offset_variation (w h d : ℕ) (hw : 0 < w) :
    variation (scaledLaw w (offsetBitLength w h d) hw) (uniformIntLaw w hw) ≤
      1 / (2 : ℚ) ^ (4 * (h + d)) := by
  apply (scaledLaw_variation w (offsetBitLength w h d) hw).trans
  have hpow : w ≤ 2 ^ Nat.clog 2 (w + 1) :=
    (Nat.le_succ w).trans (Nat.le_pow_clog (by decide) (w + 1))
  have hp : (w : ℚ) ≤ (2 : ℚ) ^ Nat.clog 2 (w + 1) := by exact_mod_cast hpow
  unfold offsetBitLength
  rw [pow_add]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  have hm := mul_le_mul_of_nonneg_right hp
    (show (0 : ℚ) ≤ 2 ^ (4 * (h + d)) by positivity)
  nlinarith [pow_pos (by norm_num : (0 : ℚ) < 2) (4 * (h + d))]

theorem dense_offset_product_variation (q h d : ℕ) (w : Fin q → ℕ)
    (hw : ∀ i, 0 < w i) (hq : q ≤ d) :
    variation (piLaw (fun i => scaledLaw (w i) (offsetBitLength (w i) h d) (hw i)))
      (piLaw (fun i => uniformIntLaw (w i) (hw i))) ≤
        (d : ℚ) / (2 : ℚ) ^ (4 * (h + d)) := by
  calc
    _ ≤ ∑ i : Fin q, variation
        (scaledLaw (w i) (offsetBitLength (w i) h d) (hw i))
        (uniformIntLaw (w i) (hw i)) := variation_pi _ _ _
    _ ≤ ∑ _i : Fin q, 1 / (2 : ℚ) ^ (4 * (h + d)) :=
      Finset.sum_le_sum (fun i _ => dense_scaled_offset_variation (w i) h d (hw i))
    _ = (q : ℚ) / (2 : ℚ) ^ (4 * (h + d)) := by simp; ring
    _ ≤ _ := div_le_div_of_nonneg_right (by exact_mod_cast hq) (by positivity)

end ContingencyTables.FairBits

end OAI
