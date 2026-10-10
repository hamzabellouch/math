import OAI.Combinatorics.LowSpaceSubsetSum.Counting.Entropy
import OAI.Combinatorics.LowSpaceSubsetSum.Separators.SeparatorIncidence

namespace OAI

/-! # Executable background allocation and its entropy error -/

namespace LowSpaceSubsetSum

/-- The implementation computes the bit length of a positive binomial count. -/
def binomialBits (m k : ℕ) : ℕ := (m.choose k).log2

theorem binomialBits_eq_floor (m k : ℕ) :
    (binomialBits m k : ℤ) = ⌊Real.logb 2 (m.choose k)⌋ := by
  have h := Real.floor_logb_natCast (b := 2) (r := (m.choose k : ℝ)) (by positivity)
  simpa only [Nat.cast_ofNat, Int.log_natCast, binomialBits, Nat.log2_eq_log_two] using h.symm

theorem binomialBits_entropy_error (m k : ℕ) (hk : k ≤ m) :
    |(binomialBits m k : ℝ) - (m : ℝ) * binaryEntropy ((k : ℝ) / m)| <
      Real.logb 2 ((m : ℝ) + 1) + 1 := by
  have h := floor_logb_choose_error m k hk
  rw [← binomialBits_eq_floor] at h
  exact_mod_cast h

/-- Signed arithmetic prevents truncation before the final division. -/
def allocateLeft (r a b : ℕ) : ℕ := (((r : ℤ) + b - a) / 2).toNat

def allocateRight (r a b : ℕ) : ℕ := r - allocateLeft r a b

theorem allocateLeft_eq_floor (r a b : ℕ) :
    allocateLeft r a b = ⌊((r : ℝ) + b - a) / 2⌋₊ := by
  unfold allocateLeft
  rw [← Int.floor_toNat]
  congr 1
  have heq : ((r : ℝ) + b - a) / 2 = (((r : ℤ) + b - a : ℤ) : ℝ) / (2 : ℕ) := by
    simp only [Int.cast_sub, Int.cast_add, Int.cast_natCast, Nat.cast_ofNat]
  rw [heq, Int.floor_div_natCast, Int.floor_intCast]
  rfl

theorem allocation_feasible (r a b : ℕ) (ha : a ≤ r + b) (hb : b ≤ r + a) :
    allocateLeft r a b ≤ r ∧ allocateLeft r a b + allocateRight r a b = r := by
  have hnonneg : (0 : ℤ) ≤ (r : ℤ) + b - a := by omega
  have hbound : ((r : ℤ) + b - a) / 2 ≤ r := by omega
  have hcast : (allocateLeft r a b : ℤ) = ((r : ℤ) + b - a) / 2 :=
    Int.toNat_of_nonneg (Int.ediv_nonneg hnonneg (by decide))
  have hleft : allocateLeft r a b ≤ r := by omega
  exact ⟨hleft, by unfold allocateRight; omega⟩

/-- Integer division contributes less than one to each balancing step. -/
theorem allocateLeft_error (r a b : ℕ) (ha : a ≤ r + b) :
    |(allocateLeft r a b : ℝ) - ((r : ℝ) + b - a) / 2| < 1 := by
  have hnonneg : (0 : ℝ) ≤ ((r : ℝ) + b - a) / 2 := by
    have h : (a : ℝ) ≤ r + b := by exact_mod_cast ha
    linarith
  rw [allocateLeft_eq_floor]
  have hl := Nat.floor_le hnonneg
  have hu := Nat.lt_floor_add_one (((r : ℝ) + b - a) / 2)
  rw [abs_of_nonpos (by linarith)]
  linarith

/-- One balancing step converts bit-length errors into an allocation error. -/
theorem allocateLeft_entropy_error (r a b : ℕ) (ha : a ≤ r + b)
    {A B e : ℝ} (haE : |(a : ℝ) - A| ≤ e) (hbE : |(b : ℝ) - B| ≤ e) :
    |(allocateLeft r a b : ℝ) - ((r : ℝ) / 2 + (B - A) / 2)| < e + 1 := by
  have hf := abs_lt.mp (allocateLeft_error r a b ha)
  have hA := abs_le.mp haE
  have hB := abs_le.mp hbE
  apply abs_lt.mpr
  constructor <;> linarith

theorem allocateRight_entropy_error (r a b : ℕ) (ha : a ≤ r + b) (hb : b ≤ r + a)
    {A B e : ℝ} (haE : |(a : ℝ) - A| ≤ e) (hbE : |(b : ℝ) - B| ≤ e) :
    |(allocateRight r a b : ℝ) - ((r : ℝ) / 2 + (A - B) / 2)| < e + 1 := by
  have hs := (allocation_feasible r a b ha hb).2
  have hsR : (allocateLeft r a b : ℝ) + allocateRight r a b = r := by exact_mod_cast hs
  have h := abs_lt.mp (allocateLeft_entropy_error r a b ha haE hbE)
  apply abs_lt.mpr
  constructor <;> linarith

/-- The manuscript's executable binomial balancing, with an explicit logarithmic error. -/
theorem binomial_allocation_error (r m k l : ℕ) (hk : k ≤ m) (hl : l ≤ m)
    (ha : binomialBits m k ≤ r + binomialBits m l)
    (hb : binomialBits m l ≤ r + binomialBits m k) :
    let A := (m : ℝ) * binaryEntropy ((k : ℝ) / m)
    let B := (m : ℝ) * binaryEntropy ((l : ℝ) / m)
    |(allocateLeft r (binomialBits m k) (binomialBits m l) : ℝ) -
      ((r : ℝ) / 2 + (B - A) / 2)| < Real.logb 2 ((m : ℝ) + 1) + 2 ∧
    |(allocateRight r (binomialBits m k) (binomialBits m l) : ℝ) -
      ((r : ℝ) / 2 + (A - B) / 2)| < Real.logb 2 ((m : ℝ) + 1) + 2 := by
  have hA := (binomialBits_entropy_error m k hk).le
  have hB := (binomialBits_entropy_error m l hl).le
  constructor
  · convert allocateLeft_entropy_error r _ _ ha hA hB using 1; ring
  · convert allocateRight_entropy_error r _ _ ha hb hA hB using 1; ring


/-- A sufficient, symmetric feasibility test computed from the two bit lengths. -/
theorem allocation_feasible_of_difference (r a b : ℕ)
    (h : |(b : ℤ) - a| ≤ r) :
    allocateLeft r a b ≤ r ∧ allocateLeft r a b + allocateRight r a b = r := by
  obtain ⟨hlo, hhi⟩ := abs_le.mp h
  exact allocation_feasible r a b (by omega) (by omega)

theorem binomialBits_difference (m k l : ℕ) (hk : k ≤ m) (hl : l ≤ m)
    (hkr : (k : ℝ) / m ∈ Set.Icc (1 / 6) (1 / 3))
    (hlr : (l : ℝ) / m ∈ Set.Icc (1 / 6) (1 / 3)) :
    |(binomialBits m l : ℝ) - binomialBits m k| <
      (3 / 8 : ℝ) * m + 2 * (Real.logb 2 ((m : ℝ) + 1) + 1) := by
  have hA := abs_lt.mp (binomialBits_entropy_error m k hk)
  have hB := abs_lt.mp (binomialBits_entropy_error m l hl)
  have hH := (binaryEntropy_abs_sub_lt hlr hkr).le
  have hmul : |(m : ℝ) * binaryEntropy ((l : ℝ) / m) -
      (m : ℝ) * binaryEntropy ((k : ℝ) / m)| ≤ (m : ℝ) * (3 / 8) := by
    rw [← mul_sub, abs_mul, abs_of_nonneg (Nat.cast_nonneg m)]
    exact mul_le_mul_of_nonneg_left hH (Nat.cast_nonneg m)
  have hdiff := abs_le.mp hmul
  apply abs_lt.mpr
  constructor <;> nlinarith

/-- Either parent's background size is bounded from below by the imbalance
bound, with only the single integer-rounding loss. -/
theorem allocated_sides_lower (r a b : ℕ) {d : ℝ}
    (hd : |(b : ℝ) - a| ≤ d) (hdr : d ≤ r) :
    (r : ℝ) / 2 - d / 2 - 1 < allocateLeft r a b ∧
    (r : ℝ) / 2 - d / 2 - 1 < allocateRight r a b := by
  have hab := abs_le.mp hd
  have haR : (a : ℝ) ≤ r + b := by linarith
  have hbR : (b : ℝ) ≤ r + a := by linarith
  have ha : a ≤ r + b := by exact_mod_cast haR
  have hb : b ≤ r + a := by exact_mod_cast hbR
  have he := abs_lt.mp (allocateLeft_error r a b ha)
  have hs := (allocation_feasible r a b ha hb).2
  have hsR : (allocateLeft r a b : ℝ) + allocateRight r a b = r := by exact_mod_cast hs
  constructor <;> linarith


/-- The two leaves split each child's background with at most half an item
of error, because the remainder is assigned to the second leaf. -/
def leafBackgroundSize (r : ℕ) (i : Fin 2) : ℕ := if i = 0 then r / 2 else r - r / 2

theorem leafBackgroundSize_sum (r : ℕ) :
    leafBackgroundSize r 0 + leafBackgroundSize r 1 = r := by
  simp [leafBackgroundSize]
  omega

theorem leafBackgroundSize_error (r : ℕ) (i : Fin 2) :
    |(leafBackgroundSize r i : ℝ) - (r : ℝ) / 2| ≤ 1 / 2 := by
  have hn : r / 2 * 2 ≤ r := Nat.div_mul_le_self r 2
  have hu : r < 2 * (r / 2 + 1) := by omega
  have hnR : (r / 2 : ℕ) * (2 : ℝ) ≤ r := by exact_mod_cast hn
  have huR : (r : ℝ) ≤ 2 * (r / 2 : ℕ) + 1 := by exact_mod_cast (show r ≤ 2 * (r / 2) + 1 by omega)
  fin_cases i
  · simp only [leafBackgroundSize, Fin.ext_iff, Fin.val_zero, ↓reduceIte]
    apply abs_le.mpr
    constructor <;> linarith
  · have hs : (r - r / 2 : ℕ) + r / 2 = r := by omega
    have hsR : ((r - r / 2 : ℕ) : ℝ) + (r / 2 : ℕ) = r := by exact_mod_cast hs
    simp only [leafBackgroundSize, Fin.ext_iff, Fin.val_zero, Nat.one_ne_zero, ↓reduceIte]
    apply abs_le.mpr
    constructor <;> linarith

/-- Replacing the current total by its ideal value costs half the previous
error. This is the two-level substitution used in the leaf-size estimate. -/
theorem allocation_error_compose (r a b : ℕ) (ha : a ≤ r + b)
    {ideal A B e0 e1 : ℝ} (hr : |(r : ℝ) - ideal| ≤ e0)
    (hA : |(a : ℝ) - A| ≤ e1) (hB : |(b : ℝ) - B| ≤ e1) :
    |(allocateLeft r a b : ℝ) - (ideal / 2 + (B - A) / 2)| < e0 / 2 + e1 + 1 := by
  have hfirst := abs_lt.mp (allocateLeft_entropy_error r a b ha hA hB)
  have hprev := abs_le.mp hr
  apply abs_lt.mpr
  constructor <;> linarith

theorem leaf_error_compose (r : ℕ) (i : Fin 2) {ideal e : ℝ}
    (hr : |(r : ℝ) - ideal| ≤ e) :
    |(leafBackgroundSize r i : ℝ) - ideal / 2| ≤ e / 2 + 1 / 2 := by
  have hf := abs_le.mp (leafBackgroundSize_error r i)
  have hp := abs_le.mp hr
  apply abs_le.mpr
  constructor <;> linarith

end LowSpaceSubsetSum

end OAI
