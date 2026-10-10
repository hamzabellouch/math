import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationExtraPrime
import Mathlib.Algebra.Order.Floor.Semifield

namespace OAI

/-! # Exact integer computation of the representation parameters

Distinct-sum counts determine the ordering and low-prime bit lengths.
Logarithms remain analysis quantities and are not evaluated by the program.
-/

namespace LowSpaceSubsetSum

/-- Sort by decreasing distinct-sum count, with the same index tie rule as
the deficiency ordering in the analysis. -/
def mixerOrderFromCounts (counts : Fin 3 → ℕ) : Equiv.Perm (Fin 3) :=
  Tuple.sort (fun i => -(counts i : ℤ))

/-- The floor of the rational cutoff, with natural truncation at zero. -/
def rationalLowParameter (n half : ℕ) : ℕ :=
  ((5000 * (half : ℤ) - 39 * n) / 5000).toNat

def lowParameterFromCount (n half count : ℕ) : ℕ :=
  max (rationalLowParameter n half) (Nat.log2 count / 2)

def extraParameterFromLow (n m : ℕ) (low : Fin 3 → ℕ) : ℕ :=
  ((125 * (n : ℤ) - 234 * m + 500 * min (low 0) (min (low 1) (low 2))) / 500).toNat

theorem rationalLowParameter_eq (n half : ℕ) :
    rationalLowParameter n half = ⌊(half : ℝ) - (39 / 5000 : ℝ) * n⌋₊ := by
  rw [rationalLowParameter, ← Int.floor_toNat]
  congr 1
  have he : (half : ℝ) - (39 / 5000 : ℝ) * n =
      ((5000 * (half : ℤ) - 39 * n : ℤ) : ℝ) / (5000 : ℕ) := by
    push_cast
    ring
  rw [he, Int.floor_div_natCast, Int.floor_intCast]
  norm_num

theorem floor_half_logb_count (count : ℕ) :
    ⌊Real.logb 2 (count : ℝ) / 2⌋₊ = Nat.log2 count / 2 := by
  rw [Nat.floor_div_ofNat]
  have hl := Real.natFloor_logb_natCast 2 count
  norm_num only [Nat.cast_ofNat] at hl
  rw [hl, Nat.log2_eq_log_two]

private theorem sort_eq_of_le_iff {α β : Type*} [LinearOrder α] [LinearOrder β]
    (f : Fin 3 → α) (g : Fin 3 → β)
    (h : ∀ i j, f i ≤ f j ↔ g i ≤ g j) : Tuple.sort f = Tuple.sort g := by
  apply Tuple.eq_sort_iff.mpr
  obtain ⟨hm, ht⟩ := (Tuple.eq_sort_iff (f := f) (σ := Tuple.sort f)).mp rfl
  constructor
  · intro i j hij
    exact (h _ _).mp (hm hij)
  · intro i j hij he
    apply ht i j hij
    exact le_antisymm ((h _ _).mpr he.le) ((h _ _).mpr he.ge)

namespace RepresentationSetup

variable {n : ℕ} (R : RepresentationSetup n)

theorem rawMixers_card_mixerSize (z : Layout n) (i : Fin 3) :
    (R.rawMixers z i).card = mixerSize n := by
  rw [rawMixers, permuteSubset_card, R.card]

theorem mixerOrder_eq_integer (z : Layout n) :
    R.mixerOrder z = mixerOrderFromCounts
      (fun i => distinctSumCount R.originalWeights (R.rawMixers z i)) := by
  unfold mixerOrder mixerOrderFromCounts
  apply sort_eq_of_le_iff
  intro i j
  have hi := distinctSumCount_pos_real R.originalWeights (R.rawMixers z i)
  have hj := distinctSumCount_pos_real R.originalWeights (R.rawMixers z j)
  have hl := Real.logb_le_logb (by norm_num : (1 : ℝ) < 2) hj hi
  simp only [deficiency, R.rawMixers_card_mixerSize]
  rw [sub_le_sub_iff_left, hl, neg_le_neg_iff]
  exact_mod_cast Iff.rfl

/-- The exact floor of each low exponent is computed by integer arithmetic
and the bit length of the distinct-sum count. -/
theorem floor_lowExponent_eq_integer (z : Layout n) (i : Fin 3) :
    ⌊R.lowExponent z i⌋₊ = lowParameterFromCount n R.halfSize
      (distinctSumCount R.originalWeights (R.orderedMixers z i)) := by
  have hc : (R.orderedMixers z i).card = 2 * R.halfSize := R.orderedMixers_card z i
  have hcR : ((R.orderedMixers z i).card : ℝ) = 2 * R.halfSize := by exact_mod_cast hc
  have he : R.lowExponent z i = max
      ((R.halfSize : ℝ) - (39 / 5000 : ℝ) * n)
      (Real.logb 2 (distinctSumCount R.originalWeights (R.orderedMixers z i)) / 2) := by
    unfold lowExponent deficiency
    rw [hcR, ← max_sub_sub_left]
    congr 1
    ring
  rw [he, lowParameterFromCount, rationalLowParameter_eq, ← floor_half_logb_count]
  exact Nat.floor_mono.map_max

theorem extraPrimeParameter_eq_integer (z : Layout n) :
    R.extraPrimeParameter z = extraParameterFromLow n (mixerSize n)
      (fun i => lowParameterFromCount n R.halfSize
        (distinctSumCount R.originalWeights (R.orderedMixers z i))) := by
  simp only [extraPrimeParameter, R.floor_lowExponent_eq_integer]
  let k := min
    (lowParameterFromCount n R.halfSize
      (distinctSumCount R.originalWeights (R.orderedMixers z 0)))
    (min (lowParameterFromCount n R.halfSize
      (distinctSumCount R.originalWeights (R.orderedMixers z 1)))
      (lowParameterFromCount n R.halfSize
        (distinctSumCount R.originalWeights (R.orderedMixers z 2))))
  change ⌊(n : ℝ) / 4 + (4 / 125 : ℝ) * mixerSize n -
      (mixerSize n : ℝ) / 2 + k⌋₊ =
    ((125 * (n : ℤ) - 234 * mixerSize n + 500 * k) / 500).toNat
  rw [← Int.floor_toNat]
  congr 1
  have he : (n : ℝ) / 4 + (4 / 125 : ℝ) * mixerSize n -
      (mixerSize n : ℝ) / 2 + k =
    ((125 * (n : ℤ) - 234 * mixerSize n + 500 * k : ℤ) : ℝ) / (500 : ℕ) := by
    push_cast
    ring
  rw [he, Int.floor_div_natCast, Int.floor_intCast]
  norm_num

end RepresentationSetup
end LowSpaceSubsetSum

end OAI
