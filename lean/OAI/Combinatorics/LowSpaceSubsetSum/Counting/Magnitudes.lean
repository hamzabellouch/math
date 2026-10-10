import OAI.Combinatorics.LowSpaceSubsetSum.Counting.Model
import Mathlib.Data.Nat.Log
import Mathlib.Data.Finset.Lattice.Fold

namespace OAI

/-!
# Input bit lengths and exact signed-weight bounds

The bit parameter is the manuscript's ceiling logarithm, computed on the
original nonnegative input. These bounds include raw occurrences that repeat
indices, so hashing before a local-overlap test is covered.
-/

namespace LowSpaceSubsetSum

open scoped BigOperators

def inputMaximum {n : ℕ} (I : Instance n) : ℕ :=
  max I.target (Finset.univ.sup I.values)

def inputBits {n : ℕ} (I : Instance n) : ℕ :=
  max 1 (Nat.clog 2 (1 + inputMaximum I))

def inputScale {n : ℕ} (I : Instance n) : ℕ := n + inputBits I + 2

theorem inputBits_pos {n : ℕ} (I : Instance n) : 0 < inputBits I := by
  exact lt_of_lt_of_le (by decide : 0 < 1) (le_max_left _ _)

theorem inputMaximum_lt_two_pow_bits {n : ℕ} (I : Instance n) :
    inputMaximum I < 2 ^ inputBits I := by
  have h := Nat.le_pow_clog (by decide : 1 < 2) (1 + inputMaximum I)
  have hmono := Nat.pow_le_pow_right (by decide : 0 < 2)
    (show Nat.clog 2 (1 + inputMaximum I) ≤ inputBits I from le_max_right _ _)
  omega

theorem value_lt_two_pow_bits {n : ℕ} (I : Instance n) (i : Fin n) :
    I.values i < 2 ^ inputBits I := by
  have hle : I.values i ≤ inputMaximum I :=
    (Finset.le_sup (Finset.mem_univ i)).trans (le_max_right _ _)
  exact hle.trans_lt (inputMaximum_lt_two_pow_bits I)

theorem target_lt_two_pow_bits {n : ℕ} (I : Instance n) :
    I.target < 2 ^ inputBits I :=
  (le_max_left _ _).trans_lt (inputMaximum_lt_two_pow_bits I)

theorem weight_natAbs_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → ℤ) (S : Finset ι) {M : ℕ} (hM : ∀ i, (a i).natAbs ≤ M) :
    (weight a S).natAbs ≤ Fintype.card ι * M := by
  apply (Int.natAbs_sum_le Finset.univ (fun i => if i ∈ S then a i else 0)).trans
  calc
    ∑ i, (if i ∈ S then a i else 0).natAbs ≤ ∑ _i : ι, M := by
      apply Finset.sum_le_sum
      intro i _
      by_cases hi : i ∈ S <;> simp [hi, hM i]
    _ = Fintype.card ι * M := by simp

theorem flip_natAbs {ι : Type*} (a : ι → ℤ) [DecidableEq ι] (F : Finset ι) (i : ι) :
    (flip a F i).natAbs = (a i).natAbs := by
  by_cases hi : i ∈ F <;> simp [flip, hi]

/-- The list retains repeated index occurrences in a raw tuple. -/
def occurrenceWeight {ι : Type*} (a : ι → ℤ) (xs : List ι) : ℤ :=
  (xs.map a).sum

theorem occurrenceWeight_natAbs_le {ι : Type*} (a : ι → ℤ)
    {M : ℕ} (hM : ∀ i, (a i).natAbs ≤ M) (xs : List ι) :
    (occurrenceWeight a xs).natAbs ≤ xs.length * M := by
  induction xs with
  | nil => simp [occurrenceWeight]
  | cons i xs ih =>
    have htriangle := Int.natAbs_add_le (a i) (occurrenceWeight a xs)
    simp only [occurrenceWeight, List.map_cons, List.sum_cons] at ih htriangle ⊢
    simp only [List.length_cons]
    nlinarith [hM i]

theorem signed_weight_natAbs_le {n : ℕ} (I : Instance n) (F S : Finset (Fin n)) :
    (weight (flip (fun i => (I.values i : ℤ)) F) S).natAbs ≤ n * 2 ^ inputBits I := by
  simpa only [Fintype.card_fin] using weight_natAbs_le
    (flip (fun i => (I.values i : ℤ)) F) S (M := 2 ^ inputBits I)
    (fun i => by simpa only [flip_natAbs, Int.natAbs_natCast] using
      (value_lt_two_pow_bits I i).le)

theorem signed_target_natAbs_le {n : ℕ} (I : Instance n) (F : Finset (Fin n)) :
    ((I.target : ℤ) - weight (fun i => (I.values i : ℤ)) F).natAbs ≤
      (n + 1) * 2 ^ inputBits I := by
  have hweight := weight_natAbs_le (fun i => (I.values i : ℤ)) F
    (M := 2 ^ inputBits I) (fun i => by simpa only [Int.natAbs_natCast] using
      (value_lt_two_pow_bits I i).le)
  have ht := (target_lt_two_pow_bits I).le
  have htriangle := Int.natAbs_sub_le (I.target : ℤ)
    (weight (fun i => (I.values i : ℤ)) F)
  simp only [Int.natAbs_natCast, Fintype.card_fin] at hweight htriangle
  nlinarith

theorem raw_signed_weight_natAbs_le {n : ℕ} (I : Instance n)
    (F : Finset (Fin n)) (xs : List (Fin n)) (hlen : xs.length ≤ 2 * n) :
    (occurrenceWeight (flip (fun i => (I.values i : ℤ)) F) xs).natAbs ≤
      2 * n * 2 ^ inputBits I := by
  apply (occurrenceWeight_natAbs_le (flip (fun i => (I.values i : ℤ)) F)
    (M := 2 ^ inputBits I) (fun i => by
      simpa only [flip_natAbs, Int.natAbs_natCast] using
        (value_lt_two_pow_bits I i).le) xs).trans
  exact Nat.mul_le_mul_right _ hlen

theorem relevant_magnitude_lt {n b d : ℕ} (hd : d ≤ (4 * n + 2) * 2 ^ b) :
    d < 2 ^ (2 * (n + b + 2)) := by
  have hn : n < 2 ^ n := Nat.lt_two_pow_self
  have hpowpos : 0 < 2 ^ n := pow_pos (by decide) _
  have hcoef : 4 * n + 2 ≤ 2 ^ (n + 3) := by
    rw [pow_add]
    norm_num
    omega
  calc
    d ≤ (4 * n + 2) * 2 ^ b := hd
    _ ≤ 2 ^ (n + 3) * 2 ^ b := Nat.mul_le_mul_right _ hcoef
    _ = 2 ^ (n + b + 3) := by rw [← pow_add]; congr 1; omega
    _ < 2 ^ (2 * (n + b + 2)) :=
      Nat.pow_lt_pow_right (by decide) (by omega)

/-- Every hash difference between valid or raw signed quantities of the
stated size meets the concrete prime-hashing bit hypothesis. -/
theorem relevant_difference_bits {n : ℕ} (I : Instance n) {x y : ℤ}
    (hx : x.natAbs ≤ (2 * n + 1) * 2 ^ inputBits I)
    (hy : y.natAbs ≤ (2 * n + 1) * 2 ^ inputBits I) :
    (x - y).natAbs < 2 ^ (2 * inputScale I) := by
  apply relevant_magnitude_lt
  have h := Int.natAbs_sub_le x y
  nlinarith

end LowSpaceSubsetSum

end OAI
