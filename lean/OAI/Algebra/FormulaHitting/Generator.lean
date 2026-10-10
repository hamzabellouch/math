import OAI.Algebra.FormulaHitting.Model
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Size
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

namespace OAI

namespace NCHitting

theorem dimension_pos {n s : ℕ} (hn : 0 < n) (hs : 0 < s) :
    0 < dimension n s := by
  unfold dimension
  split_ifs <;> positivity

theorem dimension_le {n s : ℕ} (hn : 0 < n) (hs : 0 < s) :
    dimension n s ≤ 2 * n * s ^ 2 := by
  unfold dimension
  split_ifs with h
  · rcases h with ⟨rfl, rfl⟩
    norm_num
  · exact le_rfl

theorem dimension_eq {n s : ℕ} (hns : 2 ≤ n * s) :
    dimension n s = 2 * n * s ^ 2 := by
  unfold dimension
  split_ifs with h
  · rcases h with ⟨rfl, rfl⟩
    norm_num at hns
  · rfl

@[simp] theorem dimension_one : dimension 1 1 = 1 := by decide

theorem generator_one (i : Fin 1) (r q : Fin (dimension 1 1)) :
    generator 1 1 i r q = 1 := by simp [generator]

theorem generator_entry {n s : ℕ} (hns : 2 ≤ n * s)
    (i : Fin n) (r q : Fin (dimension n s)) :
    generator n s i r q = matrixEntry (i.val + 1) r.val q.val := by
  have h : ¬(n = 1 ∧ s = 1) := by rintro ⟨rfl, rfl⟩; norm_num at hns
  simp [generator, h]

theorem matrixEntry_of_lt {i r q : ℕ} (h : q < r) :
    matrixEntry i r q = (-1 : ℚ) ^ (r - q - 1) / ((r : ℚ) * i ^ (r - q)) := by
  simp [matrixEntry, h]

theorem matrixEntry_of_le {i r q : ℕ} (h : r ≤ q) :
    matrixEntry i r q = 0 := by simp [matrixEntry, Nat.not_lt.mpr h]

def entryBitBound (n d : ℕ) : ℕ := 3 + d.size + d * n.size

theorem size_mul_le (a b : ℕ) : (a * b).size ≤ a.size + b.size := by
  apply Nat.size_le.mpr
  rw [pow_add]
  exact Nat.mul_lt_mul_of_lt_of_lt (Nat.lt_size_self a) (Nat.lt_size_self b)

theorem size_pow_le (a k : ℕ) : (a ^ k).size ≤ 1 + k * a.size := by
  induction k with
  | zero => simp
  | succ k ih =>
    calc
      (a ^ (k + 1)).size = (a ^ k * a).size := by rw [pow_succ]
      _ ≤ (a ^ k).size + a.size := size_mul_le _ _
      _ ≤ 1 + (k + 1) * a.size := by rw [Nat.add_mul]; omega

theorem denominator_pos {i r q : ℕ} (hi : 0 < i) (hq : q < r) :
    0 < r * i ^ (r - q) := Nat.mul_pos (by omega) (pow_pos hi _)

theorem denominator_size_le {n d i r q : ℕ}
    (hi : i ≤ n) (hr : r < d) :
    (r * i ^ (r - q)).size ≤ entryBitBound n d := by
  have hs := Nat.size_le_size hi
  have ht := Nat.size_le_size (Nat.le_of_lt hr)
  have hk : r - q ≤ d := by omega
  calc
    (r * i ^ (r - q)).size ≤ r.size + (i ^ (r - q)).size := size_mul_le _ _
    _ ≤ r.size + (1 + (r - q) * i.size) := Nat.add_le_add_left (size_pow_le _ _) _
    _ ≤ entryBitBound n d := by
      have hm := Nat.mul_le_mul hk hs
      unfold entryBitBound
      omega

theorem size_le_self (a : ℕ) : a.size ≤ a := by
  apply Nat.size_le.mpr
  exact Nat.lt_two_pow_self

theorem entryBitBound_le (n d : ℕ) : entryBitBound n d ≤ 3 + d + d * n := by
  unfold entryBitBound
  exact Nat.add_le_add (Nat.add_le_add_left (size_le_self _) _) (Nat.mul_le_mul_left _ (size_le_self _))

end NCHitting

end OAI
