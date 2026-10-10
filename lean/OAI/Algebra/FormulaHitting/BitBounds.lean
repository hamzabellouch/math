import OAI.Algebra.FormulaHitting.Generator
import Mathlib.Data.Nat.Log

namespace OAI

namespace NCHitting

theorem size_eq_clog (a : ℕ) : a.size = Nat.clog 2 (a+1) := by
  apply eq_of_forall_ge_iff
  intro k
  rw [Nat.size_le, Nat.clog_le_iff_le_pow (by decide)]
  omega

theorem entryBitBound_eq_clog (n d : ℕ) :
    entryBitBound n d = 3 + Nat.clog 2 (d+1) + d * Nat.clog 2 (n+1) := by
  simp only [entryBitBound, size_eq_clog]

theorem entryBitBound_in_parameters {n s : ℕ} (hn : 0 < n) (hs : 0 < s) :
    entryBitBound n (2*n*s^2) ≤
      6 + 3 * Nat.clog 2 (n*s+1) + 2*n*s^2 * Nat.clog 2 (n+1) := by
  have hnle : n ≤ n*s := Nat.le_mul_of_pos_right n hs
  have hsle : s ≤ n*s := Nat.le_mul_of_pos_left s hn
  have hnb := Nat.size_le_size hnle
  have hsb := Nat.size_le_size hsle
  have hpow := size_pow_le s 2
  have hmul₁ := size_mul_le 2 n
  have hmul₂ := size_mul_le (2*n) (s^2)
  have htwo : Nat.size 2 = 2 := by decide
  rw [htwo] at hmul₁
  rw [← size_eq_clog, ← size_eq_clog]
  unfold entryBitBound
  omega

end NCHitting

end OAI
