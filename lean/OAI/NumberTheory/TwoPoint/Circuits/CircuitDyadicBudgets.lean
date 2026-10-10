import OAI.NumberTheory.TwoPoint.Circuits.CircuitBravermanApproximation
import OAI.NumberTheory.TwoPoint.Circuits.CircuitFourierDegree

namespace OAI

/-! Natural-number budgets for the fixed depth twenty-two application.
Using powers of two keeps the exponential error calculation elementary. -/

namespace TwoPointCorrelations

open scoped Classical

def bravermanSamples (j : ℕ) : ℕ := 40 * (j + 1)
def bravermanBase (j : ℕ) : ℕ := bravermanSamples j * (j + 3)
def bravermanNormExponent (j : ℕ) : ℕ :=
  (2 * j + 3) * (2 * bravermanBase j + 2) ^ 22
def bravermanErrorExponent (j : ℕ) : ℕ := 20 * (j + 3)
def bravermanSwitches (j : ℕ) : ℕ :=
  2 * bravermanNormExponent j + bravermanErrorExponent j + j + 10
def bravermanDegree (j : ℕ) : ℕ :=
  2 * (bravermanBase j ^ 22 + switchingDegree 89 (bravermanSwitches j))

lemma bravermanSamples_pos (j : ℕ) : 1 ≤ bravermanSamples j := by
  unfold bravermanSamples
  omega

lemma bravermanBase_pos (j : ℕ) : 1 ≤ bravermanBase j := by
  unfold bravermanBase
  have := bravermanSamples_pos j
  nlinarith

lemma bravermanSwitches_pos (j : ℕ) : 1 ≤ bravermanSwitches j := by
  unfold bravermanSwitches
  omega

lemma nat_log_le_of_dyadic {m j : ℕ} (hm : m ≤ 2 ^ j) : Nat.log 2 m ≤ j := by
  simpa only [Nat.log_pow (by norm_num : 1 < 2)] using Nat.log_mono_right (b := 2) hm

lemma braverman_error_size_budget {m j : ℕ} (hm : m ≤ 2 ^ j) :
    AC0Circuit.exceptionPolynomialBound m (bravermanSamples j) * m ≤
      2 ^ bravermanErrorExponent j := by
  have hj : j + 1 ≤ 2 ^ j := Nat.succ_le_of_lt j.lt_two_pow_self
  have hs : bravermanSamples j ≤ 2 ^ (j + 6) := by
    unfold bravermanSamples
    calc
      40 * (j + 1) ≤ 64 * 2 ^ j := Nat.mul_le_mul (by norm_num) hj
      _ = 2 ^ (j + 6) := by rw [pow_add]; ring
  have hl : Nat.log 2 m + 3 ≤ 2 ^ (j + 2) := by
    have hh := nat_log_le_of_dyadic hm
    rw [pow_add]
    norm_num
    omega
  have hp : 1 ≤ 2 ^ j := Nat.one_le_pow j 2 (by omega)
  have hbracket : 1 + m * (1 + m) ≤ 2 ^ (2 * j + 2) := by
    calc
      1 + m * (1 + m) ≤ 4 * (2 ^ j) ^ 2 := by nlinarith [hm]
      _ = 2 ^ (2 * j + 2) := by
        rw [pow_add, show 2 * j = j * 2 by omega, pow_mul]
        ring
  have hadd : 5 + m ≤ 2 ^ (4 * j + 10) := by
    calc
      5 + m ≤ 8 * 2 ^ j := by omega
      _ = 2 ^ (j + 3) := by rw [pow_add]; ring
      _ ≤ _ := Nat.pow_le_pow_right (by omega) (by omega)
  have hprod : bravermanSamples j * (Nat.log 2 m + 3) * (1 + m * (1 + m)) ≤
      2 ^ (4 * j + 10) := by
    calc
      _ ≤ 2 ^ (j + 6) * 2 ^ (j + 2) * 2 ^ (2 * j + 2) :=
        Nat.mul_le_mul (Nat.mul_le_mul hs hl) hbracket
      _ = _ := by simp only [← pow_add]; congr 1; omega
  calc
    _ ≤ (2 ^ (4 * j + 10) + 2 ^ (4 * j + 10)) * 2 ^ j :=
      Nat.mul_le_mul (Nat.add_le_add hadd hprod) hm
    _ = 2 ^ (5 * j + 11) := by simp only [pow_succ]; ring
    _ ≤ _ := Nat.pow_le_pow_right (by omega) (by unfold bravermanErrorExponent; omega)

end TwoPointCorrelations

end OAI
