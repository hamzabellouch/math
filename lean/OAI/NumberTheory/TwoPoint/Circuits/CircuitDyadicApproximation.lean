import OAI.NumberTheory.TwoPoint.Circuits.CircuitDyadicBudgets

namespace OAI

/-! Specialize the proved approximation construction to dyadic size
budgets and circuit depth twenty-two. -/

namespace TwoPointCorrelations

open scoped Classical

lemma braverman_approx_degree_bound {m j d : ℕ} (hm : m ≤ 2 ^ j) (hd : d ≤ 22) :
    (bravermanSamples j * (Nat.log 2 m + 3)) ^ d ≤ bravermanBase j ^ 22 := by
  have hbase : bravermanSamples j * (Nat.log 2 m + 3) ≤ bravermanBase j :=
    Nat.mul_le_mul_left _ (Nat.add_le_add_right (nat_log_le_of_dyadic hm) 3)
  exact (Nat.pow_le_pow_left hbase _).trans
    (Nat.pow_le_pow_right (bravermanBase_pos j) hd)

lemma braverman_norm_power_bound {m j d : ℕ} (hm : m ≤ 2 ^ j) (hd : d ≤ 22) :
    (2 * (bravermanSamples j * (Nat.log 2 m + 3)) + 2) ^ d ≤
      (2 * bravermanBase j + 2) ^ 22 := by
  have hbase : bravermanSamples j * (Nat.log 2 m + 3) ≤ bravermanBase j :=
    Nat.mul_le_mul_left _ (Nat.add_le_add_right (nat_log_le_of_dyadic hm) 3)
  exact (Nat.pow_le_pow_left (Nat.add_le_add_right (Nat.mul_le_mul_left 2 hbase) 2) _).trans
    (Nat.pow_le_pow_right (by omega) hd)

lemma braverman_norm_base_bound {m j : ℕ} (hm : m ≤ 2 ^ j) :
    2 * ((m : ℝ) + 1) ^ 2 ≤ (2 : ℝ) ^ (2 * j + 3) := by
  have hmreal : (m : ℝ) ≤ (2 : ℝ) ^ j := by exact_mod_cast hm
  have htwo : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
  have hsum : (m : ℝ) + 1 ≤ 2 * (2 : ℝ) ^ j := by linarith only [hmreal, htwo]
  calc
    _ ≤ 2 * (2 * (2 : ℝ) ^ j) ^ 2 :=
      mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (add_nonneg (Nat.cast_nonneg m) zero_le_one) hsum 2) (by norm_num)
    _ = _ := by
      rw [pow_add, show 2 * j = j * 2 by omega, pow_mul]
      ring

theorem AC0Circuit.dyadic_approximation {n j : ℕ}
    (ν : FiniteLaw (BooleanCube n)) (c : AC0Circuit n)
    (hc : c.depth ≤ 22) (hm : c.size ≤ 2 ^ j) :
    ∃ (P : BooleanCube n → ℝ) (E : AC0Circuit n),
      WalshDegreeLE P (bravermanBase j ^ 22) ∧
      E.depth ≤ 89 ∧ E.size ≤ 2 ^ bravermanErrorExponent j ∧
      ν.probability (fun x => E.eval x = true) ≤
        (2 : ℝ) ^ j * (7 / 8 : ℝ) ^ bravermanSamples j ∧
      (∀ x, E.eval x ≠ true → P x = c.indicator x) ∧
      ∀ x, |P x| ≤ (2 : ℝ) ^ bravermanNormExponent j := by
  obtain ⟨P, E, hP, hd, hsize, hprob, he, hnorm⟩ :=
    c.polynomial_error_approximation ν (bravermanSamples j) (bravermanSamples_pos j)
  have hmreal : (c.size : ℝ) ≤ (2 : ℝ) ^ j := by exact_mod_cast hm
  have h89 : E.depth ≤ 89 := hd.trans (Nat.add_le_add_right (Nat.mul_le_mul_left 4 hc) 1)
  refine ⟨P, E, hP.mono (braverman_approx_degree_bound hm hc), h89,
    hsize.trans (braverman_error_size_budget hm), ?_, he, ?_⟩
  · exact hprob.trans (mul_le_mul_of_nonneg_right hmreal (by positivity))
  · intro x
    calc
      |P x| ≤ _ := hnorm x
      _ ≤ ((2 : ℝ) ^ (2 * j + 3)) ^
          ((2 * (bravermanSamples j * (Nat.log 2 c.size + 3)) + 2) ^ c.depth) :=
        pow_le_pow_left₀ (by positivity) (braverman_norm_base_bound hm) _
      _ ≤ ((2 : ℝ) ^ (2 * j + 3)) ^ ((2 * bravermanBase j + 2) ^ 22) :=
        pow_le_pow_right₀ (one_le_pow₀ (by norm_num)) (braverman_norm_power_bound hm hc)
      _ = _ := by rw [← pow_mul]; rfl

end TwoPointCorrelations

end OAI
