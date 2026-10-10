import OAI.NumberTheory.Ostmann.QuadraticCenter.DistinctCoefficientError

namespace OAI

namespace Ostmann.QuadraticCenter
open scoped BigOperators

theorem paired_monomial_le {a S : ℝ} (ha : 0 ≤ a) (hS : 0 ≤ S)
    {j k : ℕ} (hj : 1 ≤ j) (hjk : 2 * j ≤ k) :
    a ^ j * S ^ (k - 2 * j) ≤ a * (S + Real.sqrt a) ^ (k - 2) := by
  have hsplit : a ^ j * S ^ (k - 2 * j) =
      a * ((Real.sqrt a) ^ (2 * (j - 1)) * S ^ (k - 2 * j)) := by
    rw [pow_mul, Real.sq_sqrt ha]
    rw [← mul_assoc, ← pow_succ', Nat.sub_add_cancel hj]
  rw [hsplit]
  apply mul_le_mul_of_nonneg_left _ ha
  calc
    (Real.sqrt a) ^ (2 * (j - 1)) * S ^ (k - 2 * j) ≤
        (S + Real.sqrt a) ^ (2 * (j - 1)) * (S + Real.sqrt a) ^ (k - 2 * j) := by
      apply mul_le_mul
      · exact pow_le_pow_left₀ (Real.sqrt_nonneg _) (by linarith) _
      · exact pow_le_pow_left₀ hS (by linarith [Real.sqrt_nonneg a]) _
      · exact pow_nonneg hS _
      · exact pow_nonneg (add_nonneg hS (Real.sqrt_nonneg _)) _
    _ = (S + Real.sqrt a) ^ (k - 2) := by
      rw [← pow_add]
      congr 1
      omega

theorem paired_monomial_tail_le {a S : ℝ} (ha : 0 ≤ a) (hS : 0 ≤ S) (m k : ℕ) :
    (∑ j ∈ (Finset.range (m + 1)).erase 0,
      if 2 * j ≤ k then a ^ j * S ^ (k - 2 * j) else 0) ≤
      (k : ℝ) * a * (S + Real.sqrt a) ^ (k - 2) := by
  classical
  let T := ((Finset.range (m + 1)).erase 0).filter (fun j => 2 * j ≤ k)
  have hsub : T ⊆ Finset.Icc 1 k := by
    intro j hj
    obtain ⟨hjer, hjk⟩ := Finset.mem_filter.mp hj
    have hj0 := (Finset.mem_erase.mp hjer).1
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  have hcard : T.card ≤ k := by
    have hc := Finset.card_le_card hsub
    simpa only [Nat.card_Icc, Nat.add_sub_cancel] using hc
  have hnonneg : 0 ≤ a * (S + Real.sqrt a) ^ (k - 2) := by positivity
  rw [← Finset.sum_filter]
  change (∑ j ∈ T, a ^ j * S ^ (k - 2 * j)) ≤ _
  calc
    (∑ j ∈ T, a ^ j * S ^ (k - 2 * j)) ≤
        ∑ _j ∈ T, a * (S + Real.sqrt a) ^ (k - 2) := by
      apply Finset.sum_le_sum
      intro j hj
      obtain ⟨hjer, hjk⟩ := Finset.mem_filter.mp hj
      have hj0 := (Finset.mem_erase.mp hjer).1
      exact paired_monomial_le ha hS (by omega) hjk
    _ = (T.card : ℝ) * (a * (S + Real.sqrt a) ^ (k - 2)) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (k : ℝ) * (a * (S + Real.sqrt a) ^ (k - 2)) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hnonneg
    _ = _ := by ring

theorem paired_series_adaptive_error_bound {S m J k : ℕ}
    (hS : S ≤ J) (hm : m ≤ J) (hk : 2 ≤ k) :
    |(k.factorial : ℝ) *
        (∑ j ∈ Finset.range (m + 1),
          if 2 * j ≤ k then (-1 : ℝ) ^ j * (m.choose j : ℝ) * (S.choose (k - 2 * j) : ℝ)
          else 0) - (S : ℝ) ^ k| ≤
      ((k : ℝ) + 1) * (k : ℝ) ^ 2 * J *
        ((S : ℝ) + k * Real.sqrt (J : ℝ)) ^ (k - 2) := by
  let a : ℝ := (k : ℝ) ^ 2 * J
  have ha : 0 ≤ a := by positivity
  have hs0 : (0 : ℝ) ≤ S := Nat.cast_nonneg _
  have hroot : Real.sqrt a = (k : ℝ) * Real.sqrt (J : ℝ) := by
    dsimp only [a]
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs,
      abs_of_nonneg (Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have hb := paired_series_error_bound hS hm hk
  have ht := paired_monomial_tail_le ha hs0 m k
  have hp : (S : ℝ) ^ (k - 2) ≤ ((S : ℝ) + Real.sqrt a) ^ (k - 2) :=
    pow_le_pow_left₀ hs0 (by linarith [Real.sqrt_nonneg a]) _
  have hp' := mul_le_mul_of_nonneg_left hp ha
  change _ ≤ ((k : ℝ) + 1) * (k : ℝ) ^ 2 * J *
    ((S : ℝ) + k * Real.sqrt (J : ℝ)) ^ (k - 2)
  rw [hroot] at ht hp'
  dsimp only [a] at ht hp'
  nlinarith

end Ostmann.QuadraticCenter

end OAI
