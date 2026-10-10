import OAI.NumberTheory.Ostmann.QuadraticSieveSquarefreeDyadic
import OAI.NumberTheory.Ostmann.QuadraticSieveWeightedSmoothing

namespace OAI

noncomputable section
namespace Ostmann.QuadraticSieve
open scoped BigOperators

theorem smoothing_column_cauchy {α : Type*} (s : Finset α) (f : α → ℂ) :
    ‖∑ j ∈ s,f j‖^2 ≤ (s.card:ℝ)*∑ j ∈ s,‖f j‖^2 := by
  apply (pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2).trans
  simpa only [one_pow,mul_one,Finset.sum_const, nsmul_eq_mul,mul_comm] using
    Finset.sum_mul_sq_le_sq_mul_sq s (fun j => ‖f j‖) (fun _ => (1:ℝ))

theorem smoothingWeight_sum_le (M K : ℕ) :
    (∑ m ∈ smoothingRows M K,|smoothingWeight M m|) ≤ 3*(M:ℝ) := by
  have hcard : (smoothingRows M K).card ≤ 3*M := by
    calc
      _ ≤ (Finset.Icc (1:ℤ) (3*(M:ℤ))).card := Finset.card_filter_le _ _
      _ = 3*M := by simp [Int.card_Icc, Int.toNat_mul]
  calc
    _ ≤ ∑ m ∈ smoothingRows M K,(1:ℝ) := by
      apply Finset.sum_le_sum
      intro m hm
      rw [abs_of_nonneg (smoothingWeight_nonneg M m)]
      exact sieveBump_le_one _
    _ = ((smoothingRows M K).card:ℝ) := by simp
    _ ≤ _ := by exact_mod_cast hcard

theorem smoothingNorm_le_trivial (M K : ℕ) (S : Finset ℕ) :
    smoothingNorm M K S ≤ 3*(M:ℝ)*S.card := by
  apply weightedNumeratorNorm_le_of_bound _ _ _ (by positivity)
  intro a
  exact (weightedNumeratorEnergy_le_card_mul _ _ _ a).trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (smoothingWeight_sum_le M K) (by positivity))
      (coefficientEnergy_nonneg S a))

theorem binarySquarefreeRows_zero {N : ℕ} (hN : 0 < N) :
    binarySquarefreeRows N 0 = {1} := by
  ext n
  simp only [binarySquarefreeRows,Finset.mem_filter,mem_oddSquarefreeUpTo,
    pow_zero,zero_add,pow_one,Finset.mem_singleton]
  constructor
  · omega
  · intro hn
    subst n
    exact ⟨⟨by omega,by omega,by decide,squarefree_one⟩,by omega,by omega⟩

theorem smoothingNorm_binary_zero_le {N : ℕ} (hN : 0 < N) (M K : ℕ) :
    smoothingNorm M K (binarySquarefreeRows N 0) ≤ 3*(M:ℝ) := by
  simpa only [binarySquarefreeRows_zero hN,Finset.card_singleton,Nat.cast_one,mul_one]
    using smoothingNorm_le_trivial M K (binarySquarefreeRows N 0)

theorem binarySquarefreeRows_positive_data {N j : ℕ} (hj : 0 < j) :
    2 ≤ 2^j ∧ ∀ n ∈ binarySquarefreeRows N j,
      1 < n ∧ 2^j ≤ n ∧ n < 2*2^j ∧ n ≤ N ∧ Odd n ∧ Squarefree n := by
  have htwo : 2 ≤ (2:ℕ)^j := by
    have hh := Nat.pow_le_pow_right (by omega : 0 < (2:ℕ)) (by omega : 1 ≤ j)
    simpa using hh
  refine ⟨htwo,?_⟩
  intro n hn
  obtain ⟨hn, hlo,hhi⟩ := Finset.mem_filter.mp hn
  obtain ⟨hnpos,hnN,hno,hns⟩ := mem_oddSquarefreeUpTo.mp hn
  rw [pow_succ,mul_comm] at hhi
  exact ⟨by omega,hlo,hhi,hnN,hno,hns⟩

end Ostmann.QuadraticSieve

end

end OAI
