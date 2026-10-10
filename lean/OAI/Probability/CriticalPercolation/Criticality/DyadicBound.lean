import Mathlib

namespace OAI

section
section
noncomputable section
open scoped BigOperators

namespace CriticalPercolation
lemma sum_two_pow (N : ℕ) : ∑ k ∈ Finset.range N, (2:ℝ)^k = 2^N-1 := by
  induction N with
  | zero => simp
  | succ N ih => rw [Finset.sum_range_succ,ih,pow_succ]; ring

lemma sum_two_inv_pow (N : ℕ) : ∑ k ∈ Finset.range N, 1/(2:ℝ)^k = 2-2/2^N := by
  induction N with
  | zero => norm_num
  | succ N ih =>
    rw [Finset.sum_range_succ,ih,pow_succ]
    field_simp
    ring

lemma dyadic_sum_bound (N K : ℕ) :
    (∑ k ∈ Finset.range N,
      min ((2:ℝ)^(k+1)/4^K) ((2:ℝ)^(k+1)/4^k)) ≤ 6/2^K := by
  have hfour (k : ℕ) : (4:ℝ)^k = (2^k)^2 := by
    rw [← pow_mul,mul_comm k 2,pow_mul]
    norm_num
  have hnonneg (k : ℕ) : 0 ≤ min ((2:ℝ)^(k+1)/4^K) ((2:ℝ)^(k+1)/4^k) := by positivity
  calc
    _ ≤ ∑ k ∈ Finset.range (K+N),
        min ((2:ℝ)^(k+1)/4^K) ((2:ℝ)^(k+1)/4^k) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
      intro k _ _
      exact hnonneg k
    _ = (∑ k ∈ Finset.range K,
        min ((2:ℝ)^(k+1)/4^K) ((2:ℝ)^(k+1)/4^k)) +
        ∑ k ∈ Finset.range N,
        min ((2:ℝ)^(K+k+1)/4^K) ((2:ℝ)^(K+k+1)/4^(K+k)) :=
      Finset.sum_range_add _ _ _
    _ ≤ (∑ k ∈ Finset.range K, (2:ℝ)^(k+1)/4^K) +
        ∑ k ∈ Finset.range N, (2:ℝ)^(K+k+1)/4^(K+k) := by
      apply add_le_add
      · exact Finset.sum_le_sum (fun k _ => min_le_left _ _)
      · exact Finset.sum_le_sum (fun k _ => min_le_right _ _)
    _ ≤ 6/2^K := by
      have h1 : (∑ k ∈ Finset.range K, (2:ℝ)^(k+1)/4^K) =
          2*(2^K-1)/4^K := by
        simp only [pow_succ,mul_div_assoc]
        rw [← Finset.sum_mul,sum_two_pow]
        ring
      have h2 : (∑ k ∈ Finset.range N, (2:ℝ)^(K+k+1)/4^(K+k)) =
          2/2^K * (2-2/2^N) := by
        have he (k : ℕ) : (2:ℝ)^(K+k+1)/4^(K+k) = (2/2^K)*(1/2^k) := by
          rw [hfour,pow_succ,pow_add]
          field_simp
        simp_rw [he]
        rw [← Finset.mul_sum,sum_two_inv_pow]
      rw [h1,h2,hfour]
      have hpowK : (0:ℝ)<2^K := by positivity
      have hpowN : (0:ℝ)<2^N := by positivity
      have h1' : 2*((2:ℝ)^K-1)/((2:ℝ)^K)^2 ≤ 2/2^K := by
        apply (div_le_iff₀ (sq_pos_of_pos hpowK)).mpr
        field_simp
        nlinarith
      have h2' : (2/(2:ℝ)^K) * (2-2/2^N) ≤ 4/2^K := by
        calc _ ≤ (2/(2:ℝ)^K)*2 := mul_le_mul_of_nonneg_left (by have := (div_nonneg (by norm_num : (0:ℝ)≤2) hpowN.le); linarith) (by positivity)
             _ = _ := by ring
      calc _ ≤ 2/(2:ℝ)^K+4/2^K := add_le_add h1' h2'
           _ = _ := by ring

end CriticalPercolation
end
end
end

end OAI
