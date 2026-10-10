import OAI.NumberTheory.Ostmann.QuadraticSieveDualAggregateNorm
import OAI.NumberTheory.Ostmann.QuadraticSieveSquarefreeDyadic

namespace OAI

noncomputable section
namespace Ostmann.QuadraticSieve

theorem complement_binary_base_le {K j : ℕ} (hK : 0 < K)
    (hj : j ∈ Finset.range (Nat.log 2 K+1)) : 2^j ≤ K := by
  have hj' : j ≤ Nat.log 2 K := by have := Finset.mem_range.mp hj; omega
  exact (Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) hj').trans (Nat.pow_log_le_self 2 hK.ne')

theorem binarySquarefreeRows_subset_prefix (K j : ℕ) :
    binarySquarefreeRows K j ⊆ oddSquarefreeUpTo (2*2^j) := by
  intro v hv
  obtain ⟨hv',hlo,hhi⟩ := Finset.mem_filter.mp hv
  obtain ⟨hpos,hK,ho,hsq⟩ := mem_oddSquarefreeUpTo.mp hv'
  apply mem_oddSquarefreeUpTo.mpr
  refine ⟨hpos,?_,ho,hsq⟩
  rw [pow_succ,mul_comm] at hhi
  exact hhi.le

theorem complement_binary_smaller_norm {ξ : ℝ}
    (hξ : ExponentBound (fun M N => quadraticNorm (oddSquarefreeUpTo M) (oddSquarefreeUpTo N)) ξ)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ K N j q : ℕ, 0 < K → 0 < N → 0 < q →
      j ∈ Finset.range (Nat.log 2 K+1) →
      quadraticNorm (binarySquarefreeRows K j) (oddSquarefreeUpTo (N/q)) ≤
        C*(2*(K:ℝ)*N)^δ*(((2*2^j:ℕ):ℝ)^ξ+(N:ℝ)/q) := by
  obtain ⟨C,hC,hbound⟩ := exponentBound_smaller_norm hξ δ hδ
  refine ⟨C,hC,?_⟩
  intro K N j q hK hN hq hj
  have hb := hbound (2*2^j) N q (binarySquarefreeRows K j) (by positivity) hN hq
    (binarySquarefreeRows_subset_prefix K j)
  refine hb.trans ?_
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  apply mul_le_mul_of_nonneg_left _ hC.le
  apply Real.rpow_le_rpow (by positivity) _ hδ.le
  have he : (((2*2^j:ℕ):ℝ)) ≤ 2*(K:ℝ) := by
    exact_mod_cast Nat.mul_le_mul_left 2 (complement_binary_base_le hK hj)
  exact mul_le_mul_of_nonneg_right he (Nat.cast_nonneg N)

theorem complement_binary_main_scale {M B K ξ : ℝ}
    (hM : 0 < M) (hB : 0 < B) (hBK : B ≤ K) (hξ1 : 1 ≤ ξ) (hξ2 : ξ ≤ 2) :
    Real.sqrt (M/B)*(2*B)^ξ ≤ 4*Real.sqrt M*K^(ξ-1/2) := by
  have htwo : (2:ℝ)^ξ ≤ 4 := by
    have hh := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤2) hξ2
    norm_num only [Real.rpow_two, Nat.reducePow] at hh
    exact hh
  have hpow : (2*B)^ξ ≤ 4*B^ξ := by
    rw [Real.mul_rpow (by norm_num : (0:ℝ)≤2) hB.le]
    exact mul_le_mul_of_nonneg_right htwo (Real.rpow_nonneg hB.le _)
  have hdiv : B^ξ/Real.sqrt B = B^(ξ-1/2) := by
    rw [Real.sqrt_eq_rpow,← Real.rpow_sub hB]
  calc
    Real.sqrt (M/B)*(2*B)^ξ ≤ Real.sqrt (M/B)*(4*B^ξ) :=
      mul_le_mul_of_nonneg_left hpow (Real.sqrt_nonneg _)
    _ = 4*Real.sqrt M*(B^ξ/Real.sqrt B) := by rw [Real.sqrt_div hM.le]; ring
    _ = 4*Real.sqrt M*B^(ξ-1/2) := by rw [hdiv]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow hB.le hBK (by linarith)) (by positivity)

end Ostmann.QuadraticSieve

end

end OAI
