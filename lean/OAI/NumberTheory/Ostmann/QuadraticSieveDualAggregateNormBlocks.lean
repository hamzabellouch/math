import OAI.NumberTheory.Ostmann.QuadraticSieveDualAggregateNorm

namespace OAI

namespace Ostmann.QuadraticSieve

theorem binary_base_le_cutoff {K j : ℕ} (hK : 0 < K)
    (hj : j ∈ Finset.range (Nat.log 2 K+1)) : 2^j ≤ K := by
  have hlog : j ≤ Nat.log 2 K := by have h := Finset.mem_range.mp hj; omega
  exact (Nat.pow_le_pow_right (by decide : 0 < 2) hlog).trans (Nat.pow_log_le_self 2 hK.ne')

theorem binarySquarefreeRows_subset_upper (K j : ℕ) :
    binarySquarefreeRows K j ⊆ oddSquarefreeUpTo (2*2^j) := by
  intro v hv
  obtain ⟨hv',hlo,hhi⟩ := Finset.mem_filter.mp hv
  obtain ⟨hp,hK,ho,hs⟩ := mem_oddSquarefreeUpTo.mp hv'
  apply mem_oddSquarefreeUpTo.mpr
  exact ⟨hp,by simpa only [pow_succ,mul_comm] using hhi.le,ho,hs⟩

theorem exponentBound_binary_smaller_norm {ξ : ℝ}
    (hξ : ExponentBound (fun M N => quadraticNorm (oddSquarefreeUpTo M) (oddSquarefreeUpTo N)) ξ)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (K N j q : ℕ), 0 < K → 0 < N →
      j ∈ Finset.range (Nat.log 2 K+1) → 0 < q →
      quadraticNorm (binarySquarefreeRows K j) (oddSquarefreeUpTo (N/q)) ≤
        C * (((2*K : ℕ) : ℝ)*N)^δ * (((2*2^j : ℕ) : ℝ)^ξ+(N : ℝ)/q) := by
  obtain ⟨C,hC,hbound⟩ := exponentBound_smaller_norm hξ δ hδ
  refine ⟨C,hC,?_⟩
  intro K N j q hK hN hj hq
  apply (hbound (2*2^j) N q (binarySquarefreeRows K j) (by positivity) hN hq
    (binarySquarefreeRows_subset_upper K j)).trans
  have hb : ((2*2^j : ℕ) : ℝ) ≤ (2*K : ℕ) := by
    exact_mod_cast Nat.mul_le_mul_left 2 (binary_base_le_cutoff hK hj)
  gcongr

theorem binary_recursion_term_le {M B K ξ : ℝ} (hM : 0 < M) (hB : 0 < B)
    (hBK : B ≤ K) (hξ : 1 < ξ) (hξ2 : ξ ≤ 2) :
    M+Real.sqrt (M/B)*(2*B)^ξ ≤ 4*(M+Real.sqrt M*K^(ξ-1/2)) := by
  have hK : 0 < K := hB.trans_le hBK
  have hp : 0 ≤ ξ-1/2 := by linarith
  have htwo : (2 : ℝ)^ξ ≤ 4 := by
    have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hξ2
    norm_num [Real.rpow_two] at h ⊢
    exact h
  have hroot : Real.sqrt (M/B)*B^ξ = Real.sqrt M*B^(ξ-1/2) := by
    simp only [Real.sqrt_div hM.le,Real.sqrt_eq_rpow,Real.rpow_sub hB]
    ring
  have hterm : Real.sqrt (M/B)*(2*B)^ξ ≤ 4*Real.sqrt M*K^(ξ-1/2) := by
    calc
      _ = (2 : ℝ)^ξ*(Real.sqrt (M/B)*B^ξ) := by
        rw [Real.mul_rpow (by norm_num) hB.le]
        ring
      _ = (2 : ℝ)^ξ*(Real.sqrt M*B^(ξ-1/2)) := by rw [hroot]
      _ ≤ 4*(Real.sqrt M*K^(ξ-1/2)) := by gcongr
      _ = _ := by ring
  nlinarith

end Ostmann.QuadraticSieve

end OAI
