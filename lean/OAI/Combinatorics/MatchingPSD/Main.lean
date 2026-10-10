import OAI.Combinatorics.MatchingPSD.NumericalBounds

namespace OAI

namespace PerfectMatchingPSD
open MatchingSmoothing MatchingInterpolation Matrix Filter Asymptotics
open scoped BigOperators MatrixOrder

lemma main_nat (p : ℕ) : ∃ n₀ : ℕ, 4 ≤ n₀ ∧
    ∀ n : ℕ, n₀ ≤ n → Even n → (n:ℝ)^p < (psdRank n:ℝ) := by
  classical
  obtain ⟨d,H,hd,D,hD,hdecode⟩ := conditional_cell_lower_bound (10*(p+1))
  obtain ⟨Te,hTe⟩ := eventually_atTop.mp (eventually_pow_lt_half_exp (6*p))
  let T := 2+H+1024*(d+1)+Fintype.card (SampleIndex d)+⌈8*(D+1)⌉₊+Te
  refine ⟨vertexSize d T+4, by omega, ?_⟩
  intro n hn hneven
  obtain ⟨t,ht,hleft,hright⟩ := bracket_vertexSize d T n (by omega)
  dsimp only [T] at ht
  have ht2 : 2 ≤ t := by omega
  have ht1 : 1 ≤ t := by omega
  have hHt : H ≤ t := by omega
  have hdt : 1024*(d+1) ≤ t := by omega
  have hTt : Fintype.card (SampleIndex d) ≤ t := by omega
  have hDt : 8*(D+1) ≤ (t:ℝ) :=
    (Nat.le_ceil (8*(D+1))).trans (by exact_mod_cast (show ⌈8*(D+1)⌉₊ ≤ t by omega))
  have htet : Te ≤ t := by omega
  have hn6 : n ≤ t^6 := hright.le.trans (vertexSize_succ_le_pow6 d t ht1 hdt)
  have hl : 1 ≤ t^4 := one_le_pow₀ ht1
  have hs : 1 ≤ blockSize d t := hl.trans (blockSize_ge d t)
  have hH : H ≤ 3*blockSize d t+1 := by
    have hts : t ≤ blockSize d t := (Nat.le_pow (by decide : 0 < 4)).trans (blockSize_ge d t)
    omega
  by_contra hnot
  have hrn : (psdRank n:ℝ) ≤ (n:ℝ)^p := le_of_not_gt hnot
  obtain ⟨k,⟨e⟩⟩ := exists_padded_global_equiv hneven hleft
  obtain ⟨Q,B,hQ,hB,htrQ,htrB,hpair⟩ := global_factors_of_factorization
    hneven (by omega : 1 ≤ n) (hasFactorization_psdRank n) e (standardPairing (H := Fin k))
  have hsel : (t:ℝ)*(psdRank n)^4*(Fintype.card (SampleIndex d))*
      ((2*(3*(blockSize d t:ℝ)+1))^(2*(10*(p+1))))⁻¹ ≤
      (1/((psdRank n:ℝ)*((n:ℝ)+1)*(2*(t^4:ℕ))))^2 := by
    simpa only [Nat.cast_pow] using numerical_selection p d t (psdRank n) n
      (Fintype.card (SampleIndex d)) ht2 (psdRank_pos n) hn6 hTt hrn
  have hsmall : 16*(t:ℝ)^2*((t:ℝ)*D+1) ≤ 2*(t^4:ℕ) := by
    simpa only [Nat.cast_pow] using numerical_smallness D t ht1 hDt
  have hlower : (2:ℝ)^t/2 ≤ (psdRank n:ℝ) :=
    hdecode (blockSize d t) t (t^4) (psdRank n) hH hs ht1 (blockSize_grid d t) hl
      (psdRank_pos n) ((n:ℝ)+1) (by positivity) Q B hQ hB htrQ htrB hpair hsel hsmall
  have hn6r : (n:ℝ) ≤ (t:ℝ)^6 := by exact_mod_cast hn6
  have hpow : (n:ℝ)^p ≤ (t:ℝ)^(6*p) := by
    simpa only [pow_mul] using pow_le_pow_left₀ (Nat.cast_nonneg n) hn6r p
  exact (not_lt_of_ge hlower) ((hrn.trans hpow).trans_lt (hTe t htet))

theorem main : MainClaim := by
  intro C _hC
  obtain ⟨n₀,hn₀,hmain⟩ := main_nat ⌈C⌉₊
  refine ⟨n₀,hn₀,?_⟩
  intro n hn heven
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hpow := Real.rpow_le_rpow_of_exponent_le hn1 (Nat.le_ceil C)
  rw [Real.rpow_natCast] at hpow
  exact hpow.trans_lt (hmain n hn heven)

end PerfectMatchingPSD

end OAI
