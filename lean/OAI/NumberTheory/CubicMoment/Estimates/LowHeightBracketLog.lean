import OAI.NumberTheory.CubicMoment.Estimates.LowHeightLogScale

namespace OAI

/-! The explicit low-height bracket, independently of any coefficients. -/
noncomputable section
namespace CubicFirstMoment

theorem low_height_bracket_log_saving (k : ℕ) :
    ∃ (K : ℝ) (Ct : ℕ), 0 < K ∧ ∀ N B T : ℝ,
      65536 ≤ N → 1 ≤ B → B ≤ N^2 → (1+Real.log N)^Ct ≤ T →
      N*((1+N/T)*(5832*(1+Real.log N)^(4*(k+2)))+
        ((largeCoreDyadicIndices (5832*(1+Real.log N)^(4*(k+2))) B).card:ℝ)*
          (N*((5832*(1+Real.log N)^(4*(k+2)))/5832)^(-(1/4:ℝ))+
            N^(1-1/20000:ℝ))) ≤ K*N^2/(1+Real.log N)^k := by
  obtain ⟨CI,hCI,hcount⟩ := core_dyadic_index_log_count
  obtain ⟨H₁,hH₁,hlog₁⟩ := log_power_normalization_bound (4*(k+2)+k)
    (by norm_num : (0:ℝ) < 1)
  obtain ⟨H₂,hH₂,hlog₂⟩ := log_power_normalization_bound (k+2)
    (by norm_num : (0:ℝ) < 1/20000)
  let Q := 5832*(H₁+1)+CI*(1+H₂)
  refine ⟨Q,4*(k+2)+k,by dsimp [Q]; positivity,?_⟩
  intro N B T hN hB hBN hT
  let L := 1+Real.log N
  let V := 5832*L^(4*(k+2))
  let I := (largeCoreDyadicIndices V B).card
  have hN1 : 1 ≤ N := by linarith
  have hNp : 0 < N := by linarith
  have hL1 : 1 ≤ L := by dsimp [L]; linarith [Real.log_nonneg hN1]
  have hLp : 0 < L := zero_lt_one.trans_le hL1
  have hI : (I:ℝ) ≤ CI*L^2 := hcount V B N hB hN1 hBN
  have hs := low_height_small_core_log_scale hNp hL1 k 0
    (by simpa only [Nat.add_zero] using hT) (by simpa only [Nat.add_zero] using hlog₁ N hN1)
  have hsmall : N*((1+N/T)*V) ≤ 5832*(H₁+1)*N^2/L^k := by
    simpa only [pow_zero,mul_one,mul_assoc] using hs
  have hv : (V/5832)^(-(1/4:ℝ)) = 1/L^(k+2) := logarithmic_core_cutoff hLp k
  have hmid : N*(I:ℝ)*(N*(V/5832)^(-(1/4:ℝ))) ≤ CI*N^2/L^k := by
    rw [hv]
    calc
      _ ≤ N*(CI*L^2)*(N*(1/L^(k+2))) := by gcongr
      _ = _ := by rw [pow_add]; field_simp
  have hnlog : N^(2-1/20000:ℝ)*L^2 ≤ H₂*N^2/L^k := by
    simpa only [Real.rpow_two] using
      rpow_log_saving hNp hLp k 2 (p := 2) (s := 1/20000) (hlog₂ N hN1)
  have hn : N*N^(1-1/20000:ℝ) = N^(2-1/20000:ℝ) := by
    nth_rw 1 [←Real.rpow_one N]
    rw [←Real.rpow_add hNp]
    congr 1
    norm_num
  have hlarge : N*(I:ℝ)*N^(1-1/20000:ℝ) ≤ (CI*H₂)*N^2/L^k := by
    calc
      _ ≤ N*(CI*L^2)*N^(1-1/20000:ℝ) := by gcongr
      _ = CI*(N^(2-1/20000:ℝ)*L^2) := by rw [←hn]; ring
      _ ≤ CI*(H₂*N^2/L^k) := mul_le_mul_of_nonneg_left hnlog hCI.le
      _ = _ := by ring
  have hh := add_le_add hsmall (add_le_add hmid hlarge)
  dsimp [Q]
  convert hh using 1 <;> ring

end CubicFirstMoment

end

end OAI
