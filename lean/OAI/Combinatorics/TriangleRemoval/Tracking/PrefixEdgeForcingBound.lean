import Mathlib
import OAI.Combinatorics.TriangleRemoval.Tracking.PrefixTriangleRadius

namespace OAI

section
noncomputable section
open scoped BigOperators
open Filter Classical

namespace SharpTerminalLeave

noncomputable def prefixEdgeForcingBound (n : ℕ) : ℝ :=
  4/(n : ℝ)+codegreeNoiseRadius n+16*prefixTriangleRadius n*Real.log n+
    4/prefixD n+24*Real.log n/(n : ℝ)

lemma prefix_edge_forcing_power : ∀ᶠ n : ℕ in atTop,
    0 ≤ prefixEdgeForcingBound n ∧
    prefixEdgeForcingBound n ≤ 49*(1+Real.log (n : ℝ))*prefixTriangleRadius n := by
  filter_upwards [prefixD_eventual_envelope,eventually_ge_atTop (1 : ℕ)] with n hD hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := lt_of_lt_of_le zero_lt_one hn1
  have ht : 0 ≤ prefixTriangleRadius n := Real.rpow_nonneg hn0.le _
  have hl := Real.log_nonneg hn1
  have hD0 := lt_of_lt_of_le (Real.rpow_pos_of_pos hn0 _) hD.1
  have hi : 1/(n : ℝ) ≤ prefixTriangleRadius n := by
    simpa only [Real.rpow_neg_one,one_div,prefixTriangleRadius] using
      (Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num : (-1 : ℝ) ≤ -3/80000))
  have hno0 : 0 ≤ codegreeNoiseRadius n := Real.rpow_nonneg hn0.le _
  have hno : codegreeNoiseRadius n ≤ prefixTriangleRadius n :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num)
  have hdi : 1/prefixD n ≤ prefixTriangleRadius n := by
    apply (div_le_div_of_nonneg_left zero_le_one (Real.rpow_pos_of_pos hn0 _) hD.1).trans
    rw [one_div,← Real.rpow_neg hn0.le]
    exact Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num)
  have hg := mul_le_mul_of_nonneg_left hi (show 0 ≤ 24*Real.log (n : ℝ) by positivity)
  constructor
  · unfold prefixEdgeForcingBound
    positivity
  · unfold prefixEdgeForcingBound
    simp only [div_eq_mul_inv,one_mul] at hi hdi hg ⊢
    nlinarith only [hi,hno,hdi,hg,ht,mul_nonneg ht hl]

lemma edge_stability_log_bounds {L S : ℝ} (hL : 0 ≤ L) (hS : 0 ≤ S) (hS' : S ≤ 4*L) :
    0 ≤ 1+2*S ∧ 1+2*S ≤ 8*(1+L) ∧
    (1+2*S)*S ≤ 32*(1+L)^2 ∧
    (1+2*S)*S*6 ≤ 192*(1+L)^2 := by
  have hp := mul_le_mul (show 1+2*S ≤ 8*(1+L) by linarith) hS'
    hS (show 0 ≤ 8*(1+L) by positivity)
  have hpoly : 8*(1+L)*(4*L) ≤ 32*(1+L)^2 := by nlinarith only [hL]
  refine ⟨by positivity,by linarith,hp.trans hpoly,?_⟩
  nlinarith only [hp,hpoly]

lemma edge_stability_gain_bound {K : ℕ} {L S F r : ℝ}
    (hL : 0 ≤ L) (hS : 0 ≤ S) (hS' : S ≤ 4*L) (hF : 0 ≤ F)
    (hr : 0 ≤ r) (hF' : F ≤ 49*(1+L)*r) :
    2*(∑ j ∈ Finset.range K, ((1+2*S)*S*6)^j)*(1+2*S)*F ≤
      (784*(K : ℝ)*192^K)*(1+L)^(2*K+2)*r := by
  obtain ⟨hB,hB',_,hA⟩ := edge_stability_log_bounds hL hS hS'
  have hbase : 1 ≤ 192*(1+L)^2 := by nlinarith only [hL,sq_nonneg L]
  have hsum : (∑ j ∈ Finset.range K, ((1+2*S)*S*6)^j) ≤
      (K : ℝ)*(192*(1+L)^2)^K := by
    calc
      _ ≤ ∑ _j ∈ Finset.range K, (192*(1+L)^2)^K := by
        apply Finset.sum_le_sum
        intro j hj
        exact (pow_le_pow_left₀ (by positivity) hA j).trans
          (pow_le_pow_right₀ hbase (Finset.mem_range.mp hj).le)
      _ = _ := by simp
  have hs0 : 0 ≤ ∑ j ∈ Finset.range K, ((1+2*S)*S*6)^j := by positivity
  calc
    _ ≤ 2*(∑ j ∈ Finset.range K, ((1+2*S)*S*6)^j)*(1+2*S)*(49*(1+L)*r) :=
      mul_le_mul le_rfl hF' hF (mul_nonneg (mul_nonneg (by norm_num) hs0) hB)
    _ ≤ 2*((K : ℝ)*(192*(1+L)^2)^K)*(8*(1+L))*(49*(1+L)*r) := by
      apply mul_le_mul_of_nonneg_right _ (mul_nonneg (by positivity) hr)
      gcongr
    _ = _ := by rw [mul_pow,← pow_mul,pow_add,pow_succ, pow_succ]; ring

theorem prefix_edge_stability_budget {γ : ℝ} (hγ : 0 < γ) :
    ∃ K : ℕ, 0 < K ∧ ∀ᶠ n : ℕ in atTop, ∀ S : ℝ,
      0 ≤ S → S ≤ 4*Real.log n →
      ((1+2*S)*S*(n : ℝ)^(-γ))^K*(n : ℝ)^2 ≤ 1/2 ∧
      2*(∑ j ∈ Finset.range K, ((1+2*S)*S*6)^j)*(1+2*S)*prefixEdgeForcingBound n ≤
        prefixEdgeRadius n/2 := by
  obtain ⟨K,hK⟩ := exists_nat_gt (3/γ)
  have hKγ : 3 < γ*(K : ℝ) := by
    have hh := (div_lt_iff₀ hγ).mp hK
    nlinarith only [hh]
  have hK0 : 0 < K := by
    have hkR : (0 : ℝ) < K := lt_trans (by positivity) hK
    exact_mod_cast hkR
  let C : ℝ := 784*(K : ℝ)*192^K
  have hC : 0 < C := by dsimp [C]; positivity
  have hremexp : 0 < γ*(K : ℝ)-2 := by linarith
  refine ⟨K,hK0,?_⟩
  filter_upwards [prefix_edge_forcing_power,
    prefixTemplateFactor_subpower (2*K : ℝ) hremexp
      (by positivity : (0 : ℝ) < 1/(2*32^K)),
    prefixTemplateFactor_subpower (2*K+2 : ℝ)
      (by norm_num : (0 : ℝ) < 1/80000) (by positivity : (0 : ℝ) < 1/(2*C)),
    eventually_ge_atTop (1 : ℕ)] with n hF hrem hgain hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := lt_of_lt_of_le zero_lt_one hn1
  have hl := Real.log_nonneg hn1
  have htr0 : 0 ≤ prefixTriangleRadius n := Real.rpow_nonneg hn0.le _
  have hrem' : (1+Real.log (n : ℝ))^(2*K) ≤
      1/(2*32^K)*(n : ℝ)^(γ*(K : ℝ)-2) := by
    convert hrem using 1
    simp only [prefixTemplateFactor]
    rw [← Real.rpow_natCast]
    congr 1
    push_cast
    ring
  have hgain' : (1+Real.log (n : ℝ))^(2*K+2) ≤
      1/(2*C)*(n : ℝ)^(1/80000 : ℝ) := by
    convert hgain using 1
    simp only [prefixTemplateFactor]
    rw [← Real.rpow_natCast]
    congr 1
    push_cast
    ring
  intro S hS hS'
  obtain ⟨hB,hB',hA,_⟩ := edge_stability_log_bounds hl hS hS'
  constructor
  · calc
      _ ≤ (32*(1+Real.log (n : ℝ))^2*(n : ℝ)^(-γ))^K*(n : ℝ)^2 := by gcongr
      _ = 32^K*(1+Real.log (n : ℝ))^(2*K)*(n : ℝ)^(-γ*(K : ℝ)+2) := by
        rw [mul_pow,mul_pow,← pow_mul]
        have he : ((n : ℝ)^(-γ))^K*(n : ℝ)^2 = (n : ℝ)^(-γ*(K : ℝ)+2) := by
          rw [← Real.rpow_natCast ((n : ℝ)^(-γ)) K,← Real.rpow_mul hn0.le,
            ← Real.rpow_natCast (n : ℝ) 2,← Real.rpow_add hn0]
          norm_num
        rw [mul_assoc (32^K*(1+Real.log (n : ℝ))^(2*K)),he]
      _ ≤ 32^K*(1/(2*32^K)*(n : ℝ)^(γ*(K : ℝ)-2))*(n : ℝ)^(-γ*(K : ℝ)+2) := by gcongr
      _ = 1/2 := by
        rw [mul_assoc, mul_assoc,← Real.rpow_add hn0]
        simp only [show γ*(K : ℝ)-2+(-γ*(K : ℝ)+2) = 0 by ring,Real.rpow_zero,mul_one]
        field_simp
  · have hb := edge_stability_gain_bound hl hS hS' hF.1
      htr0 hF.2 (K := K)
    apply hb.trans
    change C*(1+Real.log (n : ℝ))^(2*K+2)*prefixTriangleRadius n ≤ _
    calc
      _ ≤ C*(1/(2*C)*(n : ℝ)^(1/80000 : ℝ))*prefixTriangleRadius n := by gcongr
      _ = prefixEdgeRadius n/2 := by
        have he : (n : ℝ)^(1/80000 : ℝ)*prefixTriangleRadius n = prefixEdgeRadius n := by
          unfold prefixTriangleRadius prefixEdgeRadius
          rw [← Real.rpow_add hn0]
          norm_num
        calc
          _ = (C*(1/(2*C)))*((n : ℝ)^(1/80000 : ℝ)*prefixTriangleRadius n) := by ring
          _ = prefixEdgeRadius n/2 := by rw [he]; field_simp

end SharpTerminalLeave
end
end

end OAI
