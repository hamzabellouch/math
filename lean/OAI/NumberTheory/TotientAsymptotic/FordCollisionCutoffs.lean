import OAI.NumberTheory.TotientAsymptotic.GoodTuples

namespace OAI

/-! The actual Ford scales satisfy the cutoff hypotheses used for good collisions. -/

noncomputable section
open scoped Topology
open Filter

namespace TotientAsymptotic

lemma ford_band_lower : ∀ᶠ x : ℝ in atTop, ∀ i < m x,
    (99/100 : ℝ)*lam*(m x-i : ℕ)/rho^(m x-i) ≤ fordBandScale x i := by
  filter_upwards [fordBandScale_uniform_comparison (ε := 1/100) (by norm_num),
    theta_eventually_mem] with x hx hs
  intro i hi
  have hp := bandScale_pos hi
  have hd := (lt_div_iff₀ hp).mp (show (99/100 : ℝ) < fordBandScale x i/bandScale x i by
    linarith [(abs_lt.mp (hx i hi)).1])
  have ha := mul_le_mul_of_nonneg_right (alpha_ge_lam hs.1)
    (div_nonneg (Nat.cast_nonneg (m x-i)) (pow_pos rho_pos (m x-i)).le)
  have he : lam*((m x-i : ℕ) : ℝ)/rho^(m x-i) ≤ bandScale x i := by
    simpa only [bandScale,div_eq_mul_inv,mul_assoc] using ha
  convert (mul_le_mul_of_nonneg_left he (by norm_num : (0 : ℝ) ≤ 99/100)).trans hd.le using 1
  ring

lemma next_band_below_ford_cutoff : ∀ᶠ x : ℝ in atTop, ∀ j < m x,
    (11/10 : ℝ)*bandScale x (j+1) < (7/10 : ℝ)*fordBandScale x j := by
  filter_upwards [fordBandScale_uniform_comparison (ε := 1/100) (by norm_num)] with x hx
  intro j hj
  have hp := bandScale_pos hj
  have hd := (lt_div_iff₀ hp).mp (show (99/100 : ℝ) < fordBandScale x j/bandScale x j by
    linarith [(abs_lt.mp (hx j hj)).1])
  have hn := bandScale_succ_le x j
  have hr := collision_rho_bounds.2
  have hρ := mul_lt_mul_of_pos_right hr hp
  nlinarith

theorem basic_residual_ford_smooth : ∀ᶠ x : ℝ in atTop, ∀ H j : ℕ,
    L x H < m x → j < L x H → ∀ η : RemainderDatum (L x H),
    IsBasicRemainder x H η →
    (largestPrimeFactor (suffixPreimage η j).totient : ℝ) <
      Real.exp (Real.exp ((7/10 : ℝ)*fordBandScale x j)) := by
  filter_upwards [next_band_below_ford_cutoff] with x hx
  intro H j hL hj η hη
  have hp := hη.2.1 (j+1) (Finset.mem_Icc.mpr ⟨by omega,by omega⟩)
  have hpos : (1 : ℝ) < remainderPrime η (j+1) := by exact_mod_cast hp.1.one_lt
  have hc : B (remainderPrime η (j+1)) < (7/10 : ℝ)*fordBandScale x j :=
    hp.2.2.trans_lt (hx j (hj.trans hL))
  have hprime : (remainderPrime η (j+1) : ℝ) <
      Real.exp (Real.exp ((7/10 : ℝ)*fordBandScale x j)) := by
    apply (Real.log_lt_iff_lt_exp (zero_lt_one.trans hpos)).mp
    exact (Real.log_lt_iff_lt_exp (Real.log_pos hpos)).mp hc
  exact lt_of_le_of_lt (by exact_mod_cast basic_suffix_totient_smooth hη hL hj) hprime

lemma ford_band_polynomial_lower (k : ℕ) : ∀ᶠ H : ℕ in atTop,
    ∀ᶠ x : ℝ in atTop, ∀ i : ℕ, i < m x → H ≤ m x-i →
    ((m x-i : ℕ) : ℝ)^k ≤ fordBandScale x i := by
  have hp : (0 : ℝ) < (99/100 : ℝ)*lam := mul_pos (by norm_num) lam_pos
  have ht := (tendsto_pow_const_mul_const_pow_of_lt_one k rho_pos.le rho_lt_one).eventually
    (eventually_lt_nhds hp)
  obtain ⟨H₀,hH₀⟩ := eventually_atTop.mp ht
  filter_upwards [eventually_ge_atTop H₀,eventually_ge_atTop 1] with H hH hH1
  filter_upwards [ford_band_lower] with x hx
  intro i hi hHi
  have hpow := hH₀ (m x-i) (hH.trans hHi)
  have hh : (1 : ℝ) ≤ (m x-i : ℕ) := by exact_mod_cast hH1.trans hHi
  have h0 : 0 ≤ ((m x-i : ℕ) : ℝ)^k := by positivity
  have ha : ((m x-i : ℕ) : ℝ)^k ≤
      (99/100 : ℝ)*lam/rho^(m x-i) := by
    apply (le_div_iff₀ (pow_pos rho_pos _)).mpr
    exact hpow.le
  have hc : (99/100 : ℝ)*lam/rho^(m x-i) ≤
      (99/100 : ℝ)*lam*(m x-i : ℕ)/rho^(m x-i) := by
    apply div_le_div_of_nonneg_right _ (pow_pos rho_pos _).le
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hh hp.le
  exact ha.trans (hc.trans (hx i hi))

lemma cube_root_le_scaled {h : ℕ} {b : ℝ} (hh : 1 ≤ h) (hb : (h : ℝ)^33 ≤ b) :
    b^(1/3 : ℝ) ≤ b/(h : ℝ)^21 := by
  have h1 : (1 : ℝ) ≤ h := by exact_mod_cast hh
  have h0 : (0 : ℝ) < h := lt_of_lt_of_le zero_lt_one h1
  have hb0 : 0 < b := (pow_pos h0 _).trans_le hb
  have hpow : (h : ℝ)^63 ≤ b^2 := by
    calc
      _ ≤ (h : ℝ)^66 := pow_le_pow_right₀ h1 (by omega)
      _ = ((h : ℝ)^33)^2 := by ring
      _ ≤ b^2 := pow_le_pow_left₀ (by positivity) hb _
  have hcube : b ≤ (b/(h : ℝ)^21)^3 := by
    rw [div_pow]
    apply (le_div_iff₀ (pow_pos (pow_pos h0 _) _)).mpr
    have hp := mul_le_mul_of_nonneg_left hpow hb0.le
    convert hp using 1 <;> ring
  apply (pow_le_pow_iff_left₀ (Real.rpow_nonneg hb0.le _) (by positivity) (by norm_num : 3 ≠ 0)).mp
  have he : (b^(1/3 : ℝ))^3=b := by
    rw [← Real.rpow_mul_natCast hb0.le]
    norm_num
  rw [he]
  exact hcube

lemma ford_collision_layer_ratio {x : ℝ} {i : ℕ} (hB : 1 < B x)
    (hi : i < m x) (hJ : 2*collisionCutoff (m x-i) < m x-i) :
    rho/(2*((m x-i : ℕ) : ℝ)^20) ≤
      fordBandScale x (collisionLastIndex x i)/fordBandScale x i ∧
    fordBandScale x (collisionLastIndex x i)/fordBandScale x i ≤
      1/((m x-i : ℕ) : ℝ)^18 := by
  have hh : 1 ≤ m x-i := Nat.sub_pos_of_lt hi
  have hk : collisionLastIndex x i < m x := by unfold collisionLastIndex; omega
  have hc : bandCenterRatio x ≠ 0 := by
    unfold bandCenterRatio
    exact div_ne_zero (Real.log_pos hB).ne' (mul_ne_zero lam_pos.ne'
      (Nat.cast_ne_zero.mpr (by omega)))
  have he : fordBandScale x (collisionLastIndex x i)/fordBandScale x i =
      bandScale x (collisionLastIndex x i)/bandScale x i := by
    rw [fordBandScale_eq_ratio_mul hB hk,fordBandScale_eq_ratio_mul hB hi]
    field_simp
  rw [he]
  have hdim : m x-collisionLastIndex x i = (m x-i)-collisionCutoff (m x-i) := by
    unfold collisionLastIndex
    omega
  have hr := collision_layer_ratio hh hJ.le (theta x)
  simpa only [bandScale,hdim,div_eq_mul_inv,mul_assoc] using hr

lemma scaled_cube_root_lt {h : ℕ} {b : ℝ} (hh : 10 ≤ h) (hb : (h : ℝ)^33 ≤ b) :
    b^(1/3 : ℝ) < (7/10 : ℝ)*(rho/(2*(h : ℝ)^20)*b) := by
  have h1 : 1 ≤ h := by omega
  have hhR : (10 : ℝ) ≤ h := by exact_mod_cast hh
  have h0 : (0 : ℝ) < h := by linarith
  have hb0 : 0 < b := (pow_pos h0 _).trans_le hb
  have hc : 2 < (7/10 : ℝ)*rho*h := by
    have hp := mul_le_mul_of_nonneg_left hhR
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 7/10) rho_pos.le)
    nlinarith [collision_rho_bounds.1]
  apply (cube_root_le_scaled h1 hb).trans_lt
  have hs : 1/(h : ℝ) < (7/10 : ℝ)*rho/2 := by
    apply (div_lt_iff₀ h0).mpr
    linarith
  have hm := mul_lt_mul_of_pos_right hs (div_pos hb0 (pow_pos h0 20))
  convert hm using 1 <;> field_simp

/-- The normality scale lies strictly below the smooth-residual cutoff,
uniformly for all retained collision indices. -/
theorem collision_normality_below_cutoff : ∀ᶠ H : ℕ in atTop,
    ∀ᶠ x : ℝ in atTop, ∀ i ≤ R x H,
      normalityScale x i < collisionSmoothCutoff x i := by
  filter_upwards [eventually_collision_indices,ford_band_polynomial_lower 33,
    eventually_ge_atTop 10] with H hind hpoly hH
  filter_upwards [hpoly,B_tendsto.eventually (eventually_gt_atTop (1 : ℝ)),
    m_tendsto.eventually (eventually_ge_atTop H)] with x hp hB hm
  intro i hi
  obtain ⟨hHi,hJ,_⟩ := hind x hm i hi
  have him : i < m x := by unfold R at hi; omega
  have hb := hp i him hHi
  have hr := (ford_collision_layer_ratio hB him hJ).1
  have hb0 := fordBandScale_pos (zero_lt_one.trans hB) him
  have hl : rho/(2*((m x-i : ℕ) : ℝ)^20)*fordBandScale x i ≤
      fordBandScale x (collisionLastIndex x i) := (le_div_iff₀ hb0).mp hr
  apply Real.exp_lt_exp.mpr
  apply Real.exp_lt_exp.mpr
  exact (scaled_cube_root_lt (hH.trans hHi) hb).trans_le
    (mul_le_mul_of_nonneg_left hl (by norm_num))

theorem collision_residual_below_cutoff : ∀ᶠ H : ℕ in atTop,
    ∀ᶠ x : ℝ in atTop, ∀ i ≤ R x H, ∀ η : RemainderDatum (L x H),
      IsBasicRemainder x H η →
      (largestPrimeFactor (collisionResidual η i) : ℝ) < collisionSmoothCutoff x i := by
  filter_upwards [eventually_collision_indices,P_tendsto.eventually (eventually_ge_atTop 1),
    eventually_ge_atTop 2] with H hind hP hH
  filter_upwards [basic_residual_ford_smooth,m_tendsto.eventually (eventually_ge_atTop H)]
    with x hx hm
  intro i hi η hη
  exact hx H (collisionLastIndex x i) (by unfold L; omega) (hind x hm i hi).2.2 η hη

end TotientAsymptotic

end

end OAI
