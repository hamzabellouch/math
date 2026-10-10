import OAI.NumberTheory.TotientAsymptotic.FordKernel

namespace OAI

/-! The remaining finite choices fit inside the recovered collision saving. -/

noncomputable section

namespace TotientAsymptotic

lemma canceled_mass_power_bound {M Y h : ℝ} {c : ℕ}
    (hY : 1 ≤ Y) (hh : 1 ≤ h) (hc : (c : ℝ) ≤ h)
    (hlog : Real.log Y ≤ 26*h) :
    (2*(|Real.log M|+3*Y))^c ≤ Real.exp ((2*|Real.log M|+32)*h^2) := by
  let K := 2*|Real.log M|+6
  have hK : 0 < K := by dsimp [K]; positivity
  have hY0 : 0 < Y := zero_lt_one.trans_le hY
  have hbase : 2*(|Real.log M|+3*Y) ≤ K*Y := by
    have hm := mul_le_mul_of_nonneg_left hY (abs_nonneg (Real.log M))
    dsimp [K]
    nlinarith
  have hlogK : Real.log K ≤ K := Real.log_le_self hK.le
  have he : (K*Y)^c=Real.exp ((c : ℝ)*(Real.log K+Real.log Y)) := by
    rw [← Real.log_mul hK.ne' hY0.ne',Real.exp_nat_mul,Real.exp_log (mul_pos hK hY0)]
  apply (pow_le_pow_left₀ (by positivity) hbase c).trans
  rw [he]
  apply Real.exp_le_exp.mpr
  have hm := mul_le_mul_of_nonneg_left (add_le_add hlogK hlog) (Nat.cast_nonneg c : (0 : ℝ) ≤ c)
  have hm' := mul_le_mul_of_nonneg_right hc (show 0 ≤ K+26*h by positivity)
  have hk := mul_le_mul_of_nonneg_left hh (show 0 ≤ K*h by positivity)
  dsimp [K] at *
  nlinarith

lemma smooth_choice_cost {M z : ℝ} (hM : 0 < M) (hz : 1 < z) (hlz : 1 ≤ Real.log z) :
    M*Real.log (⌈z⌉₊ : ℝ) ≤ Real.exp (|Real.log M|+1+B z) := by
  have hceil0 : (0 : ℝ) < ⌈z⌉₊ := lt_of_lt_of_le (zero_lt_one.trans hz) (Nat.le_ceil z)
  have hceil : (⌈z⌉₊ : ℝ) ≤ 2*z := by have := Nat.ceil_lt_add_one (zero_lt_one.trans hz).le; linarith
  have hlog := Real.log_le_log hceil0 hceil
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (zero_lt_one.trans hz).ne'] at hlog
  have hlog2 : Real.log (⌈z⌉₊ : ℝ) ≤ 2*Real.log z := by linarith [Real.log_two_lt_d9]
  have hm : M ≤ Real.exp |Real.log M| := by
    conv_lhs => rw [← Real.exp_log hM]
    exact Real.exp_le_exp.mpr (le_abs_self _)
  calc
    _ ≤ Real.exp (|Real.log M|)*(2*Real.log z) :=
      mul_le_mul hm hlog2 (Real.log_nonneg (hz.trans_le (Nat.le_ceil z)).le) (Real.exp_pos _).le
    _ = Real.exp (|Real.log M|+Real.log 2+B z) := by
      rw [Real.exp_add,Real.exp_add,Real.exp_log (by norm_num : (0 : ℝ) < 2),
        B,Real.exp_log (Real.log_pos hz)]
      ring
    _ ≤ _ := Real.exp_le_exp.mpr (by linarith [Real.log_two_lt_d9])

lemma residual_choice_exponent {Y h Z : ℝ} (hY : 0 ≤ Y) (hh : 2 ≤ h)
    (hZ : Z ≤ 2*Y/h^18) : Z ≤ Y/(16*h^4) := by
  have hh0 : 0 < h := by linarith
  have hp : (32 : ℝ) ≤ h^14 := by
    have ht := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hh 14
    norm_num at ht
    linarith
  have hdiv : 2/h^14 ≤ (1/16 : ℝ) := by
    apply (div_le_iff₀ (pow_pos hh0 _)).mpr
    linarith
  have hmul := mul_le_mul_of_nonneg_right hdiv (div_nonneg hY (pow_nonneg hh0.le 4))
  apply hZ.trans
  convert hmul using 1 <;> field_simp

lemma subset_choice_cost {J : ℕ} {h : ℝ} (hh : 1 ≤ h) (hJ : (J : ℝ) ≤ h) :
    (2 : ℝ)^J ≤ Real.exp (h^2) := by
  rw [← Real.exp_log (by norm_num : (0 : ℝ) < 2),← Real.exp_nat_mul]
  apply Real.exp_le_exp.mpr
  have hj : (J : ℝ)*Real.log 2 ≤ J := by
    have := mul_le_mul_of_nonneg_left Real.log_two_lt_d9.le (Nat.cast_nonneg J : (0 : ℝ) ≤ J)
    nlinarith [Nat.cast_nonneg (α := ℝ) J]
  have hs := mul_le_mul_of_nonneg_left hh (show 0 ≤ h by linarith)
  nlinarith

lemma rounded_prime_endpoint_height {y : ℝ} (hy : 1 < y)
    (hlog : 1 ≤ Real.log y) (hB : 1 ≤ B y) :
    2 ≤ ⌈y+1⌉₊ ∧ B (⌈y+1⌉₊ : ℝ) ≤ 3*B y := by
  have hnlo : y+1 ≤ (⌈y+1⌉₊ : ℝ) := Nat.le_ceil _
  have hnhi : (⌈y+1⌉₊ : ℝ) ≤ 3*y := by
    have ht := (Nat.ceil_lt_add_one (show 0 ≤ y+1 by linarith)).le
    linarith
  have hn1 : (1 : ℝ) < ⌈y+1⌉₊ := by linarith
  have hp := Real.log_le_log (zero_lt_one.trans hn1) hnhi
  rw [Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) (zero_lt_one.trans hy).ne'] at hp
  have hl3 : Real.log (3 : ℝ) ≤ 2 := by
    have ht := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
    linarith
  have hlog' : Real.log (⌈y+1⌉₊ : ℝ) ≤ 3*Real.log y := by linarith
  have hB' := Real.log_le_log (Real.log_pos hn1) hlog'
  rw [Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) (by linarith : Real.log y ≠ 0)] at hB'
  have hn2 : 2 ≤ ⌈y+1⌉₊ := by
    have ht : 1 < ⌈y+1⌉₊ := by exact_mod_cast hn1
    omega
  refine ⟨hn2,?_⟩
  change Real.log (Real.log (⌈y+1⌉₊ : ℝ)) ≤ 3*B y
  change 1 ≤ Real.log (Real.log y) at hB
  change Real.log (Real.log (⌈y+1⌉₊ : ℝ)) ≤ Real.log 3+Real.log (Real.log y) at hB'
  change _ ≤ 3*Real.log (Real.log y)
  linarith

lemma canceled_rounded_mass_power {M y : ℝ} {c : ℕ} (hy : 1 < y)
    (hlog : 1 ≤ Real.log y) (hB : 1 ≤ B y) :
    (2*(Real.log M+B (⌈y+1⌉₊ : ℝ)))^c ≤ (2*(|Real.log M|+3*B y))^c := by
  have hheight := (rounded_prime_endpoint_height hy hlog hB).2
  have hyle : y ≤ (⌈y+1⌉₊ : ℝ) := by have ht := Nat.le_ceil (y+1); linarith
  have hlogmono := Real.log_le_log (zero_lt_one.trans hy) hyle
  have hBmono := Real.log_le_log (Real.log_pos hy) hlogmono
  have hnonneg : 0 ≤ B (⌈y+1⌉₊ : ℝ) := (zero_le_one.trans hB).trans hBmono
  calc
    _ ≤ |(2*(Real.log M+B (⌈y+1⌉₊ : ℝ)))^c| := le_abs_self _
    _ = |2*(Real.log M+B (⌈y+1⌉₊ : ℝ))|^c := abs_pow _ _
    _ ≤ _ := by
      apply pow_le_pow_left₀ (abs_nonneg _)
      rw [abs_mul,abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      have ha := abs_add_le (Real.log M) (B (⌈y+1⌉₊ : ℝ))
      rw [abs_of_nonneg hnonneg] at ha
      nlinarith

end TotientAsymptotic

end

end OAI
