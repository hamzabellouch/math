import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTExtraPrimeMass

namespace OAI

/-! Numerical Bonferroni and CRT errors for the additional prime band.
The truncation has order log(log N)/10, small enough for the true finite
interval boundary and large enough for the actual small prime mass. -/

namespace TwoPointCorrelations

lemma mrt_extra_sieve_tail {M L : ℝ} {j : ℕ} (hL : 1 ≤ L)
    (hM : M ≤ Real.log L/50) (hj : Real.log L/5 ≤ (j:ℝ)) :
    Real.exp (2*M)/(2:ℝ)^j ≤ L^(-3/50:ℝ) := by
  have hL0 : 0 < L := by linarith
  have hlog2 : (1/2:ℝ) ≤ Real.log 2 := by
    have hh := Real.one_sub_inv_le_log_of_pos (show (0:ℝ)<2 by norm_num)
    norm_num at hh
    linarith
  rw [← Real.rpow_natCast,Real.rpow_def_of_pos (show (0:ℝ)<2 by norm_num),
    ← Real.exp_sub,Real.rpow_def_of_pos hL0]
  apply Real.exp_le_exp.mpr
  have hm := mul_le_mul_of_nonneg_right hj (show (0:ℝ) ≤ 1/2 by norm_num)
  have hn := mul_le_mul_of_nonneg_left hlog2 (Nat.cast_nonneg j)
  nlinarith

lemma mrt_extra_sieve_boundary {L Q C : ℝ} (N r : ℕ)
    (hL : 1 ≤ L) (hLL : 100 ≤ Real.log L)
    (hsmall : Real.log L/5+3 ≤ L/20)
    (hQ0 : 0 ≤ Q) (hQ : Q ≤ Real.exp (L/Real.log L))
    (hC0 : 0 ≤ C) (hC : C ≤ Q) (hN : Real.exp L ≤ N)
    (hr : ((2*r+1:ℕ):ℝ) ≤ Real.log L/5+3) :
    (1/(N:ℝ))*((2*r+1:ℕ):ℝ)*(C*Q+1)^(2*r) ≤ Real.exp (-L/4) := by
  have hL0 : 0 < L := by linarith
  have hlog : 0 < Real.log L := by linarith
  have hN0 : (0:ℝ) < N := (Real.exp_pos L).trans_le hN
  have hbase : 1 ≤ C*Q+1 := by nlinarith [mul_nonneg hC0 hQ0]
  have hbase0 : 0 < C*Q+1 := by linarith
  have hb : C*Q+1 ≤ 2*Real.exp (2*L/Real.log L) := by
    have hcq : C*Q ≤ Q^2 := by
      nlinarith [mul_le_mul_of_nonneg_right hC hQ0]
    have hq2 := pow_le_pow_left₀ hQ0 hQ 2
    have hexp : (Real.exp (L/Real.log L))^2 = Real.exp (2*L/Real.log L) := by
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    rw [hexp] at hq2
    have he1 : 1 ≤ Real.exp (2*L/Real.log L) := Real.one_le_exp (by positivity)
    linarith
  have hlogbase : Real.log (C*Q+1) ≤ Real.log 2+2*L/Real.log L := by
    have hh := Real.log_le_log hbase0 hb
    simpa only [Real.log_mul (by norm_num : (2:ℝ) ≠ 0) (Real.exp_ne_zero _),
      Real.log_exp] using hh
  have hlog20 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlog21 : Real.log 2 ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]
  have hr' : ((2*r:ℕ):ℝ) ≤ Real.log L/5+3 := by
    push_cast at hr ⊢
    linarith
  have hfrac : 6*L/Real.log L ≤ (3/50:ℝ)*L := by
    apply (div_le_iff₀ hlog).mpr
    have hh := mul_le_mul_of_nonneg_right hLL
      (show 0 ≤ (3/50:ℝ)*L by positivity)
    nlinarith
  have hprod : (Real.log L/5+3)*(1+2*L/Real.log L) =
      (Real.log L/5+3)+2*L/5+6*L/Real.log L := by
    field_simp
    ring
  have hexponent : ((2*r:ℕ):ℝ)*Real.log (C*Q+1) ≤ (3/5:ℝ)*L := by
    calc
      _ ≤ (Real.log L/5+3)*(Real.log 2+2*L/Real.log L) :=
        mul_le_mul hr' hlogbase (Real.log_nonneg hbase) (by positivity)
      _ ≤ (Real.log L/5+3)*(1+2*L/Real.log L) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ ≤ _ := by rw [hprod]; linarith
  have hpow : (C*Q+1)^(2*r) ≤ Real.exp ((3/5:ℝ)*L) := by
    rw [mrt_nat_pow_eq_exp hbase0]
    exact Real.exp_le_exp.mpr hexponent
  have hj : ((2*r+1:ℕ):ℝ) ≤ Real.exp (L/20) :=
    (hr.trans hsmall).trans (by linarith [Real.add_one_le_exp (L/20)])
  have hinv : 1/(N:ℝ) ≤ Real.exp (-L) := by
    rw [Real.exp_neg,← one_div]
    exact one_div_le_one_div_of_le (Real.exp_pos _) hN
  calc
    _ ≤ Real.exp (-L)*Real.exp (L/20)*Real.exp ((3/5:ℝ)*L) :=
      mul_le_mul (mul_le_mul hinv hj (by positivity) (by positivity)) hpow
        (by positivity) (by positivity)
    _ = Real.exp ((-7/20:ℝ)*L) := by rw [← Real.exp_add,← Real.exp_add]; congr 1; ring
    _ ≤ _ := Real.exp_le_exp.mpr (by linarith)

end TwoPointCorrelations

end OAI
