import OAI.NumberTheory.TotientAsymptotic.RenewalConvolution

namespace OAI

/-! Uniform exponential approximation for the shrinking tail of a simplex. -/

noncomputable section
open scoped Topology
open Filter

namespace TotientAsymptotic

lemma log_one_sub_quadratic {q : ℝ} (hq : 0 ≤ q) (hq' : q ≤ 1/2) :
    |Real.log (1-q)+q| ≤ q^2 := by
  have hq1 : q < 1 := by linarith
  have hz : ‖(-q : ℂ)‖ < 1 := by
    simpa only [norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hq] using hq1
  have h := Complex.norm_log_one_add_sub_self_le hz
  have he : (1+(-q : ℂ)) = ((1-q : ℝ) : ℂ) := by push_cast; ring
  rw [he, ← Complex.ofReal_log (by linarith : 0 ≤ 1-q)] at h
  have hn : ‖((Real.log (1-q) : ℂ)-(-q : ℂ))‖ = |Real.log (1-q)+q| := by
    norm_cast
    rw [Real.norm_eq_abs, sub_neg_eq_add]
  rw [hn] at h
  simp only [norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hq] at h
  apply h.trans
  have hden : 0 < 1-q := by linarith
  rw [← div_eq_mul_inv, div_div, div_le_iff₀ (mul_pos hden (by norm_num))]
  nlinarith [sq_nonneg q]

/-- If `n*q` approaches a bounded nonnegative quantity, the simplex power
approaches its exponential, even when that quantity varies with the phase. -/
theorem simplex_power_approximation {ι : Type*} {l : Filter ι}
    (n : ι → ℕ) (q b : ι → ℝ) (K : ℝ) (_hK : 0 ≤ K)
    (hn : Tendsto n l atTop)
    (hq : ∀ᶠ x in l, 0 ≤ q x)
    (hb : ∀ᶠ x in l, 0 ≤ b x ∧ b x ≤ K)
    (herr : Tendsto (fun x => (n x : ℝ)*q x-b x) l (nhds 0)) :
    Tendsto (fun x => (max (1-q x) 0)^(n x)-Real.exp (-b x)) l (nhds 0) := by
  have hnR : Tendsto (fun x => (n x : ℝ)) l atTop :=
    tendsto_natCast_atTop_atTop.comp hn
  have ha : ∀ᶠ x in l, (n x : ℝ)*q x ≤ K+1 := by
    filter_upwards [herr.eventually (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)), hb]
      with x he hb
    linarith
  have hqbound : ∀ᶠ x in l, q x ≤ (K+1)*(n x : ℝ)⁻¹ := by
    filter_upwards [ha, hnR.eventually (eventually_gt_atTop 0)] with x ha hn0
    rw [← div_eq_mul_inv, le_div_iff₀ hn0]
    nlinarith
  have hq0 : Tendsto q l (nhds 0) := by
    apply squeeze_zero' hq hqbound
    simpa using (tendsto_inv_atTop_zero.comp hnR).const_mul (K+1)
  have hqhalf : ∀ᶠ x in l, q x ≤ 1/2 :=
    hq0.eventually (eventually_le_nhds (by norm_num : (0 : ℝ) < 1/2))
  have hlog : Tendsto (fun x => (n x : ℝ)*(Real.log (1-q x)+q x)) l (nhds 0) := by
    apply squeeze_zero_norm' (a := fun x => (K+1)*q x)
    · filter_upwards [hq, hqhalf, ha] with x hq hqhalf ha
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Nat.cast_nonneg (n x))]
      calc
        _ ≤ (n x : ℝ)*(q x)^2 := mul_le_mul_of_nonneg_left
          (log_one_sub_quadratic hq hqhalf) (Nat.cast_nonneg _)
        _ ≤ (K+1)*q x := by nlinarith
    · simpa using hq0.const_mul (K+1)
  have hexp : Tendsto (fun x => (n x : ℝ)*Real.log (1-q x)+b x) l (nhds 0) := by
    convert hlog.sub herr using 1
    · funext x
      ring
    · simp
  have hsmall : Tendsto (fun x => Real.exp ((n x : ℝ)*Real.log (1-q x)+b x)-1)
      l (nhds 0) := by simpa using (Real.tendsto_exp_nhds_zero_nhds_one.comp hexp).sub_const 1
  apply squeeze_zero_norm' (a := fun x =>
    |Real.exp ((n x : ℝ)*Real.log (1-q x)+b x)-1|)
  · filter_upwards [hq, hqhalf, hb] with x hqx hqx' hbx
    have hbase : 0 < 1-q x := by linarith
    have hp : (max (1-q x) 0)^(n x) =
        Real.exp ((n x : ℝ)*Real.log (1-q x)) := by
      rw [max_eq_left hbase.le, Real.exp_nat_mul, Real.exp_log hbase]
    rw [hp, Real.norm_eq_abs]
    have he : Real.exp ((n x : ℝ)*Real.log (1-q x))-Real.exp (-b x) =
        Real.exp (-b x)*(Real.exp ((n x : ℝ)*Real.log (1-q x)+b x)-1) := by
      rw [mul_sub, ← Real.exp_add, mul_one]
      congr 2
      ring
    rw [he, abs_mul, abs_of_pos (Real.exp_pos _)]
    exact mul_le_of_le_one_left (abs_nonneg _)
      (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hbx.1))
  · simpa using hsmall.abs

end TotientAsymptotic

end

end OAI
