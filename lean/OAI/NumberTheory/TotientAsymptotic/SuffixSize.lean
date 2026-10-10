import OAI.NumberTheory.TotientAsymptotic.ResidualCutoff

namespace OAI

/-! Deterministic size estimates for the complete remainder of a basic witness. -/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace TotientAsymptotic

lemma basic_prime_log_le {x : ℝ} {H r : ℕ}
    {η : RemainderDatum (L x H)} (hη : IsBasicRemainder x H η)
    (hr : r ∈ Finset.Icc 1 (L x H)) :
    Real.log (remainderPrime η r : ℝ) ≤ Real.exp ((11/10 : ℝ)*bandScale x r) := by
  have hp := hη.2.1 r hr
  have hpos : (1 : ℝ) < remainderPrime η r := by exact_mod_cast hp.1.one_lt
  have hr0 : r ≠ 0 := by have := (Finset.mem_Icc.mp hr).1; omega
  apply (Real.log_le_iff_le_exp (Real.log_pos hpos)).mp
  simpa only [remainderCoord, ite_eq_right hr0] using hp.2.2

lemma log_suffixPreimage {x : ℝ} {H j : ℕ}
    {η : RemainderDatum (L x H)} (hη : IsBasicRemainder x H η) :
    Real.log (suffixPreimage η j : ℝ) = Real.log (η.cofactor : ℝ)+
      ∑ r ∈ Finset.Icc (j+1) (L x H), Real.log (remainderPrime η r : ℝ) := by
  have hcof : (η.cofactor : ℝ) ≠ 0 := by exact_mod_cast hη.1.ne'
  have hp (r : ℕ) (hr : r ∈ Finset.Icc (j+1) (L x H)) :
      (remainderPrime η r : ℝ) ≠ 0 := by
    have hr' : r ∈ Finset.Icc 1 (L x H) := Finset.mem_Icc.mpr
      ⟨by have := (Finset.mem_Icc.mp hr).1; omega, (Finset.mem_Icc.mp hr).2⟩
    exact_mod_cast (hη.2.1 r hr').1.ne_zero
  simp only [suffixPreimage, Nat.cast_mul, Nat.cast_prod]
  rw [Real.log_mul hcof (Finset.prod_ne_zero_iff.mpr hp), Real.log_prod hp]

/-- All factors after a cutoff are bounded by the first band after it. This
keeps the cofactor separate and permits repetitions of the last prime. -/
theorem basic_suffix_log_bound {x : ℝ} {H j : ℕ}
    {η : RemainderDatum (L x H)} (hη : IsBasicRemainder x H η) :
    Real.log (suffixPreimage η j : ℝ) ≤
      (L x H-j : ℕ)*Real.exp ((11/10 : ℝ)*bandScale x (j+1))+
        Real.exp (2*bandScale x (L x H)) := by
  rw [log_suffixPreimage hη]
  have hs : (∑ r ∈ Finset.Icc (j+1) (L x H), Real.log (remainderPrime η r : ℝ)) ≤
      (L x H-j : ℕ)*Real.exp ((11/10 : ℝ)*bandScale x (j+1)) := by
    calc
      _ ≤ ∑ _r ∈ Finset.Icc (j+1) (L x H), Real.exp ((11/10 : ℝ)*bandScale x (j+1)) := by
        apply Finset.sum_le_sum
        intro r hr
        have hr' : r ∈ Finset.Icc 1 (L x H) := Finset.mem_Icc.mpr
          ⟨by have := (Finset.mem_Icc.mp hr).1; omega, (Finset.mem_Icc.mp hr).2⟩
        exact (basic_prime_log_le hη hr').trans (Real.exp_le_exp.mpr
          (mul_le_mul_of_nonneg_left (bandScale_antitone x (Finset.mem_Icc.mp hr).1)
            (by norm_num)))
      _ = _ := by simp [Nat.card_Icc]
  linarith [hη.2.2.2.2]

lemma m_le_log_B : ∀ᶠ x : ℝ in atTop, (m x : ℝ) ≤ Real.log (B x)/lam := by
  filter_upwards [B_tendsto.eventually (eventually_gt_atTop (Real.exp 1 : ℝ)),
    (psi_tendsto.comp B_tendsto).eventually (eventually_ge_atTop (0 : ℝ))] with x hB hpsi
  have hlog : 1 < Real.log (B x) := by rwa [Real.lt_log_iff_exp_lt ((Real.exp_pos 1).trans hB)]
  have hfloor := Nat.floor_le hpsi
  change (m x : ℝ) ≤ psi (B x) at hfloor
  exact hfloor.trans (by
    unfold psi
    exact div_le_div_of_nonneg_right (sub_le_self _ (Real.log_nonneg hlog.le)) lam_pos.le)

/-- The total logarithmic size of a basic remainder is uniformly smaller
than the largest-prime scale. -/
theorem basic_remainder_log_small (H : ℕ) :
    ∀ᶠ x : ℝ in atTop, ∀ η : RemainderDatum (L x H), IsBasicRemainder x H η →
      Real.log (suffixPreimage η 0 : ℝ) ≤ (Real.log x)^(4/5 : ℝ) := by
  let C := Real.exp (2*(lam/rho)*(P H : ℝ)*(rho^(P H))⁻¹)
  have hsmall : Tendsto (fun b : ℝ => (Real.log b/lam)*Real.exp (-(1/10 : ℝ)*b)+
      C*Real.exp (-(4/5 : ℝ)*b)) atTop (nhds 0) := by
    have he : Tendsto (fun b : ℝ => b*Real.exp (-(1/10 : ℝ)*b)) atTop (nhds 0) := by
      simpa only [Real.rpow_one] using tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 (1/10) (by norm_num : (0 : ℝ)<1/10)
    have he' : Tendsto (fun b : ℝ => Real.log b*Real.exp (-(1/10 : ℝ)*b)) atTop (nhds 0) := by
      apply squeeze_zero'
      · filter_upwards [eventually_ge_atTop (1 : ℝ)] with b hb
        exact mul_nonneg (Real.log_nonneg hb) (Real.exp_pos _).le
      · filter_upwards [eventually_ge_atTop (1 : ℝ)] with b hb
        exact mul_le_mul_of_nonneg_right (Real.log_le_self (zero_le_one.trans hb)) (Real.exp_pos _).le
      · exact he
    have hce : Tendsto (fun b : ℝ => Real.exp (-(4/5 : ℝ)*b)) atTop (nhds 0) := by
      apply Real.tendsto_exp_atBot.comp
      exact tendsto_id.const_mul_atTop_of_neg (by norm_num)
    simpa only [div_mul_eq_mul_div, zero_div, mul_zero, add_zero] using
      (he'.div_const lam).add (hce.const_mul C)
  filter_upwards [m_le_log_B, B_tendsto.eventually (eventually_gt_atTop (0 : ℝ)),
    eventually_gt_atTop (1 : ℝ), m_tendsto.eventually (eventually_gt_atTop (P H)),
    theta_eventually_mem, (hsmall.comp B_tendsto).eventually (eventually_lt_nhds (by norm_num : (0 : ℝ)<1)),
    B_tendsto.eventually (eventually_gt_atTop (1 : ℝ)),
    bandCenterRatio_tendsto.eventually (eventually_gt_nhds (by norm_num : (9/10 : ℝ)<1))]
    with x hm hB hx hPm htheta hs hB1 hratio
  intro η hη
  have hmpos : 0 < m x := by omega
  have hb0 : bandScale x 0 ≤ (10/9 : ℝ)*B x := by
    have hf := fordBandScale_eq_ratio_mul hB1 hmpos
    have he : fordBandScale x 0 = B x := by simp [fordBandScale]
    rw [he] at hf
    nlinarith [bandScale_nonnegative x 0]
  have hb1 : (11/10 : ℝ)*bandScale x 1 ≤ (7/10 : ℝ)*B x := by
    have hb := bandScale_succ_le x 0
    have hr := collision_rho_bounds.2
    have hp := bandScale_nonnegative x 0
    have : bandScale x 1 ≤ (137/250 : ℝ)*((10/9 : ℝ)*B x) :=
      hb.trans (mul_le_mul hr.le hb0 hp (by norm_num))
    nlinarith
  have hbL : bandScale x (L x H) ≤ (lam/rho)*(P H : ℝ)*(rho^(P H))⁻¹ := by
    have he : m x-L x H = P H := by unfold L; omega
    simp only [bandScale, he]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (alpha_le _ htheta) (Nat.cast_nonneg _))
      (inv_nonneg.mpr (pow_pos rho_pos _).le)
  have hbound := basic_suffix_log_bound hη (j := 0)
  have hlast : Real.exp (2*bandScale x (L x H)) ≤ C :=
    Real.exp_le_exp.mpr (by nlinarith [hbL])
  have hmL0 : (L x H : ℝ) ≤ m x := by exact_mod_cast Nat.sub_le (m x) (P H)
  have hmL : (L x H : ℝ) ≤ Real.log (B x)/lam := hmL0.trans hm
  have hlog : Real.log (suffixPreimage η 0 : ℝ) ≤
      (Real.log (B x)/lam)*Real.exp ((7/10 : ℝ)*B x)+C := by
    simp only [Nat.sub_zero] at hbound
    exact hbound.trans (add_le_add (mul_le_mul hmL (Real.exp_le_exp.mpr hb1)
      (Real.exp_pos _).le (div_nonneg (Real.log_nonneg hB1.le) lam_pos.le)) hlast)
  have heq : ((Real.log (B x)/lam)*Real.exp ((7/10 : ℝ)*B x)+C)*
      Real.exp (-(4/5 : ℝ)*B x) =
      (Real.log (B x)/lam)*Real.exp (-(1/10 : ℝ)*B x)+C*Real.exp (-(4/5 : ℝ)*B x) := by
    rw [add_mul, mul_assoc, ← Real.exp_add]
    rw [show (7/10 : ℝ)*B x+(-(4/5 : ℝ)*B x) = -(1/10 : ℝ)*B x by ring]
  have hlt : (Real.log (B x)/lam)*Real.exp ((7/10 : ℝ)*B x)+C ≤ Real.exp ((4/5 : ℝ)*B x) := by
    have ht : ((Real.log (B x)/lam)*Real.exp ((7/10 : ℝ)*B x)+C)*Real.exp (-(4/5 : ℝ)*B x) < 1 := by rwa [heq]
    have hh := mul_lt_mul_of_pos_right ht (Real.exp_pos ((4/5 : ℝ)*B x))
    rw [mul_assoc, ← Real.exp_add] at hh
    norm_num at hh
    exact hh.le
  apply hlog.trans (hlt.trans_eq ?_)
  rw [Real.rpow_def_of_pos (Real.log_pos hx)]
  congr 1
  simp only [B]
  ring

end TotientAsymptotic

end

end OAI
