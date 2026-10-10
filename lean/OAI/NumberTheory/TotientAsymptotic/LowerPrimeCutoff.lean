import OAI.NumberTheory.TotientAsymptotic.ShiftedPrimeCount

namespace OAI

/-! The lower bound on the largest prime has negligible cost in every actual fiber. -/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace TotientAsymptotic

def headCutoffLoss (x : ℝ) : ℝ :=
  (x^(9/10 : ℝ)+1)*Real.exp ((Real.log x)^(4/5 : ℝ))*Real.log x/x

lemma headCutoffLoss_tendsto : Tendsto headCutoffLoss atTop (nhds 0) := by
  have hb : Tendsto (fun x : ℝ => 2*(Real.log x*Real.exp (-(1/20 : ℝ)*Real.log x))) atTop (nhds 0) := by
    simpa only [Real.rpow_one, mul_zero, Function.comp_def] using
      ((tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 (1/20) (by norm_num)).comp
        Real.tendsto_log_atTop).const_mul 2
  apply squeeze_zero' (g := fun x : ℝ => 2*(Real.log x*Real.exp (-(1/20 : ℝ)*Real.log x)))
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    exact div_nonneg (mul_nonneg (mul_nonneg (by positivity) (Real.exp_pos _).le)
      (Real.log_pos hx).le) (zero_lt_one.trans hx).le
  · filter_upwards [eventually_gt_atTop (1 : ℝ),
      subpower_log_ratio.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ)<1/20))] with x hx hs
    have hx0 := zero_lt_one.trans hx
    have hL := Real.log_pos hx
    have hsmall : (Real.log x)^(4/5 : ℝ) ≤ (1/20 : ℝ)*Real.log x :=
      ((div_lt_iff₀ hL).mp hs).le
    have hxpow : 1 ≤ x^(9/10 : ℝ) := Real.one_le_rpow hx.le (by norm_num)
    have he : (x^(9/10 : ℝ)+1)*Real.exp ((Real.log x)^(4/5 : ℝ)) ≤
        2*Real.exp ((19/20 : ℝ)*Real.log x) := by
      calc
        _ ≤ (2*x^(9/10 : ℝ))*Real.exp ((1/20 : ℝ)*Real.log x) :=
          mul_le_mul (by linarith) (Real.exp_le_exp.mpr hsmall) (Real.exp_pos _).le (by positivity)
        _ = _ := by
          rw [Real.rpow_def_of_pos hx0, mul_assoc, ← Real.exp_add]
          congr 2
          ring
    apply (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right he hL.le) hx0.le).trans_eq
    calc
      _ = (2*Real.log x)*(Real.exp ((19/20 : ℝ)*Real.log x)*Real.exp (-Real.log x)) := by
        rw [div_eq_mul_inv, show x⁻¹ = Real.exp (-Real.log x) by rw [Real.exp_neg, Real.exp_log hx0]]
        ring
      _ = _ := by
        rw [← Real.exp_add]
        rw [show (19/20 : ℝ)*Real.log x+-Real.log x = -(1/20 : ℝ)*Real.log x by ring]
        ring
  · exact hb

lemma lower_prime_cutoff_negligible {a ε : ℝ} (ha : 0 < a) (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, ∀ D t : ℝ, 1 ≤ D →
      Real.log D ≤ (Real.log x)^(4/5 : ℝ) → a*x ≤ t →
      x^(9/10 : ℝ)+1 ≤ ε*(t/(D*Real.log x)) := by
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    headCutoffLoss_tendsto.eventually (eventually_lt_nhds (mul_pos hε ha))] with x hx hsmall
  intro D t hD hlogD ht
  have hx0 := zero_lt_one.trans hx
  have hL := Real.log_pos hx
  have hD0 : 0 < D := zero_lt_one.trans_le hD
  have he : D ≤ Real.exp ((Real.log x)^(4/5 : ℝ)) := (Real.log_le_iff_le_exp hD0).mp hlogD
  have hc : 0 ≤ x^(9/10 : ℝ)+1 := by positivity
  have hmain : (x^(9/10 : ℝ)+1)*(D*Real.log x) ≤ ε*t := by
    calc
      _ ≤ (x^(9/10 : ℝ)+1)*(Real.exp ((Real.log x)^(4/5 : ℝ))*Real.log x) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right he hL.le) hc
      _ = headCutoffLoss x*x := by unfold headCutoffLoss; field_simp
      _ ≤ (ε*a)*x := mul_le_mul_of_nonneg_right hsmall.le hx0.le
      _ ≤ ε*t := by nlinarith
  have hdiv := (le_div_iff₀ (mul_pos hD0 hL)).mpr hmain
  convert hdiv using 1; ring

/-- Complete largest-prime asymptotic, with the manuscript's lower cutoff. -/
theorem shifted_prime_uniform_asymptotic (hpnt : PrimeNumberTheoremInput)
    {a : ℝ} (ha : 0 < a) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, ∀ D : ℕ, 0 < D →
      Real.log (D : ℝ) ≤ (Real.log x)^(4/5 : ℝ) → ∀ t : ℝ, a*x ≤ t → t ≤ x →
      |((shiftedPrimeSet x t D).card : ℝ)-t/(D*Real.log x)| ≤ ε*(t/(D*Real.log x)) := by
  filter_upwards [largest_prime_uniform_asymptotic hpnt ha (show 0 < ε/2 by positivity),
    lower_prime_cutoff_negligible ha (show 0 < ε/2 by positivity), eventually_gt_atTop (1 : ℝ)]
    with x hp hc hx
  intro D hD hlogD t ht htx
  have hD1 : (1 : ℝ) ≤ D := by exact_mod_cast hD
  calc
    _ ≤ |((shiftedPrimeSet x t D).card : ℝ)-(Nat.primeCounting ⌊1+t/D⌋₊ : ℝ)|+
        |(Nat.primeCounting ⌊1+t/D⌋₊ : ℝ)-t/(D*Real.log x)| := abs_sub_le _ _ _
    _ ≤ (ε/2)*(t/(D*Real.log x))+(ε/2)*(t/(D*Real.log x)) :=
      add_le_add ((shiftedPrimeSet_cutoff_error (zero_lt_one.trans hx).le t D).trans
        (hc D t hD1 hlogD ht)) (hp D t hD1 hlogD ht htx)
    _ = _ := by ring

end TotientAsymptotic

end

end OAI
