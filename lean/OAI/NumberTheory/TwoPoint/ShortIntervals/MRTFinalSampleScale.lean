import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTExtraSampleScale

namespace OAI

/-! The last ordinary prime band gives a separated-sample count strictly
below the square-root scale. This is the count needed by the integer
Gram kernel before the additional large-prime split. -/

namespace TwoPointCorrelations

open Filter

lemma mrt_final_sample_cost_pointwise {L Y T α : ℝ}
    (hL : 4 ≤ L) (hLL : 16 ≤ Real.log L)
    (hsmall : |Real.log (432*Real.exp 1)|+6*Real.log L+Real.sqrt L ≤ L/200)
    (hY : 1 < Y) (hYL : 200*Real.log L ≤ Real.log Y)
    (hYU : Real.log Y ≤ Real.sqrt L) (hT : 1 < T) (hTU : T ≤ Real.exp L)
    (hα : 0 ≤ α) (hαu : α ≤ 6/25) :
    mrtShortPrimeSampleCost Y (Real.exp (-α*Real.log Y)) T
      (mrtAmplificationOrder Y T) ≤ Real.exp ((99/200:ℝ)*L) := by
  have hL0 : 0 < L := by linarith
  have hL1 : 1 ≤ L := by linarith
  have hlogL0 : 0 ≤ Real.log L := by linarith
  have hlogY : 1 ≤ Real.log Y := by linarith
  have hlogY0 : 0 < Real.log Y := Real.log_pos hY
  have hlogT : Real.log T ≤ L := by
    simpa only [Real.log_exp] using Real.log_le_log (by linarith : 0 < T) hTU
  have hsqrt : Real.sqrt L ≤ L := Real.sqrt_le_self_iff.mpr (Or.inr hL1)
  have hYU' : Real.log Y ≤ L := hYU.trans hsqrt
  let r := mrtAmplificationOrder Y T
  have hrpos : 0 < r := by
    dsimp [r,mrtAmplificationOrder]
    exact Nat.ceil_pos.mpr (div_pos (Real.log_pos hT) hlogY0)
  have hr0 : (0:ℝ) < r := by exact_mod_cast hrpos
  have hr : (r:ℝ) ≤ Real.log T/Real.log Y+1 :=
    (mrt_amplification_order_bounds hY hT.le).2.2.le
  have hrL : (r:ℝ) ≤ 2*L := by
    have hd : Real.log T/Real.log Y ≤ L :=
      (div_le_div_of_nonneg_right hlogT hlogY0.le).trans
        (div_le_self hL0.le hlogY)
    linarith
  have hlog4 : Real.log (4*Y) ≤ 2*L := by
    rw [Real.log_mul (by norm_num : (4:ℝ) ≠ 0) (by linarith : Y ≠ 0)]
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 4)]
  have hrl : 0 ≤ (r:ℝ)*Real.log (4*Y) :=
    mul_nonneg hr0.le (Real.log_nonneg (by linarith))
  have hrlb : (r:ℝ)*Real.log (4*Y) ≤ 4*L^2 := by
    calc
      _ ≤ (2*L)*(2*L) := mul_le_mul hrL hlog4
        (Real.log_nonneg (by linarith)) (by positivity)
      _ = _ := by ring
  have hpref : 24*Real.exp 1*(2+((r:ℝ)*Real.log (4*Y))^2) ≤
      432*Real.exp 1*L^4 := by
    have hs := pow_le_pow_left₀ hrl hrlb 2
    have hL4 : 1 ≤ L^4 := one_le_pow₀ hL1
    have he : (4*L^2)^2 = 16*L^4 := by ring
    rw [he] at hs
    have ht : 2+((r:ℝ)*Real.log (4*Y))^2 ≤ 18*L^4 := by nlinarith
    calc
      _ ≤ 24*Real.exp 1*(18*L^4) := mul_le_mul_of_nonneg_left ht (by positivity)
      _ = _ := by ring
  have hlr : Real.log (8*(r:ℝ)) ≤ 2*Real.log L := by
    have hh := Real.log_le_log (by positivity : 0 < 8*(r:ℝ))
      (mul_le_mul_of_nonneg_left hrL (by norm_num : (0:ℝ) ≤ 8))
    rw [show (8:ℝ)*(2*L)=16*L by ring,
      Real.log_mul (by norm_num : (16:ℝ) ≠ 0) hL0.ne'] at hh
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 16)]
  have hratio : (L/Real.log Y)*(2*Real.log L) ≤ L/100 := by
    have hh := mul_le_mul_of_nonneg_left hYL (show 0 ≤ L/100 by positivity)
    calc
      _ = (L*(2*Real.log L))/Real.log Y := by ring
      _ ≤ L/100 := (div_le_iff₀ hlogY0).mpr (by nlinarith)
  have hentropy : (r:ℝ)*Real.log (8*(r:ℝ)) ≤ L/100+2*Real.log L := by
    have hrr : (r:ℝ) ≤ L/Real.log Y+1 :=
      hr.trans (add_le_add (div_le_div_of_nonneg_right hlogT hlogY0.le) le_rfl)
    calc
      _ ≤ (L/Real.log Y+1)*(2*Real.log L) :=
        mul_le_mul hrr hlr (Real.log_nonneg (by exact_mod_cast
          (show 1 ≤ 8*r by omega))) (by positivity)
      _ = (L/Real.log Y)*(2*Real.log L)+2*Real.log L := by ring
      _ ≤ _ := by linarith
  have horder : (r:ℝ)*Real.log Y ≤ L+Real.sqrt L := by
    have hh := mul_le_mul_of_nonneg_right hr hlogY0.le
    have he : (Real.log T/Real.log Y+1)*Real.log Y = Real.log T+Real.log Y := by
      rw [add_mul,div_mul_cancel₀ _ hlogY0.ne',one_mul]
    rw [he] at hh
    linarith
  have hthreshold : (r:ℝ)*(2*α*Real.log Y) ≤ (12/25:ℝ)*(L+Real.sqrt L) := by
    calc
      _ = (2*α)*((r:ℝ)*Real.log Y) := by ring
      _ ≤ (2*α)*(L+Real.sqrt L) := mul_le_mul_of_nonneg_left horder (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  have hexp : (r:ℝ)*(Real.log (8*(r:ℝ))-
      2*Real.log (Real.exp (-α*Real.log Y))) ≤
      L/100+2*Real.log L+(12/25:ℝ)*(L+Real.sqrt L) := by
    rw [Real.log_exp]
    nlinarith
  have hscalar : Real.log (432*Real.exp 1)+4*Real.log L+
      (L/100+2*Real.log L+(12/25:ℝ)*(L+Real.sqrt L)) ≤ (99/200:ℝ)*L := by
    have ha := le_abs_self (Real.log (432*Real.exp 1))
    have hs := Real.sqrt_nonneg L
    linarith
  have hfour : Real.exp (4*Real.log L)=L^4 := by
    simpa only [Nat.cast_ofNat,Real.exp_log hL0] using Real.exp_nat_mul (Real.log L) 4
  have hc := mrt_short_prime_sample_cost_exp hY (Real.exp_pos (-α*Real.log Y)) hT
  change mrtShortPrimeSampleCost Y (Real.exp (-α*Real.log Y)) T r ≤ _ at hc ⊢
  calc
    _ ≤ (432*Real.exp 1*L^4)*Real.exp
        (L/100+2*Real.log L+(12/25:ℝ)*(L+Real.sqrt L)) :=
      hc.trans (mul_le_mul hpref (Real.exp_le_exp.mpr hexp) (by positivity) (by positivity))
    _ = Real.exp (Real.log (432*Real.exp 1)+4*Real.log L+
        (L/100+2*Real.log L+(12/25:ℝ)*(L+Real.sqrt L))) := by
      conv_rhs =>
        rw [Real.exp_add,Real.exp_add,
          Real.exp_log (by positivity : 0 < 432*Real.exp 1),hfour]
    _ ≤ _ := Real.exp_le_exp.mpr hscalar

/-- Fixed eta=1/100 leaves a strict power saving below square-root sample
size. The endpoint assumptions are only on the actual short prime bin. -/
theorem mrt_final_prime_sample_cost :
    ∀ᶠ L : ℝ in atTop, ∀ Y T α : ℝ, 1 < Y →
      200*Real.log L ≤ Real.log Y → Real.log Y ≤ Real.sqrt L →
      1 < T → T ≤ Real.exp L → 0 ≤ α → α ≤ 6/25 →
      mrtShortPrimeSampleCost Y (Real.exp (-α*Real.log Y)) T
        (mrtAmplificationOrder Y T) ≤ Real.exp ((99/200:ℝ)*L) := by
  have hb := (isLittleO_log_rpow_atTop (show (0:ℝ)<1 by norm_num)).bound
    (show (0:ℝ)<1/3600 by norm_num)
  filter_upwards [hb,eventually_ge_atTop (360000:ℝ),
    eventually_ge_atTop (600*|Real.log (432*Real.exp 1)|),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (16:ℝ))]
    with L hb hL hC hLL
  have hL0 : 0 < L := by linarith
  rw [Real.norm_eq_abs,abs_of_nonneg (by linarith : 0 ≤ Real.log L),
    Real.norm_eq_abs,Real.rpow_one,abs_of_pos hL0] at hb
  have hsqrt : Real.sqrt L ≤ L/600 := by
    apply (Real.sqrt_le_iff).mpr
    constructor
    · positivity
    · have hh := mul_nonneg (show 0 ≤ L-360000 by linarith) hL0.le
      nlinarith
  have hsmall : |Real.log (432*Real.exp 1)|+6*Real.log L+Real.sqrt L ≤ L/200 := by
    linarith
  intro Y T α hY hYL hYU hT hTU hα hαu
  exact mrt_final_sample_cost_pointwise (by linarith) hLL hsmall hY hYL hYU hT hTU hα hαu

/-- Application to the literal finite prime polynomial. -/
theorem mrt_final_prime_large_samples :
    ∀ᶠ L : ℝ in atTop, ∀ Y T α : ℝ, 1 < Y →
      200*Real.log L ≤ Real.log Y → Real.log Y ≤ Real.sqrt L →
      1 < T → T ≤ Real.exp L → 0 ≤ α → α ≤ 6/25 →
      ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) →
      (∀ p ∈ P, Y ≤ (p:ℝ) ∧ (p:ℝ) ≤ 2*Y) →
      ∀ F : ℕ → ℂ, OneBounded F → ∀ S : Finset ℝ,
      (∀ t ∈ S, |t| ≤ T) →
      (∀ t ∈ S, ∀ s ∈ S, t≠s → 1 ≤ |t-s|) →
      (∀ t ∈ S, Real.exp (-α*Real.log Y) ≤ ‖mrtExponentialPolynomial P
        (fun p => F p/(p:ℂ)) (fun p => -Real.log (p:ℝ)) t‖) →
      (S.card:ℝ) ≤ Real.exp ((99/200:ℝ)*L) := by
  filter_upwards [mrt_final_prime_sample_cost] with L hL
  intro Y T α hY hYL hYU hT hTU hα hαu P hP hbin F hF S hS hsep hlarge
  exact (mrt_short_prime_large_samples P hP hY hbin F hF
    (mrtAmplificationOrder Y T) (by linarith) (Real.exp_pos _)
    S hS hsep hlarge).trans (hL Y T α hY hYL hYU hT hTU hα hαu)

end TwoPointCorrelations

end OAI
