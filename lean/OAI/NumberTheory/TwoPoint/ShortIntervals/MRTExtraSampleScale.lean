import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTSampleCost
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace OAI

/-! The large-value sample count for the additional prime interval.
The lower-endpoint complement 1/80 is deliberately smaller than the published proof's
optimized choice; it preserves the exact MRT input rates. -/

namespace TwoPointCorrelations

open Filter

lemma mrt_extra_sample_cost_pointwise {L Y T : ℝ}
    (hL : 4 ≤ L) (hLL : 1 ≤ Real.log L)
    (hsmall : (|Real.log (432*Real.exp 1)|+436)*Real.log L ≤ L^(7/(400:ℝ)))
    (hY : 1 < Y) (hYL : L^(79/(80:ℝ)) ≤ Real.log Y)
    (hYU : Real.log Y ≤ L) (hT : 1 < T) (hTU : T ≤ Real.exp L) :
    mrtShortPrimeSampleCost Y (L^(-100:ℝ)) T (mrtAmplificationOrder Y T) ≤
      Real.exp (L^(3/(100:ℝ))) := by
  have hL0 : 0 < L := by linarith
  have hL1 : 1 ≤ L := by linarith
  have hV : 0 < L^(-100:ℝ) := Real.rpow_pos_of_pos hL0 _
  let r := mrtAmplificationOrder Y T
  have hrpos : 0 < r := by
    dsimp [r,mrtAmplificationOrder]
    exact Nat.ceil_pos.mpr (div_pos (Real.log_pos hT) (Real.log_pos hY))
  have hr0 : (0:ℝ) < r := by exact_mod_cast hrpos
  have hlogT : Real.log T ≤ L := by
    simpa only [Real.log_exp] using Real.log_le_log (by linarith : 0 < T) hTU
  have hpow1 : 1 ≤ L^(1/(80:ℝ)) := Real.one_le_rpow hL1 (by norm_num)
  have hpowL : L^(1/(80:ℝ)) ≤ L := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hL1 (show (1/(80:ℝ)) ≤ 1 by norm_num)
  have hratio : L/L^(79/(80:ℝ)) = L^(1/(80:ℝ)) := by
    apply (div_eq_iff (Real.rpow_pos_of_pos hL0 _).ne').mpr
    rw [← Real.rpow_add hL0]
    norm_num
  have hr : (r:ℝ) ≤ 2*L^(1/(80:ℝ)) := by
    have hceil := (mrt_amplification_order_bounds hY hT.le).2.2.le
    change (r:ℝ) ≤ _ at hceil
    calc
      _ ≤ Real.log T/Real.log Y+1 := hceil
      _ ≤ L/L^(79/(80:ℝ))+1 := by
        have hd := (div_le_div_of_nonneg_right hlogT (Real.log_pos hY).le).trans
          (div_le_div_of_nonneg_left hL0.le (Real.rpow_pos_of_pos hL0 _) hYL)
        linarith
      _ ≤ _ := by rw [hratio]; linarith
  have hrL : (r:ℝ) ≤ 2*L := hr.trans (mul_le_mul_of_nonneg_left hpowL (by norm_num))
  have hlog4 : Real.log (4*Y) ≤ 2*L := by
    rw [Real.log_mul (by norm_num : (4:ℝ) ≠ 0) (by linarith : Y ≠ 0)]
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 4)
    linarith
  have hrl : 0 ≤ (r:ℝ)*Real.log (4*Y) :=
    mul_nonneg hr0.le (Real.log_nonneg (by linarith))
  have hrlb : (r:ℝ)*Real.log (4*Y) ≤ 4*L^2 := by
    calc
      _ ≤ (2*L)*(2*L) := mul_le_mul hrL hlog4 (Real.log_nonneg (by linarith)) (by positivity)
      _ = _ := by ring
  have hL4 : 1 ≤ L^4 := one_le_pow₀ hL1
  have hpref : 24*Real.exp 1*(2+((r:ℝ)*Real.log (4*Y))^2) ≤
      432*Real.exp 1*L^4 := by
    have hs := pow_le_pow_left₀ hrl hrlb 2
    have he : (4*L^2)^2 = 16*L^4 := by ring
    rw [he] at hs
    have ht : 2+((r:ℝ)*Real.log (4*Y))^2 ≤ 18*L^4 := by nlinarith
    calc
      _ ≤ 24*Real.exp 1*(18*L^4) :=
        mul_le_mul_of_nonneg_left ht (by positivity)
      _ = _ := by ring
  have hlr : Real.log (8*(r:ℝ)) ≤ 16*Real.log L := by
    have hh := Real.log_le_log (by positivity : 0 < 8*(r:ℝ))
      (mul_le_mul_of_nonneg_left hrL (by norm_num : (0:ℝ) ≤ 8))
    have he : (8:ℝ)*(2*L)=16*L := by ring
    rw [he,Real.log_mul (by norm_num : (16:ℝ) ≠ 0) hL0.ne'] at hh
    have h16 := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 16)
    linarith
  have hlogV : Real.log (L^(-100:ℝ)) = -100*Real.log L := by
    rw [Real.log_rpow hL0]
  have hexp : (r:ℝ)*(Real.log (8*(r:ℝ))-2*Real.log (L^(-100:ℝ))) ≤
      432*L^(1/(80:ℝ))*Real.log L := by
    rw [hlogV]
    calc
      _ ≤ (r:ℝ)*(216*Real.log L) := mul_le_mul_of_nonneg_left (by linarith) hr0.le
      _ ≤ (2*L^(1/(80:ℝ)))*(216*Real.log L) :=
        mul_le_mul_of_nonneg_right hr (by positivity)
      _ = _ := by ring
  have hscalar : Real.log (432*Real.exp 1)+4*Real.log L+
      432*L^(1/(80:ℝ))*Real.log L ≤ L^(3/(100:ℝ)) := by
    have hbig : 1 ≤ L^(1/(80:ℝ))*Real.log L := one_le_mul_of_one_le_of_one_le hpow1 hLL
    have hc : Real.log (432*Real.exp 1) ≤
        |Real.log (432*Real.exp 1)| * (L^(1/(80:ℝ))*Real.log L) := by
      exact (le_abs_self _).trans (le_mul_of_one_le_right (abs_nonneg _) hbig)
    have hlog : Real.log L ≤ L^(1/(80:ℝ))*Real.log L :=
      le_mul_of_one_le_left (by positivity) hpow1
    calc
      _ ≤ L^(1/(80:ℝ))*((|Real.log (432*Real.exp 1)|+436)*Real.log L) := by nlinarith
      _ ≤ L^(1/(80:ℝ))*L^(7/(400:ℝ)) :=
        mul_le_mul_of_nonneg_left hsmall (Real.rpow_nonneg hL0.le _)
      _ = _ := by rw [← Real.rpow_add hL0]; norm_num
  have he := mrt_short_prime_sample_cost_exp hY hV hT
  have hfour : Real.exp (4*Real.log L) = L^4 := by
    simpa only [Nat.cast_ofNat,Real.exp_log hL0] using
      Real.exp_nat_mul (Real.log L) 4
  change mrtShortPrimeSampleCost Y (L^(-100:ℝ)) T r ≤ _ at he ⊢
  calc
    _ ≤ (432*Real.exp 1*L^4)*Real.exp (432*L^(1/(80:ℝ))*Real.log L) :=
      he.trans (mul_le_mul hpref (Real.exp_le_exp.mpr hexp) (by positivity) (by positivity))
    _ = Real.exp (Real.log (432*Real.exp 1)+4*Real.log L+
        432*L^(1/(80:ℝ))*Real.log L) := by
      rw [Real.exp_add,Real.exp_add,Real.exp_log (by positivity : 0 < 432*Real.exp 1),
        hfour]
    _ ≤ _ := Real.exp_le_exp.mpr hscalar

/-- Uniform large-extra-prime sample cost. The remaining Mangoldt kernel
will have much stronger decay than this subexponential cardinality. -/
theorem mrt_extra_prime_sample_cost :
    ∀ᶠ L : ℝ in atTop, ∀ Y T : ℝ, 1 < Y →
      L^(79/(80:ℝ)) ≤ Real.log Y → Real.log Y ≤ L →
      1 < T → T ≤ Real.exp L →
      mrtShortPrimeSampleCost Y (L^(-100:ℝ)) T (mrtAmplificationOrder Y T) ≤
        Real.exp (L^(3/(100:ℝ))) := by
  let C := |Real.log (432*Real.exp 1)|+436
  have hC : 0 < C := by dsimp [C]; positivity
  have hb := (isLittleO_log_rpow_atTop (show (0:ℝ) < 7/400 by norm_num)).bound
    (show 0 < 1/C by positivity)
  filter_upwards [hb,eventually_ge_atTop (4:ℝ),
    (Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ)))] with L hb hL hLL
  have hL0 : 0 < L := by linarith
  have hlog0 : 0 ≤ Real.log L := by linarith
  rw [Real.norm_eq_abs,abs_of_nonneg hlog0,Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg hL0.le _)] at hb
  have hs : C*Real.log L ≤ L^(7/(400:ℝ)) := by
    have hh := mul_le_mul_of_nonneg_left hb hC.le
    have he : C*((1/C)*L^(7/(400:ℝ)))=L^(7/(400:ℝ)) := by field_simp
    simpa only [he] using hh
  intro Y T hY hYL hYU hT hTU
  exact mrt_extra_sample_cost_pointwise hL hLL hs hY hYL hYU hT hTU

/-- The preceding optimized cost bounds the actual separated large-value
samples of every additional short prime interval. -/
theorem mrt_extra_prime_large_samples :
    ∀ᶠ L : ℝ in atTop, ∀ Y T : ℝ, 1 < Y →
      L^(79/(80:ℝ)) ≤ Real.log Y → Real.log Y ≤ L →
      1 < T → T ≤ Real.exp L →
      ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) →
      (∀ p ∈ P, Y ≤ (p:ℝ) ∧ (p:ℝ) ≤ 2*Y) →
      ∀ F : ℕ → ℂ, OneBounded F → ∀ S : Finset ℝ,
      (∀ t ∈ S, |t| ≤ T) →
      (∀ t ∈ S, ∀ s ∈ S, t≠s → 1 ≤ |t-s|) →
      (∀ t ∈ S, L^(-100:ℝ) ≤ ‖mrtExponentialPolynomial P
        (fun p => F p/(p:ℂ)) (fun p => -Real.log (p:ℝ)) t‖) →
      (S.card:ℝ) ≤ Real.exp (L^(3/(100:ℝ))) := by
  filter_upwards [mrt_extra_prime_sample_cost,eventually_gt_atTop (0:ℝ)] with L hL hL0
  intro Y T hY hYL hYU hT hTU P hP hbin F hF S hS hsep hlarge
  exact (mrt_short_prime_large_samples P hP hY hbin F hF
    (mrtAmplificationOrder Y T) (by linarith) (Real.rpow_pos_of_pos hL0 _)
    S hS hsep hlarge).trans (hL Y T hY hYL hYU hT hTU)

end TwoPointCorrelations

end OAI
