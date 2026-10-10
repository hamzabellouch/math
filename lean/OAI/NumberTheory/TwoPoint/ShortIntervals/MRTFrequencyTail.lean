import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTShortEnergy
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

namespace OAI

/-! Partial summation of a frequency mean square. This elementary tail
estimate allows the finite-height MRT bounds to be used with the full
fixed-window Fourier kernel. -/

namespace TwoPointCorrelations

open MeasureTheory Set Filter

lemma mrt_symmetric_prefix (F : ℝ → ℝ) (hF : Continuous F) (x : ℝ) :
    (∫ t in (0:ℝ)..x, F t + F (-t)) = ∫ t in -x..x, F t := by
  rw [intervalIntegral.integral_add (hF.intervalIntegrable _ _)
    (show IntervalIntegrable (fun t => F (-t)) volume 0 x from
      (hF.comp continuous_neg).intervalIntegrable _ _), intervalIntegral.integral_comp_neg]
  simp only [neg_zero]
  rw [add_comm]
  exact intervalIntegral.integral_add_adjacent_intervals
    (hF.intervalIntegrable _ _) (hF.intervalIntegrable _ _)

theorem mrt_frequency_tail_finite (F : ℝ → ℝ) (hF : Continuous F)
    (hFn : ∀ t, 0 ≤ F t) {N R U A : ℝ} (hN : 0 < N) (hNR : N ≤ R)
    (hRU : R ≤ U) (hA : 0 ≤ A)
    (hmean : ∀ t, N ≤ t → t ≤ U → (∫ v in -t..t, F v) ≤ A * (t/N+1)) :
    (∫ t in R..U, (F t+F (-t))/t^2) ≤ 4*A/(N*R) := by
  let B : ℝ → ℝ := fun x => ∫ t in (0:ℝ)..x, F t+F (-t)
  have hfc : Continuous (fun t => F t+F (-t)) := hF.add (hF.comp continuous_neg)
  have hB : Continuous B :=
    (intervalIntegral.differentiable_integral_of_continuous hfc).continuous
  have hB' (x : ℝ) : HasDerivAt B (F x+F (-x)) x :=
    intervalIntegral.integral_hasDerivAt_right (hfc.intervalIntegrable _ _)
      hfc.aestronglyMeasurable.stronglyMeasurableAtFilter hfc.continuousAt
  have hR : 0 < R := lt_of_lt_of_le hN hNR
  have hU : 0 < U := lt_of_lt_of_le hR hRU
  have hx0 (x : ℝ) (hx : x ∈ uIcc R U) : 0 < x := by
    rw [uIcc_of_le hRU] at hx
    exact lt_of_lt_of_le hR hx.1
  have hui : ContinuousOn (fun x : ℝ => (x^2)⁻¹) (uIcc R U) :=
    (continuous_id.pow 2).continuousOn.inv₀ (fun x hx => pow_ne_zero 2 (hx0 x hx).ne')
  have hu' : ContinuousOn (fun x : ℝ => -2/x^3) (uIcc R U) :=
    continuousOn_const.div (continuous_id.pow 3).continuousOn
      (fun x hx => pow_ne_zero 3 (hx0 x hx).ne')
  have huid (x : ℝ) (hx : x ∈ Ioo (min R U) (max R U)) :
      HasDerivAt (fun x : ℝ => (x^2)⁻¹) (-2/x^3) x := by
    have hxp : 0 < x := lt_of_lt_of_le hR (by
      simpa only [min_eq_left hRU] using hx.1.le)
    have hd := ((hasDerivAt_id x).pow 2).inv (pow_ne_zero 2 hxp.ne')
    change HasDerivAt (fun y : ℝ => (y^2)⁻¹) (-(2*x^(2-1)*1)/(x^2)^2) x at hd
    convert hd using 1
    field_simp
    ring
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    hui hB.continuousOn huid (fun x _ => hB' x)
    hu'.intervalIntegrable (hfc.intervalIntegrable R U)
  have hBp (x : ℝ) (hx : N ≤ x) (hxU : x ≤ U) : B x ≤ 2*A*x/N := by
    have hbound := hmean x hx hxU
    rw [← mrt_symmetric_prefix F hF x] at hbound
    change B x ≤ A*(x/N+1) at hbound
    have hn : 1 ≤ x/N := (le_div_iff₀ hN).mpr (by simpa using hx)
    have := mul_nonneg hA (sub_nonneg.mpr hn)
    have he : 2*A*x/N = 2*A*(x/N) := by ring
    rw [he]
    nlinarith
  have hBn (x : ℝ) (hx : 0 ≤ x) : 0 ≤ B x :=
    intervalIntegral.integral_nonneg hx (fun t _ => add_nonneg (hFn t) (hFn (-t)))
  have hratio : (∫ t in R..U, 2*B t/t^3) ≤
      (4*A/N) * (R⁻¹-U⁻¹) := by
    have hle := intervalIntegral.integral_mono_on (μ := volume) hRU
      ((hB.continuousOn.const_mul 2).div (continuous_id.pow 3).continuousOn
        (fun x hx => pow_ne_zero 3 (hx0 x hx).ne')).intervalIntegrable
      ((hui.const_mul (4*A/N)).intervalIntegrable) (fun t ht => by
        have htp : 0 < t := lt_of_lt_of_le hR ht.1
        have hBt := hBp t (hNR.trans ht.1) ht.2
        calc
          _ ≤ 2*(2*A*t/N)/t^3 :=
            div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hBt (by norm_num))
              (pow_nonneg htp.le 3)
          _ = _ := by field_simp; ring)
    rw [intervalIntegral.integral_const_mul] at hle
    have hint : (∫ t in R..U, (t^2)⁻¹) = R⁻¹-U⁻¹ := by
      have hh := integral_zpow (a := R) (b := U) (n := (-2:ℤ))
        (Or.inr ⟨by norm_num, notMem_uIcc_of_lt hR hU⟩)
      norm_num at hh
      simpa only [div_neg, div_one, neg_sub] using hh
    rwa [hint] at hle
  have he : (∫ t in R..U, (F t+F (-t))/t^2) =
      B U/U^2-B R/R^2 + ∫ t in R..U, 2*B t/t^3 := by
    convert hparts using 1
    · apply intervalIntegral.integral_congr
      intro t _
      simp only [div_eq_mul_inv]
      ring
    · have hi : (∫ t in R..U, -2/t^3*B t) = -(∫ t in R..U, 2*B t/t^3) := by
        rw [← intervalIntegral.integral_neg]
        apply intervalIntegral.integral_congr
        intro t _
        ring
      rw [hi]
      simp only [div_eq_mul_inv]
      ring
  rw [he]
  have htop : B U/U^2 ≤ 2*A/(N*U) := by
    apply (div_le_div_of_nonneg_right (hBp U (hNR.trans hRU) le_rfl) (sq_nonneg U)).trans_eq
    field_simp
  have hbot : 0 ≤ B R/R^2 := div_nonneg (hBn R hR.le) (sq_nonneg R)
  calc
    _ ≤ 2*A/(N*U) + (4*A/N)*(R⁻¹-U⁻¹) := by linarith
    _ = 4*A/(N*R)-2*A/(N*U) := by ring
    _ ≤ _ := sub_le_self _ (by positivity)

theorem mrt_frequency_tail_infinite (F : ℝ → ℝ) (hF : Continuous F)
    (hFn : ∀ t, 0 ≤ F t) {N R A : ℝ} (hN : 0 < N) (hNR : N ≤ R)
    (hA : 0 ≤ A)
    (hmean : ∀ t, N ≤ t → (∫ v in -t..t, F v) ≤ A*(t/N+1))
    (htail : IntegrableOn (fun t => (F t+F (-t))/t^2) (Ioi R)) :
    (∫ t in Ioi R, (F t+F (-t))/t^2) ≤ 4*A/(N*R) := by
  apply le_of_tendsto
    (intervalIntegral_tendsto_integral_Ioi R htail (tendsto_id :
      Filter.Tendsto (fun U : ℝ => U) Filter.atTop Filter.atTop))
  filter_upwards [Filter.eventually_ge_atTop R] with U hRU
  exact mrt_frequency_tail_finite F hF hFn hN hNR hRU hA
    (fun t ht _ => hmean t ht)

end TwoPointCorrelations

end OAI
