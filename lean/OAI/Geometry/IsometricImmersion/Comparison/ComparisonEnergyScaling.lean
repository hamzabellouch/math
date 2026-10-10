import OAI.Geometry.IsometricImmersion.Comparison.ComparisonSourceBounds
import OAI.Geometry.IsometricImmersion.Comparison.FiniteApproximationJets

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry SmoothLocal.HighEquation

def comparisonLowerSourceCoefficient (A Cfirst Ctest Ccompare Cres E Q a : ℝ)
    (ha : 0 < a) (delta : ℝ) : ℝ :=
  2*A*(testDensityErrorCoefficient Ctest a ha delta+Ccompare*E)+Cfirst*Q+Cres

theorem comparisonSourceBudget_le_leading
    {A Cfirst Ctest Ccompare Cres E Q a delta tau epsilon epsilonQ : ℝ}
    (ha : 0 < a) (N : ℕ) (hA : 0 ≤ A) (hCf : 0 ≤ Cfirst)
    (hCc : 0 ≤ Ccompare) (hCr : 0 ≤ Cres) (ht : 1 ≤ tau)
    (he : epsilon ≤ E*tau/tau^N) (heQ : epsilonQ ≤ Q*tau/tau^N)
    (hlarge : comparisonLowerSourceCoefficient A Cfirst Ctest Ccompare Cres E Q a ha delta ≤ tau) :
    comparisonSourceBudget A Cfirst Ctest Ccompare Cres a ha N delta tau epsilon epsilonQ ≤
      (2*A*pulseLeadingBound a ha+1)*tau^2/tau^N := by
  have ht0 : 0 < tau := zero_lt_one.trans_le ht
  have hp : 0 < tau^N := pow_pos ht0 N
  have hscale : 0 ≤ tau/tau^N := div_nonneg ht0.le hp.le
  have hrem : qForcingRemainderBudget A Cfirst Ctest Ccompare a ha N delta tau epsilon epsilonQ ≤
      (2*A*(testDensityErrorCoefficient Ctest a ha delta+Ccompare*E)+Cfirst*Q)*tau/tau^N := by
    have hb := add_le_add
      (mul_le_mul_of_nonneg_left
        (add_le_add (le_refl (testDensityErrorCoefficient Ctest a ha delta*tau/tau^N))
          (mul_le_mul_of_nonneg_left he hCc))
        (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hA))
      (mul_le_mul_of_nonneg_left heQ hCf)
    change qForcingRemainderBudget A Cfirst Ctest Ccompare a ha N delta tau epsilon epsilonQ ≤ _ at hb
    convert hb using 1
    ring
  have hres : Cres/tau^N ≤ Cres*tau/tau^N := by
    apply div_le_div_of_nonneg_right _ hp.le
    exact le_mul_of_one_le_right hCr ht
  calc
    _ ≤ 2*A*(pulseLeadingBound a ha*tau^2/tau^N)+
        (2*A*(testDensityErrorCoefficient Ctest a ha delta+Ccompare*E)+Cfirst*Q)*tau/tau^N+
        Cres*tau/tau^N := add_le_add (add_le_add le_rfl hrem) hres
    _ = 2*A*(pulseLeadingBound a ha*tau^2/tau^N)+
        comparisonLowerSourceCoefficient A Cfirst Ctest Ccompare Cres E Q a ha delta*(tau/tau^N) := by
      unfold comparisonLowerSourceCoefficient
      ring
    _ ≤ 2*A*(pulseLeadingBound a ha*tau^2/tau^N)+tau*(tau/tau^N) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_right hlarge hscale)
    _ = _ := by ring

theorem approximationAccuracy_le_fixed_power {tau N : ℕ} (ht : 1 ≤ tau) (hN : N ≤ tau) :
    metricApproximationAccuracy tau ≤ 1/(tau : ℝ)^N := by
  have htR : (1 : ℝ) ≤ tau := by exact_mod_cast ht
  unfold metricApproximationAccuracy
  exact one_div_le_one_div_of_le (pow_pos (zero_lt_one.trans_le htR) N)
    (pow_le_pow_right₀ htR hN)

theorem fixed_scaled_approximation_le_source_scale {tau N : ℕ} {E : ℝ}
    (hE : 0 ≤ E) (ht : 1 ≤ tau) (hN : N ≤ tau) :
    E*metricApproximationAccuracy tau ≤ E*(tau : ℝ)/(tau : ℝ)^N := by
  have htR : (1 : ℝ) ≤ tau := by exact_mod_cast ht
  have hp : 0 < (tau : ℝ)^N := pow_pos (zero_lt_one.trans_le htR) N
  calc
    _ ≤ E*(1/(tau : ℝ)^N) := mul_le_mul_of_nonneg_left (approximationAccuracy_le_fixed_power ht hN) hE
    _ = E/(tau : ℝ)^N := by ring
    _ ≤ _ := div_le_div_of_nonneg_right (le_mul_of_one_le_right hE htR) hp.le

theorem comparison_exponential_tendsto_one (Lambda delta : ℝ) :
    Tendsto (fun tau : ℝ => Real.exp (Lambda*(2*delta/tau))) atTop (𝓝 1) := by
  have hzero : Tendsto (fun tau : ℝ => Lambda*(2*delta/tau)) atTop (𝓝 0) := by
    simpa only [id_eq, mul_div_assoc] using
      (tendsto_id.const_div_atTop (Lambda*(2*delta)))
  have he : Tendsto Real.exp (𝓝 (0 : ℝ)) (𝓝 (Real.exp 0)) := Real.continuous_exp.continuousAt.tendsto
  rw [Real.exp_zero] at he
  exact he.comp hzero

theorem comparison_exponential_le_fixed {Lambda delta tau : ℝ}
    (ht : 0 < tau) (hlarge : Lambda*(2*delta) ≤ tau) :
    Real.exp (Lambda*(2*delta/tau)) ≤ Real.exp 1 := by
  apply Real.exp_le_exp.mpr
  rw [← mul_div_assoc]
  exact (div_le_one ht).mpr hlarge

def comparisonGradientConstant (s0 width A a : ℝ) (ha : 0 < a) : ℝ :=
  2*Real.exp 1*Real.sqrt (2*(1+1/s0))*Real.sqrt (2*width)*(2*A*pulseLeadingBound a ha+1)

theorem comparison_gradient_scaling
    {s0 width A a delta tau Lambda F : ℝ} (ha : 0 < a) (N : ℕ)
    (hdelta : 0 ≤ delta) (ht : 0 < tau) (hF : 0 ≤ F)
    (hsource : F ≤ (2*A*pulseLeadingBound a ha+1)*tau^2/tau^N)
    (hexp : Real.exp (Lambda*(2*delta/tau)) ≤ Real.exp 1) :
    Real.sqrt (2*(1+1/s0))*
      (Real.exp (Lambda*(2*delta/tau))*F*Real.sqrt (2*width)*(2*delta/tau)) ≤
      comparisonGradientConstant s0 width A a ha*delta*tau/tau^N := by
  have h1 := mul_le_mul hexp hsource hF (Real.exp_pos 1).le
  have h2 := mul_le_mul_of_nonneg_right h1 (Real.sqrt_nonneg (2*width))
  have h3 := mul_le_mul_of_nonneg_right h2
    (div_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hdelta) ht.le)
  have h4 := mul_le_mul_of_nonneg_left h3 (Real.sqrt_nonneg (2*(1+1/s0)))
  convert h4 using 1
  unfold comparisonGradientConstant
  field_simp [ht.ne']

end SmoothLocal.Pulse

end

end OAI
