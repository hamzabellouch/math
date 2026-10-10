import Mathlib
import OAI.Probability.LatticeSurface.Dynamics.Tilt

namespace OAI

namespace SmallTilts

open MeasureTheory Set

open scoped ENNReal NNReal

variable {Ω : Type*} [MeasurableSpace Ω]

lemma event_bound (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : Ω → ℝ) (hY : Measurable Y)
    (M : ℝ≥0) (hM : (∫⁻ ω,ENNReal.ofReal (Real.exp (2*|Y ω|)) ∂μ)≤M)
    (s : Set Ω) (hs : MeasurableSet s) :
    tilted μ Y s≤(M:ENNReal)^(3/2:ℝ)*(μ s)^(1/2:ℝ) := by
  have h := (small_linear_tilt μ Y hY M hM).2.2 (s.indicator (fun _ => 1))
    (measurable_const.indicator hs)
  have he (x : Ω) : (s.indicator (fun _ => (1:ENNReal)) x)^2=s.indicator (fun _ => (1:ENNReal)) x := by
    by_cases hx : x∈s <;> simp [hx]
  simpa only [he,lintegral_indicator hs,lintegral_one,Measure.restrict_apply_univ] using h

lemma parameter_transfer (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : Ω → ℝ) (hY : Measurable Y)
    (M : ℝ≥0) (hM : (∫⁻ ω,ENNReal.ofReal (Real.exp (2*|Y ω|)) ∂μ)≤M)
    (q : ℝ≥0) (k : ℕ) (s : Set Ω) (hs : MeasurableSet s) (hP : μ s≤(q:ENNReal)^(2*k)) :
    tilted μ Y s≤(M:ENNReal)^(3/2:ℝ)*(q:ENNReal)^k := by
  refine (event_bound μ Y hY M hM s hs).trans ?_
  calc
    _ ≤ (M:ENNReal)^(3/2:ℝ)*((q:ENNReal)^(2*k))^(1/2:ℝ) := by gcongr
    _ = _ := by rw [← ENNReal.rpow_natCast,← ENNReal.rpow_mul]
                congr 1
                have he : ((2*k:ℕ):ℝ)*(1/2:ℝ)=(k:ℝ) := by push_cast;ring
                rw [he,ENNReal.rpow_natCast]

lemma small_multiple_bound (μ : Measure Ω) (X : Ω → ℝ) (a t : ℝ)
    (ht : 2*|t|≤a) (M : ℝ≥0)
    (hM : (∫⁻ ω,ENNReal.ofReal (Real.exp (a*|X ω|)) ∂μ)≤M) :
    (∫⁻ ω,ENNReal.ofReal (Real.exp (2*|t*X ω|)) ∂μ)≤M := by
  refine (lintegral_mono (fun ω => ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_))).trans hM
  rw [abs_mul,← mul_assoc]
  exact mul_le_mul_of_nonneg_right ht (abs_nonneg _)

lemma power_le_exponential (a : ℝ) (ha : 0<a) (k : ℕ) (x : ℝ) :
    |x|^k≤((k.factorial:ℝ)/a^k)*Real.exp (a*|x|) := by
  have hf : 0<(k.factorial:ℝ) := by positivity
  have he := Real.pow_div_factorial_le_exp (a*|x|) (mul_nonneg ha.le (abs_nonneg x)) k
  rw [div_le_iff₀ hf,mul_pow] at he
  rw [div_mul_eq_mul_div,le_div_iff₀ (pow_pos ha _)]
  nlinarith [he]

lemma exponential_moment_power (μ : Measure Ω) (X : Ω → ℝ) (hX : Measurable X)
    (a : ℝ) (ha : 0<a) (k : ℕ) (M : ℝ≥0)
    (hM : (∫⁻ ω,ENNReal.ofReal (Real.exp (a*|X ω|)) ∂μ)≤M) :
    (∫⁻ ω,ENNReal.ofReal (|X ω|^k) ∂μ)≤ENNReal.ofReal ((k.factorial:ℝ)/a^k)*(M:ENNReal) := by
  calc
    _ ≤ ∫⁻ ω,ENNReal.ofReal (((k.factorial:ℝ)/a^k)*Real.exp (a*|X ω|)) ∂μ :=
      lintegral_mono fun ω => ENNReal.ofReal_le_ofReal (power_le_exponential a ha k (X ω))
    _ = ENNReal.ofReal ((k.factorial:ℝ)/a^k)*(∫⁻ ω,ENNReal.ofReal (Real.exp (a*|X ω|)) ∂μ) := by
      simp only [ENNReal.ofReal_mul (by positivity : 0≤(k.factorial:ℝ)/a^k)]
      exact lintegral_const_mul _ (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (measurable_const.mul hX.abs)))
    _ ≤ _ := by gcongr

lemma tilted_moment_bound (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y X : Ω → ℝ) (hY : Measurable Y) (hX : Measurable X)
    (M N : ℝ≥0) (a : ℝ) (ha : 0<a) (k : ℕ)
    (hM : (∫⁻ ω,ENNReal.ofReal (Real.exp (2*|Y ω|)) ∂μ)≤M)
    (hN : (∫⁻ ω,ENNReal.ofReal (Real.exp (a*|X ω|)) ∂μ)≤N) :
    (∫⁻ ω,ENNReal.ofReal (|X ω|^k) ∂tilted μ Y)≤
      (M:ENNReal)^(3/2:ℝ)*(ENNReal.ofReal (((2*k).factorial:ℝ)/a^(2*k))*(N:ENNReal))^(1/2:ℝ) := by
  have h := (small_linear_tilt μ Y hY M hM).2.2 (fun ω => ENNReal.ofReal (|X ω|^k))
    (ENNReal.measurable_ofReal.comp (hX.abs.pow_const _))
  refine h.trans ?_
  have hp (ω : Ω) : (ENNReal.ofReal (|X ω|^k))^2=ENNReal.ofReal (|X ω|^(2*k)) := by
    rw [← ENNReal.ofReal_pow (by positivity),← pow_mul,Nat.mul_comm]
  simp only [hp]
  gcongr
  exact exponential_moment_power μ X hX a ha (2*k) N hN

end SmallTilts

end OAI
