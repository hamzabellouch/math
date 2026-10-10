import Mathlib
import OAI.Probability.SphericalField.Entropy.Distribution

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace SphericalPerceptron
open Matrix
open scoped InnerProductSpace

variable {H : Type*} [SeminormedAddCommGroup H] [InnerProductSpace ℝ H]
def cappedDensity (μ : Measure Time) (B x : ℝ) : ℝ :=
  (max (1 - B) (realTail μ x))⁻¹ ^ 2

def cappedA (μ : Measure Time) (B r : ℝ) : ℝ :=
  ∫ t in 0..r, cappedDensity μ B t

lemma cappedDensity_continuous (μ : Measure Time) [IsProbabilityMeasure μ]
    {B : ℝ} (hB : B < 1) : Continuous (cappedDensity μ B) := by
  unfold cappedDensity
  apply Continuous.pow
  exact (continuous_const.max (realTail_continuous μ)).inv₀ (fun x =>
    ne_of_gt (lt_of_lt_of_le (sub_pos.mpr hB) (le_max_left _ _)))

lemma cappedA_hasDerivAt (μ : Measure Time) [IsProbabilityMeasure μ]
    {B : ℝ} (hB : B < 1) (r : ℝ) :
    HasDerivAt (cappedA μ B) (cappedDensity μ B r) r := by
  have hc := cappedDensity_continuous μ hB
  exact intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable _ _)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt

lemma cappedA_continuous (μ : Measure Time) [IsProbabilityMeasure μ]
    {B : ℝ} (hB : B < 1) : Continuous (cappedA μ B) :=
  continuous_iff_continuousAt.mpr (fun r => (cappedA_hasDerivAt μ hB r).continuousAt)

lemma cappedDensity_eq (μ : Measure Time) [IsProbabilityMeasure μ] {B x : ℝ}
    (hμ : ∀ᵐ s : Time ∂μ, (s : ℝ) ≤ B) (hx : x ≤ B) :
    cappedDensity μ B x = (realTail μ x)⁻¹ ^ 2 := by
  rw [cappedDensity, max_eq_right (realTail_lower μ hμ hx)]

lemma realTail_inv_integral (μ : Measure Time) [IsProbabilityMeasure μ] {B r : ℝ}
    (hB : B < 1) (hμ : ∀ᵐ s : Time ∂μ, (s : ℝ) ≤ B) (hr : 0 ≤ r) (hrB : r ≤ B) :
    (realTail μ r)⁻¹ - (realTail μ 0)⁻¹ =
      ∫ t in 0..r, realCDF μ t * cappedDensity μ B t := by
  have hn (x : ℝ) (hx : x ≤ B) : realTail μ x ≠ 0 :=
    ne_of_gt ((sub_pos.mpr hB).trans_le (realTail_lower μ hμ hx))
  symm
  apply intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le (f := fun x : ℝ => (realTail μ x)⁻¹) hr
  · exact (realTail_continuous μ).continuousOn.inv₀ (fun x hx => hn x (hx.2.trans hrB))
  · intro x hx
    have hd := (realTail_right_derivative μ x).inv (hn x (hx.2.le.trans hrB))
    convert! hd using 1
    simp only [cappedDensity_eq μ hμ (hx.2.le.trans hrB), neg_neg, div_eq_mul_inv, inv_pow]
  · exact (realCDF_integrable μ 0 r).mul_continuousOn
      (cappedDensity_continuous μ hB).continuousOn

def weightedCDF (μ : Measure Time) (a : Time → ℝ) (x : ℝ) : ℝ :=
  ∫ s in {s : Time | (s : ℝ) ≤ x}, a s ∂μ

lemma weightedCDF_fubini (μ : Measure Time) [IsFiniteMeasure μ]
    {a : Time → ℝ} (ha : Integrable a μ) {r : ℝ} (hr : 0 ≤ r) :
    IntervalIntegrable (weightedCDF μ a) volume 0 r ∧
    (∫ t in 0..r, weightedCDF μ a t) = ∫ s : Time, max (r - s) 0 * a s ∂μ := by
  let ν : Measure ℝ := volume.restrict (Icc 0 r)
  have hmeas : MeasurableSet {p : ℝ × Time | (p.2 : ℝ) ≤ p.1} :=
    measurableSet_le (by fun_prop) measurable_fst
  have hbase : Integrable (fun p : ℝ × Time => a p.2) (ν.prod μ) := by
    simpa using (integrable_const (1 : ℝ) (μ := ν)).mul_prod ha
  have hi := hbase.indicator hmeas
  have hleft (t : ℝ) :
      (∫ s : Time, {p : ℝ × Time | (p.2 : ℝ) ≤ p.1}.indicator
        (fun p => a p.2) (t, s) ∂μ) = weightedCDF μ a t := by
    change (∫ s : Time, {s : Time | (s : ℝ) ≤ t}.indicator a s ∂μ) = _
    rw [integral_indicator (measurableSet_le (by fun_prop) measurable_const)]
    rfl
  have hright (s : Time) :
      (∫ t, {p : ℝ × Time | (p.2 : ℝ) ≤ p.1}.indicator
        (fun p => a p.2) (t, s) ∂ν) = max (r - s) 0 * a s := by
    change (∫ t, (Ici (s : ℝ)).indicator (fun _ => a s) t ∂ν) = _
    rw [integral_indicator measurableSet_Ici]
    have hset : Icc 0 r ∩ Ici (s : ℝ) = Icc (s : ℝ) r := by
      ext t
      simp only [mem_inter_iff, mem_Icc, mem_Ici]
      constructor
      · intro h; exact ⟨h.2, h.1.2⟩
      · intro h; exact ⟨⟨s.property.1.trans h.1, h.2⟩, h.1⟩
    dsimp only [ν]
    rw [Measure.restrict_restrict measurableSet_Ici, inter_comm, hset,
      setIntegral_const]
    simp only [Measure.real, Real.volume_Icc, ENNReal.toReal_ofReal', smul_eq_mul]
  have hl : (∫ t, weightedCDF μ a t ∂ν) = ∫ t in 0..r, weightedCDF μ a t := by
    dsimp only [ν]
    rw [integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le hr]
  constructor
  · apply (intervalIntegrable_iff_integrableOn_Icc_of_le hr).mpr
    have hi' : Integrable (weightedCDF μ a) ν := by
      simpa only [Function.uncurry_apply_pair, hleft] using hi.integral_prod_left
    change Integrable (weightedCDF μ a) ν
    exact hi'
  · have hs := integral_integral_swap (μ := ν) (ν := μ)
      (f := fun t s => {p : ℝ × Time | (p.2 : ℝ) ≤ p.1}.indicator (fun p => a p.2) (t,s)) hi
    simpa only [Function.uncurry_apply_pair, hleft, hright, hl] using hs

lemma realTail_inv_formula (μ : Measure Time) [IsProbabilityMeasure μ] {B r : ℝ}
    (hB : B < 1) (hμ : ∀ᵐ s : Time ∂μ, (s : ℝ) ≤ B) (hr : 0 ≤ r) (hrB : r ≤ B) :
    (realTail μ r)⁻¹ - (realTail μ 0)⁻¹ =
      realCDF μ r * cappedA μ B r - weightedCDF μ (fun s => cappedA μ B s) r := by
  rw [realTail_inv_integral μ hB hμ hr hrB,
    integral_cdf_mul μ hr ((cappedDensity_continuous μ hB).intervalIntegrable 0 r)]
  have hm : MeasurableSet {s : Time | (s : ℝ) ≤ r} :=
    measurableSet_le (by fun_prop) measurable_const
  have hA : Integrable (fun s : Time => cappedA μ B s) μ :=
    continuous_time_integrable μ ((cappedA_continuous μ hB).comp continuous_subtype_val)
  have he (s : Time) :
      (if (s : ℝ) ≤ r then ∫ t in (s : ℝ)..r, cappedDensity μ B t else 0) =
      {s : Time | (s : ℝ) ≤ r}.indicator (fun _ => cappedA μ B r) s -
      {s : Time | (s : ℝ) ≤ r}.indicator (fun s => cappedA μ B s) s := by
    by_cases hs : (s : ℝ) ≤ r
    · simp only [hs, ite_true, mem_ofPred_eq, indicator_of_mem]
      have h := intervalIntegral.integral_add_adjacent_intervals
        ((cappedDensity_continuous μ hB).intervalIntegrable (μ := volume) 0 (s : ℝ))
        ((cappedDensity_continuous μ hB).intervalIntegrable (μ := volume) (s : ℝ) r)
      change _ = _ - _
      exact eq_sub_of_add_eq' h
    · simp [hs]
  simp_rw [he]
  rw [integral_sub ((integrable_const _).indicator hm) (hA.indicator hm),
    integral_indicator_const _ hm, integral_indicator hm]
  rfl

@[simp] lemma cappedA_zero (μ : Measure Time) (B : ℝ) : cappedA μ B 0 = 0 := by
  simp [cappedA]

lemma realTail_mul_A (μ : Measure Time) [IsProbabilityMeasure μ] {B r : ℝ}
    (hB : B < 1) (hμ : ∀ᵐ s : Time ∂μ, (s : ℝ) ≤ B) (hr : 0 ≤ r) (hrB : r ≤ B) :
    realTail μ r * cappedA μ B r = r * (realTail μ 0)⁻¹ -
      ∫ s : Time, max (r - s) 0 * cappedA μ B s ∂μ := by
  have hA := cappedA_continuous μ hB
  have hAi : Integrable (fun s : Time => cappedA μ B s) μ :=
    continuous_time_integrable μ (hA.comp continuous_subtype_val)
  have hG := weightedCDF_fubini μ hAi hr
  have hd (x : ℝ) (hx : x ∈ Ioo 0 r) :
      HasDerivWithinAt (fun t => realTail μ t * cappedA μ B t)
        ((realTail μ 0)⁻¹ - weightedCDF μ (fun s => cappedA μ B s) x) (Ioi x) x := by
    have hn : realTail μ x ≠ 0 :=
      ne_of_gt ((sub_pos.mpr hB).trans_le (realTail_lower μ hμ (hx.2.le.trans hrB)))
    have he := realTail_inv_formula μ hB hμ hx.1.le (hx.2.le.trans hrB)
    have hp := (realTail_right_derivative μ x).mul (cappedA_hasDerivAt μ hB x).hasDerivWithinAt
    convert! hp using 1
    rw [cappedDensity_eq μ hμ (hx.2.le.trans hrB)]
    have hm : realTail μ x * ((realTail μ x)⁻¹ ^ 2) = (realTail μ x)⁻¹ := by
      field_simp
    rw [hm]
    linarith
  have h := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le
    (f := fun t => realTail μ t * cappedA μ B t)
    (f' := fun t => (realTail μ 0)⁻¹ - weightedCDF μ (fun s => cappedA μ B s) t)
    hr ((realTail_continuous μ).mul hA).continuousOn hd
    (intervalIntegrable_const.sub hG.1)
  rw [intervalIntegral.integral_sub (f := fun _ => (realTail μ 0)⁻¹)
    intervalIntegrable_const hG.1, hG.2] at h
  simpa using h.symm

lemma realTail_at_top (μ : Measure Time) [IsProbabilityMeasure μ] {B : ℝ}
    (hμ : ∀ᵐ s : Time ∂μ, (s : ℝ) ≤ B) : realTail μ B = 1 - B := by
  calc
    _ = ∫ _ : Time, 1 - B ∂μ := integral_congr_ae (by
      filter_upwards [hμ] with s hs
      rw [max_eq_left hs])
    _ = _ := by simp

lemma realCDF_at_top (μ : Measure Time) [IsProbabilityMeasure μ] {B : ℝ}
    (hμ : ∀ᵐ s : Time ∂μ, (s : ℝ) ≤ B) : realCDF μ B = 1 := by
  unfold realCDF Measure.real
  have h : {s : Time | (s : ℝ) ≤ B} =ᵐ[μ] univ := by
    filter_upwards [hμ] with s hs
    change ((s : ℝ) ≤ B) = True
    simp [hs]
  rw [measure_congr h]
  simp

lemma weightedCDF_at_top (μ : Measure Time) {B : ℝ}
    (hμ : ∀ᵐ s : Time ∂μ, (s : ℝ) ≤ B) (a : Time → ℝ) :
    weightedCDF μ a B = ∫ s, a s ∂μ := by
  unfold weightedCDF
  have h : {s : Time | (s : ℝ) ≤ B} =ᵐ[μ] univ := by
    filter_upwards [hμ] with s hs
    change ((s : ℝ) ≤ B) = True
    simp [hs]
  rw [setIntegral_congr_set h, setIntegral_univ]

lemma realTail_inv_zero_formula (μ : Measure Time) [IsProbabilityMeasure μ] {B : ℝ}
    (hB : B < 1) (hB0 : 0 ≤ B) (hμ : ∀ᵐ s : Time ∂μ, (s : ℝ) ≤ B) :
    (realTail μ 0)⁻¹ = 1 + ∫ s : Time, (1 - (s : ℝ)) * cappedA μ B s ∂μ := by
  have hA : Continuous (fun s : Time => cappedA μ B s) :=
    (cappedA_continuous μ hB).comp continuous_subtype_val
  have hAi := continuous_time_integrable μ hA
  have hSAi : Integrable (fun s : Time => (s : ℝ) * cappedA μ B s) μ :=
    continuous_time_integrable μ (continuous_subtype_val.mul hA)
  have htop := realTail_inv_formula μ hB hμ hB0 le_rfl
  rw [realTail_at_top μ hμ, realCDF_at_top μ hμ, one_mul,
    weightedCDF_at_top μ hμ] at htop
  have hproduct := realTail_mul_A μ hB hμ hB0 le_rfl
  rw [realTail_at_top μ hμ] at hproduct
  have hi : (∫ s : Time, max (B - s) 0 * cappedA μ B s ∂μ) =
      B * (∫ s : Time, cappedA μ B s ∂μ) - ∫ s : Time, (s : ℝ) * cappedA μ B s ∂μ := by
    calc
      _ = ∫ s : Time, B * cappedA μ B s - (s : ℝ) * cappedA μ B s ∂μ :=
        integral_congr_ae (by
          filter_upwards [hμ] with s hs
          rw [max_eq_left (sub_nonneg.mpr hs)]
          ring)
      _ = _ := by rw [integral_sub (hAi.const_mul B) hSAi, integral_const_mul]
  rw [hi] at hproduct
  have hc : (realTail μ 0)⁻¹ = 1 + (∫ s : Time, cappedA μ B s ∂μ) -
      ∫ s : Time, (s : ℝ) * cappedA μ B s ∂μ := by
    have htop' := congrArg (fun z : ℝ => (1 - B) * z) htop
    have hinv : (1 - B) * (1 - B)⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt (sub_pos.mpr hB))
    nlinarith
  rw [hc]
  have hi' : (∫ s : Time, (1 - (s : ℝ)) * cappedA μ B s ∂μ) =
      (∫ s : Time, cappedA μ B s ∂μ) - ∫ s : Time, (s : ℝ) * cappedA μ B s ∂μ := by
    simp_rw [sub_mul, one_mul]
    exact integral_sub hAi hSAi
  rw [hi']
  ring

end SphericalPerceptron
end
end

end OAI
