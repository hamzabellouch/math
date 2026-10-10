import Mathlib

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem367

def linearSignalTilt {Ω : Type*} [MeasurableSpace Ω]
    (mu : Measure Ω) (q : Ω → ℝ) (a : ℝ) : Measure Ω :=
  mu.withDensity (fun x => ENNReal.ofReal (1 + a * q x))

theorem linearSignalTilt_density_nonneg {a q : ℝ}
    (ha : |a| ≤ 1) (hq : |q| ≤ 1) : 0 ≤ 1 + a * q := by
  have hab : |a * q| ≤ 1 := by
    rw [abs_mul]
    calc
      |a| * |q| ≤ 1 * |q| := mul_le_mul_of_nonneg_right ha (abs_nonneg q)
      _ ≤ 1 := by simpa using hq
  have := (abs_le.mp hab).1
  linarith

theorem integrable_boundedSignal_mul {Ω : Type*} [MeasurableSpace Ω]
    {mu : Measure Ω} {q f : Ω → ℝ} (hq : Measurable q)
    (hqb : ∀ᵐ x ∂mu, |q x| ≤ 1) (hf : Integrable f mu) :
    Integrable (fun x => q x * f x) mu := by
  refine hf.norm.mono' (hq.aestronglyMeasurable.mul hf.aestronglyMeasurable) ?_
  filter_upwards [hqb] with x hx
  rw [norm_mul, Real.norm_eq_abs]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hx (norm_nonneg (f x))

theorem integrable_linearSignalTilt {Ω : Type*} [MeasurableSpace Ω]
    {mu : Measure Ω} {q f : Ω → ℝ} {a : ℝ} (hq : Measurable q)
    (hqb : ∀ᵐ x ∂mu, |q x| ≤ 1) (ha : |a| ≤ 1) (hf : Integrable f mu) :
    Integrable f (linearSignalTilt mu q a) := by
  rw [linearSignalTilt, integrable_withDensity_iff_integrable_smul'
    (by fun_prop) (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  apply (hf.add ((integrable_boundedSignal_mul hq hqb hf).const_mul a)).congr
  filter_upwards [hqb] with x hx
  rw [ENNReal.toReal_ofReal (linearSignalTilt_density_nonneg ha hx), smul_eq_mul]
  simp only [Pi.add_apply]
  ring

theorem integral_linearSignalTilt {Ω : Type*} [MeasurableSpace Ω]
    {mu : Measure Ω} {q f : Ω → ℝ} {a : ℝ} (hq : Measurable q)
    (hqb : ∀ᵐ x ∂mu, |q x| ≤ 1) (ha : |a| ≤ 1) (hf : Integrable f mu) :
    (∫ x, f x ∂linearSignalTilt mu q a) =
      (∫ x, f x ∂mu) + a * ∫ x, q x * f x ∂mu := by
  rw [linearSignalTilt, integral_withDensity_eq_integral_toReal_smul
    (by fun_prop) (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  have heq : (fun x => (ENNReal.ofReal (1 + a * q x)).toReal • f x) =ᵐ[mu]
      (fun x => f x + a * (q x * f x)) := by
    filter_upwards [hqb] with x hx
    rw [ENNReal.toReal_ofReal (linearSignalTilt_density_nonneg ha hx), smul_eq_mul]
    ring
  rw [integral_congr_ae heq,
    integral_add hf ((integrable_boundedSignal_mul hq hqb hf).const_mul a),
    integral_const_mul]

theorem linearSignalTilt_probability {Ω : Type*} [MeasurableSpace Ω]
    {mu : Measure Ω} [IsProbabilityMeasure mu] {q : Ω → ℝ} {a : ℝ}
    (hq : Measurable q) (hqb : ∀ᵐ x ∂mu, |q x| ≤ 1) (ha : |a| ≤ 1)
    (hmean : (∫ x, q x ∂mu) = 0) : IsProbabilityMeasure (linearSignalTilt mu q a) := by
  have hiq : Integrable q mu := by
    refine (integrable_const (1 : ℝ)).mono' hq.aestronglyMeasurable ?_
    simpa only [Real.norm_eq_abs] using hqb
  have hid : Integrable (fun x => 1 + a * q x) mu := (integrable_const 1).add (hiq.const_mul a)
  have hnonneg : 0 ≤ᵐ[mu] (fun x => 1 + a * q x) :=
    hqb.mono (fun _ hx => linearSignalTilt_density_nonneg ha hx)
  have hint : (∫ x, 1 + a * q x ∂mu) = 1 := by
    rw [integral_add (integrable_const 1) (hiq.const_mul a), integral_const_mul, hmean]
    simp
  constructor
  rw [linearSignalTilt, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hid hnonneg, hint]
  simp

theorem integral_eq_zero_of_ae_sign_reversal {Ω : Type*} [MeasurableSpace Ω]
    {mu : Measure Ω} (T : Ω ≃ᵐ Ω) (hT : MeasurePreserving T mu mu)
    {f : Ω → ℝ} (hf : ∀ᵐ x ∂mu, f (T x) = -f x) : (∫ x, f x ∂mu) = 0 := by
  have h := hT.integral_comp' f
  rw [integral_congr_ae hf, integral_neg] at h
  linarith

theorem integral_eq_zero_of_sign_reversal {Ω : Type*} [MeasurableSpace Ω]
    {mu : Measure Ω} (T : Ω ≃ᵐ Ω) (hT : MeasurePreserving T mu mu)
    {f : Ω → ℝ} (hf : ∀ x, f (T x) = -f x) : (∫ x, f x ∂mu) = 0 := by
  exact integral_eq_zero_of_ae_sign_reversal T hT (Filter.Eventually.of_forall hf)

theorem integral_linearSignalTilt_even {Ω : Type*} [MeasurableSpace Ω]
    {mu : Measure Ω} {q f : Ω → ℝ} {a : ℝ} (hq : Measurable q)
    (hqb : ∀ᵐ x ∂mu, |q x| ≤ 1) (ha : |a| ≤ 1) (hf : Integrable f mu)
    (T : Ω ≃ᵐ Ω) (hT : MeasurePreserving T mu mu)
    (hqodd : ∀ x, q (T x) = -q x) (hfeven : ∀ x, f (T x) = f x) :
    (∫ x, f x ∂linearSignalTilt mu q a) = ∫ x, f x ∂mu := by
  rw [integral_linearSignalTilt hq hqb ha hf]
  have hz : (∫ x, q x * f x ∂mu) = 0 :=
    integral_eq_zero_of_sign_reversal T hT (fun x => by rw [hqodd, hfeven, neg_mul])
  rw [hz]
  ring

theorem integral_linearSignalTilt_ae_even {Ω : Type*} [MeasurableSpace Ω]
    {mu : Measure Ω} {q f : Ω → ℝ} {a : ℝ} (hq : Measurable q)
    (hqb : ∀ᵐ x ∂mu, |q x| ≤ 1) (ha : |a| ≤ 1) (hf : Integrable f mu)
    (T : Ω ≃ᵐ Ω) (hT : MeasurePreserving T mu mu)
    (hqodd : ∀ᵐ x ∂mu, q (T x) = -q x) (hfeven : ∀ᵐ x ∂mu, f (T x) = f x) :
    (∫ x, f x ∂linearSignalTilt mu q a) = ∫ x, f x ∂mu := by
  rw [integral_linearSignalTilt hq hqb ha hf]
  have hz : (∫ x, q x * f x ∂mu) = 0 := by
    apply integral_eq_zero_of_ae_sign_reversal T hT
    filter_upwards [hqodd, hfeven] with x hxq hxf
    rw [hxq, hxf, neg_mul]
  rw [hz]
  ring

theorem map_withDensity_comp {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    {mu : Measure Ω} {f : Ω → X} {w : X → ENNReal}
    (hf : Measurable f) (hw : Measurable w) :
    Measure.map f (mu.withDensity (w ∘ f)) = (Measure.map f mu).withDensity w := by
  ext s hs
  rw [Measure.map_apply hf hs, withDensity_apply _ (hf hs), withDensity_apply _ hs,
    setLIntegral_map hs hw hf]
  rfl

theorem map_linearSignalTilt {Ω : Type*} [MeasurableSpace Ω]
    {mu : Measure Ω} {q : Ω → ℝ} (hq : Measurable q) (a : ℝ) :
    Measure.map q (linearSignalTilt mu q a) = linearSignalTilt (Measure.map q mu) id a := by
  unfold linearSignalTilt
  simpa only [Function.comp_def, id_eq] using
    (map_withDensity_comp (mu := mu) (f := q)
      (w := fun y : ℝ => ENNReal.ofReal (1 + a * y)) hq (by fun_prop))

end Problem367

end

end OAI
