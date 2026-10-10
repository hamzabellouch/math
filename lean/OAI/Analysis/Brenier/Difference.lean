import Mathlib

namespace OAI

noncomputable section

open MeasureTheory Set

namespace Problem358

/-- Translation of a finite difference controls its squared interval integral
by the squared integral of the original function. -/
theorem forwardDifference_sq_control
    {f : ℝ → ℝ} {a b h : ℝ} (hh : 0 < h) (habh : h ≤ b - a)
    (hf : IntervalIntegrable (fun t => (f t) ^ 2) volume a b)
    (hfmeas : AEStronglyMeasurable f volume) :
    IntervalIntegrable (fun t => ((f (t + h) - f t) / h) ^ 2) volume a (b - h) ∧
    (∫ t in a..b - h, ((f (t + h) - f t) / h) ^ 2) ≤
      4 / h ^ 2 * ∫ t in a..b, (f t) ^ 2 := by
  have hab : a ≤ b := by linarith
  have hsmall : a ≤ b - h := by linarith
  have hleft : a ≤ a + h := by linarith
  have hright : a + h ≤ b := by linarith
  have htail : b - h ≤ b := by linarith
  have hsub {c d : ℝ} (hac : a ≤ c) (hcd : c ≤ d) (hdb : d ≤ b) :
      IntervalIntegrable (fun t => (f t) ^ 2) volume c d := by
    apply hf.mono_set
    rw [uIcc_of_le hcd, uIcc_of_le hab]
    exact Icc_subset_Icc hac hdb
  have hshift : IntervalIntegrable (fun t => (f (t + h)) ^ 2) volume a (b - h) := by
    simpa only [add_sub_cancel_right] using
      (hsub hleft hright le_rfl).comp_add_right h
  have hbase := hsub le_rfl hsmall htail
  have hpoint (t : ℝ) :
      ((f (t + h) - f t) / h) ^ 2 ≤
        (2 / h ^ 2) * ((f (t + h)) ^ 2 + (f t) ^ 2) := by
    rw [div_pow]
    apply (div_le_iff₀ (sq_pos_of_pos hh)).mpr
    field_simp
    nlinarith [sq_nonneg (f (t + h) + f t)]
  have hboundInt := (hshift.add hbase).const_mul (2 / h ^ 2)
  have hmeas : AEStronglyMeasurable
      (fun t => ((f (t + h) - f t) / h) ^ 2) volume := by
    have hs := hfmeas.comp_measurePreserving (measurePreserving_add_right volume h)
    have hd : AEStronglyMeasurable (fun t => (f (t + h) - f t) / h) volume := by
      simpa only [div_eq_mul_inv, Pi.sub_apply, Function.comp_apply] using
        (hs.sub hfmeas).mul_const h⁻¹
    exact hd.fun_pow 2
  have hint : IntervalIntegrable
      (fun t => ((f (t + h) - f t) / h) ^ 2) volume a (b - h) := by
    apply hboundInt.mono_fun' hmeas.restrict
    filter_upwards [] with t
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hpoint t
  refine ⟨hint, ?_⟩
  have hi := intervalIntegral.integral_mono_on hsmall hint hboundInt
    (fun t _ => hpoint t)
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add hshift hbase,
    intervalIntegral.integral_comp_add_right (fun t => (f t) ^ 2) h] at hi
  simp only [sub_add_cancel] at hi
  have hnonneg : 0 ≤ᵐ[volume.restrict (Ioc a b)] (fun t => (f t) ^ 2) :=
    Filter.Eventually.of_forall fun t => sq_nonneg (f t)
  have h₁ := intervalIntegral.integral_mono_interval hleft hright le_rfl hnonneg hf
  have h₂ := intervalIntegral.integral_mono_interval le_rfl hsmall htail hnonneg hf
  have hcoef : 0 ≤ 2 / h ^ 2 := by positivity
  have hj := mul_le_mul_of_nonneg_left (add_le_add h₁ h₂) hcoef
  calc
    _ ≤ (2 / h ^ 2) * ((∫ t in a + h..b, (f t) ^ 2) +
      ∫ t in a..b - h, (f t) ^ 2) := hi
    _ ≤ (2 / h ^ 2) * ((∫ t in a..b, (f t) ^ 2) +
      ∫ t in a..b, (f t) ^ 2) := hj
    _ = _ := by ring

/-- Square-integrability of a forward difference quotient on the shortened interval. -/
theorem intervalIntegrable_forwardDifference_sq
    {f : ℝ → ℝ} {a b h : ℝ} (hh : 0 < h) (habh : h ≤ b - a)
    (hf : IntervalIntegrable (fun t => (f t) ^ 2) volume a b)
    (hfmeas : AEStronglyMeasurable f volume) :
    IntervalIntegrable (fun t => ((f (t + h) - f t) / h) ^ 2) volume a (b - h) :=
  (forwardDifference_sq_control hh habh hf hfmeas).1

/-- The squared norm of a forward difference is bounded by four times the
squared norm of the function, divided by the squared increment. -/
theorem integral_forwardDifference_sq_le
    {f : ℝ → ℝ} {a b h : ℝ} (hh : 0 < h) (habh : h ≤ b - a)
    (hf : IntervalIntegrable (fun t => (f t) ^ 2) volume a b)
    (hfmeas : AEStronglyMeasurable f volume) :
    (∫ t in a..b - h, ((f (t + h) - f t) / h) ^ 2) ≤
      4 / h ^ 2 * ∫ t in a..b, (f t) ^ 2 :=
  (forwardDifference_sq_control hh habh hf hfmeas).2

end Problem358

end

/-!
# Pointwise estimates for convex forward difference quotients

These are the pointwise ingredients of the coordinate-slice gradient
interpolation argument.  They do not assert an almost-everywhere derivative
existence result or any of the transport theorems.
-/

noncomputable section

namespace Problem358

/-- Forward difference quotient with step `h`. -/
def forwardQuotient (u : ℝ → ℝ) (h x : ℝ) : ℝ :=
  (u (x + h) - u x) / h

/-- Convexity sandwiches a positive-step quotient between the two endpoint
 derivatives. -/
theorem convex_forwardQuotient_bounds {S : Set ℝ} {u : ℝ → ℝ}
    {x h p q : ℝ} (hu : ConvexOn ℝ S u)
    (hx : x ∈ S) (hxh : x + h ∈ S) (hh : 0 < h)
    (hp : HasDerivAt u p x) (hq : HasDerivAt u q (x + h)) :
    p ≤ forwardQuotient u h x ∧ forwardQuotient u h x ≤ q := by
  have hlt : x < x + h := by linarith
  constructor
  · simpa [forwardQuotient, slope_def_field] using
      hu.le_slope_of_hasDerivAt hx hxh hlt hp
  · simpa [forwardQuotient, slope_def_field] using
      hu.slope_le_of_hasDerivAt hx hxh hlt hq

/-- The nonnegative quotient error is dominated by the derivative increment,
 which is at most twice the derivative bound. -/
theorem convex_forwardQuotient_error_bounds {S : Set ℝ} {u : ℝ → ℝ}
    {x h p q L : ℝ} (hu : ConvexOn ℝ S u)
    (hx : x ∈ S) (hxh : x + h ∈ S) (hh : 0 < h)
    (hp : HasDerivAt u p x) (hq : HasDerivAt u q (x + h))
    (hpL : |p| ≤ L) (hqL : |q| ≤ L) :
    0 ≤ forwardQuotient u h x - p ∧
      forwardQuotient u h x - p ≤ q - p ∧ q - p ≤ 2 * L := by
  obtain ⟨hlo, hhi⟩ := convex_forwardQuotient_bounds hu hx hxh hh hp hq
  obtain ⟨hpLlo, hpLhi⟩ := abs_le.mp hpL
  obtain ⟨hqLlo, hqLhi⟩ := abs_le.mp hqL
  exact ⟨by linarith, by linarith, by linarith⟩

/-- Squared quotient error is controlled by the derivative increment.  This
 is the integrand estimate used before translation cancellation on a slice. -/
theorem convex_forwardQuotient_error_sq_le {S : Set ℝ} {u : ℝ → ℝ}
    {x h p q L : ℝ} (hu : ConvexOn ℝ S u)
    (hx : x ∈ S) (hxh : x + h ∈ S) (hh : 0 < h)
    (hp : HasDerivAt u p x) (hq : HasDerivAt u q (x + h))
    (hpL : |p| ≤ L) (hqL : |q| ≤ L) :
    (forwardQuotient u h x - p) ^ 2 ≤ 2 * L * (q - p) := by
  obtain ⟨he0, heq, hqL'⟩ :=
    convex_forwardQuotient_error_bounds hu hx hxh hh hp hq hpL hqL
  have hL : 0 ≤ L := (abs_nonneg p).trans hpL
  have heL : forwardQuotient u h x - p ≤ 2 * L := heq.trans hqL'
  calc
    (forwardQuotient u h x - p) ^ 2 ≤
        2 * L * (forwardQuotient u h x - p) := by
      nlinarith
    _ ≤ 2 * L * (q - p) := mul_le_mul_of_nonneg_left heq (by positivity)

/-- Forward quotients commute with subtraction. -/
theorem forwardQuotient_sub (u v : ℝ → ℝ) (h x : ℝ) :
    forwardQuotient (fun t => u t - v t) h x =
      forwardQuotient u h x - forwardQuotient v h x := by
  unfold forwardQuotient
  ring

/-- Pointwise decomposition bound for the difference of two derivatives.
 The two last terms are the respective forward quotient errors. -/
theorem derivative_difference_sq_le_quotient_errors
    (u v : ℝ → ℝ) (h x p q : ℝ) :
    (p - q) ^ 2 ≤ 3 *
      ((forwardQuotient (fun t => u t - v t) h x) ^ 2 +
        (forwardQuotient u h x - p) ^ 2 +
        (forwardQuotient v h x - q) ^ 2) := by
  rw [forwardQuotient_sub]
  nlinarith [sq_nonneg (forwardQuotient u h x - forwardQuotient v h x +
      (forwardQuotient u h x - p)),
    sq_nonneg (forwardQuotient u h x - forwardQuotient v h x -
      (forwardQuotient v h x - q)),
    sq_nonneg ((forwardQuotient u h x - p) + (forwardQuotient v h x - q))]

/-- A difference quotient is bounded by the two endpoint function values. -/
theorem forwardQuotient_sq_le (u : ℝ → ℝ) (h x : ℝ) :
    (forwardQuotient u h x) ^ 2 ≤
      2 / h ^ 2 * ((u (x + h)) ^ 2 + (u x) ^ 2) := by
  unfold forwardQuotient
  have hsq : (u (x + h) - u x) ^ 2 ≤
      2 * ((u (x + h)) ^ 2 + (u x) ^ 2) := by
    nlinarith [sq_nonneg (u (x + h) + u x)]
  have := div_le_div_of_nonneg_right hsq (sq_nonneg h)
  rw [div_pow]
  calc
    (u (x + h) - u x) ^ 2 / h ^ 2 ≤
        (2 * ((u (x + h)) ^ 2 + (u x) ^ 2)) / h ^ 2 := this
    _ = _ := by ring

/-- Combined pointwise estimate for two convex functions.  Integrating the
last two derivative increments is the cancellation step of the slice proof. -/
theorem convex_derivative_difference_sq_le {S : Set ℝ} {u v : ℝ → ℝ}
    {x h p₀ p₁ q₀ q₁ L : ℝ}
    (hu : ConvexOn ℝ S u) (hv : ConvexOn ℝ S v)
    (hx : x ∈ S) (hxh : x + h ∈ S) (hh : 0 < h)
    (hp₀ : HasDerivAt u p₀ x) (hq₀ : HasDerivAt u q₀ (x + h))
    (hp₁ : HasDerivAt v p₁ x) (hq₁ : HasDerivAt v q₁ (x + h))
    (hp₀L : |p₀| ≤ L) (hq₀L : |q₀| ≤ L)
    (hp₁L : |p₁| ≤ L) (hq₁L : |q₁| ≤ L) :
    (p₀ - p₁) ^ 2 ≤
      6 / h ^ 2 * ((u (x + h) - v (x + h)) ^ 2 + (u x - v x) ^ 2) +
        6 * L * ((q₀ - p₀) + (q₁ - p₁)) := by
  have he₀ := convex_forwardQuotient_error_sq_le hu hx hxh hh hp₀ hq₀ hp₀L hq₀L
  have he₁ := convex_forwardQuotient_error_sq_le hv hx hxh hh hp₁ hq₁ hp₁L hq₁L
  have hq := forwardQuotient_sq_le (fun t => u t - v t) h x
  calc
    (p₀ - p₁) ^ 2 ≤ 3 *
        ((forwardQuotient (fun t => u t - v t) h x) ^ 2 +
          (forwardQuotient u h x - p₀) ^ 2 +
          (forwardQuotient v h x - p₁) ^ 2) :=
      derivative_difference_sq_le_quotient_errors u v h x p₀ p₁
    _ ≤ 3 * (2 / h ^ 2 *
        ((u (x + h) - v (x + h)) ^ 2 + (u x - v x) ^ 2) +
          2 * L * (q₀ - p₀) + 2 * L * (q₁ - p₁)) := by
      exact mul_le_mul_of_nonneg_left (add_le_add (add_le_add hq he₀) he₁) (by norm_num)
    _ = _ := by ring

end Problem358

open MeasureTheory MeasureTheory.Measure

namespace Problem358

variable {G : Type*} [AddGroup G] [MeasurableSpace G] [MeasurableAdd G]
variable {μ : Measure G} [IsAddRightInvariant μ]

/-- A measurable square-integrable function has a square-integrable translate
difference. -/
theorem integrable_translation_sub_sq (f : G → ℝ) (v : G) (hfm : Measurable f)
    (hf : Integrable (fun x => (f x) ^ 2) μ) :
    Integrable (fun x => (f (x + v) - f x) ^ 2) μ := by
  have hshift : Integrable (fun x => (f (x + v)) ^ 2) μ :=
    (measurePreserving_add_right μ v).integrable_comp_of_integrable hf
  have hu := (hshift.const_mul 2).add (hf.const_mul 2)
  have hm : Measurable (fun x => (f (x + v) - f x) ^ 2) := by fun_prop
  apply hu.mono' hm.aestronglyMeasurable
  exact ae_of_all _ fun x => by
    change ‖(f (x + v) - f x) ^ 2‖ ≤ 2 * (f (x + v)) ^ 2 + 2 * (f x) ^ 2
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    nlinarith [sq_nonneg (f (x + v) + f x)]

/-- Local square-integrability on the common translation domain. -/
theorem integrableOn_translation_sub_sq (K : Set G) (hK : MeasurableSet K)
    (f : G → ℝ) (v : G) (hfm : Measurable f)
    (hf : IntegrableOn (fun x => (f x) ^ 2) K μ) :
    IntegrableOn (fun x => (f (x + v) - f x) ^ 2)
      (K ∩ (fun x => x + v) ⁻¹' K) μ := by
  let g := K.indicator f
  have hg2 : (fun x => (g x) ^ 2) = K.indicator (fun x => (f x) ^ 2) := by
    funext x
    by_cases hx : x ∈ K <;> simp [g, hx]
  have hg : Integrable (fun x => (g x) ^ 2) μ := by
    rw [hg2]
    exact hf.integrable_indicator hK
  have hgi := integrable_translation_sub_sq g v (hfm.indicator hK) hg
  apply hgi.restrict.congr
  filter_upwards [ae_restrict_mem (hK.inter (hK.preimage (measurable_id.add_const v)))] with x hx
  have hx1 : x + v ∈ K := hx.2
  simp [g, hx.1, hx1]

/-- Local square-integrability of the divided finite difference. -/
theorem integrableOn_translation_quotient_sq (K : Set G) (hK : MeasurableSet K)
    (f : G → ℝ) (v : G) (h : ℝ) (hfm : Measurable f)
    (hf : IntegrableOn (fun x => (f x) ^ 2) K μ) :
    IntegrableOn (fun x => ((f (x + v) - f x) / h) ^ 2)
      (K ∩ (fun x => x + v) ⁻¹' K) μ := by
  simpa only [IntegrableOn, div_pow] using (integrableOn_translation_sub_sq K hK f v hfm hf).div_const (h ^ 2)

/-- Translation does not increase the squared `L²` finite difference by more
than four times the original squared norm. No differentiability is required. -/
theorem integral_translation_sub_sq_le (f : G → ℝ) (v : G)
    (hf : Integrable (fun x => (f x) ^ 2) μ) :
    (∫ x, (f (x + v) - f x) ^ 2 ∂μ) ≤ 4 * ∫ x, (f x) ^ 2 ∂μ := by
  have hshift : Integrable (fun x => (f (x + v)) ^ 2) μ :=
    (measurePreserving_add_right μ v).integrable_comp_of_integrable hf
  have hu := (hshift.const_mul 2).add (hf.const_mul 2)
  calc
    (∫ x, (f (x + v) - f x) ^ 2 ∂μ) ≤
        ∫ x, 2 * (f (x + v)) ^ 2 + 2 * (f x) ^ 2 ∂μ := by
      apply integral_mono_of_nonneg (ae_of_all _ fun x => sq_nonneg _) hu
      exact ae_of_all _ fun x => by
        change (f (x + v) - f x) ^ 2 ≤ 2 * (f (x + v)) ^ 2 + 2 * (f x) ^ 2
        nlinarith [sq_nonneg (f (x + v) + f x)]
    _ = 4 * ∫ x, (f x) ^ 2 ∂μ := by
      rw [integral_add (hshift.const_mul 2) (hf.const_mul 2),
        integral_const_mul, integral_const_mul,
        integral_add_right_eq_self (fun x => (f x) ^ 2) v]
      ring

/-- The finite-difference contribution on the set where both endpoints belong
to `K` is controlled by the potential's squared norm on `K`. -/
theorem setIntegral_translation_sub_sq_le (K : Set G) (hK : MeasurableSet K)
    (f : G → ℝ) (v : G) (hf : IntegrableOn (fun x => (f x) ^ 2) K μ) :
    (∫ x in K ∩ (fun x => x + v) ⁻¹' K, (f (x + v) - f x) ^ 2 ∂μ) ≤
      4 * ∫ x in K, (f x) ^ 2 ∂μ := by
  let g := K.indicator f
  have hg2 : (fun x => (g x) ^ 2) = K.indicator (fun x => (f x) ^ 2) := by
    funext x
    by_cases hx : x ∈ K <;> simp [g, hx]
  have hg : Integrable (fun x => (g x) ^ 2) μ := by
    rw [hg2]
    exact hf.integrable_indicator hK
  have hshift : Integrable (fun x => (g (x + v)) ^ 2) μ :=
    (measurePreserving_add_right μ v).integrable_comp_of_integrable hg
  let S := K ∩ (fun x => x + v) ⁻¹' K
  have hS : MeasurableSet S := hK.inter (hK.preimage (measurable_id.add_const v))
  have hu := (hshift.const_mul 2).add (hg.const_mul 2)
  calc
    (∫ x in S, (f (x + v) - f x) ^ 2 ∂μ) ≤
        ∫ x in S, 2 * (g (x + v)) ^ 2 + 2 * (g x) ^ 2 ∂μ := by
      apply integral_mono_of_nonneg (ae_of_all _ fun x => sq_nonneg _) hu.restrict
      filter_upwards [ae_restrict_mem hS] with x hx
      have hx0 : x ∈ K := hx.1
      have hx1 : x + v ∈ K := hx.2
      change (f (x + v) - f x) ^ 2 ≤ 2 * (g (x + v)) ^ 2 + 2 * (g x) ^ 2
      simp only [g, Set.indicator_of_mem hx0, Set.indicator_of_mem hx1]
      nlinarith [sq_nonneg (f (x + v) + f x)]
    _ ≤ ∫ x, 2 * (g (x + v)) ^ 2 + 2 * (g x) ^ 2 ∂μ := by
      exact setIntegral_le_integral hu (ae_of_all _ fun x => by positivity)
    _ = 4 * ∫ x, (g x) ^ 2 ∂μ := by
      rw [integral_add (hshift.const_mul 2) (hg.const_mul 2),
        integral_const_mul, integral_const_mul,
        integral_add_right_eq_self (fun x => (g x) ^ 2) v]
      ring
    _ = 4 * ∫ x in K, (f x) ^ 2 ∂μ := by
      rw [hg2, integral_indicator hK]

/-- The divided finite-difference estimate used in the gradient interpolation
argument. It is valid for every real scale (including the harmless zero case). -/
theorem setIntegral_translation_quotient_sq_le (K : Set G) (hK : MeasurableSet K)
    (f : G → ℝ) (v : G) (h : ℝ)
    (hf : IntegrableOn (fun x => (f x) ^ 2) K μ) :
    (∫ x in K ∩ (fun x => x + v) ⁻¹' K, ((f (x + v) - f x) / h) ^ 2 ∂μ) ≤
      (4 / h ^ 2) * ∫ x in K, (f x) ^ 2 ∂μ := by
  simp_rw [div_pow]
  rw [integral_div]
  calc
    (∫ x in K ∩ (fun x => x + v) ⁻¹' K, (f (x + v) - f x) ^ 2 ∂μ) / h ^ 2 ≤
        (4 * ∫ x in K, (f x) ^ 2 ∂μ) / h ^ 2 :=
      div_le_div_of_nonneg_right (setIntegral_translation_sub_sq_le K hK f v hf) (sq_nonneg h)
    _ = (4 / h ^ 2) * ∫ x in K, (f x) ^ 2 ∂μ := by ring

end Problem358

end

end OAI
