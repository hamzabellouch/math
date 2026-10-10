import OAI.Analysis.Brenier.Translation

namespace OAI

noncomputable section

open MeasureTheory Set

namespace Problem358

/-- The one-dimensional interpolation estimate, expressed through the two
nonnegative secant errors. This is the analytic assembly step before applying
convexity to produce the errors. -/
theorem slice_interpolation_of_errors
    {f g δ₀ δ₁ : ℝ → ℝ} {a b h L : ℝ}
    (hh : 0 < h) (habh : h ≤ b - a) (_hL : 0 ≤ L)
    (hf : IntervalIntegrable (fun t => (f t) ^ 2) volume a b)
    (hfmeas : AEStronglyMeasurable f volume)
    (hg : IntervalIntegrable (fun t => (g t) ^ 2) volume a b)
    (hδ₀ : IntervalIntegrable (fun t => (δ₀ t) ^ 2) volume a (b - h))
    (hδ₁ : IntervalIntegrable (fun t => (δ₁ t) ^ 2) volume a (b - h))
    (herror₀ : (∫ t in a..b - h, (δ₀ t) ^ 2) ≤ 4 * L ^ 2 * h)
    (herror₁ : (∫ t in a..b - h, (δ₁ t) ^ 2) ≤ 4 * L ^ 2 * h)
    (hdecomp : ∀ t ∈ Icc a (b - h),
      g t = (f (t + h) - f t) / h - δ₀ t + δ₁ t)
    (hbound : ∀ t ∈ Icc a b, |g t| ≤ 2 * L) :
    (∫ t in a..b, (g t) ^ 2) ≤
      12 / h ^ 2 * (∫ t in a..b, (f t) ^ 2) + 28 * L ^ 2 * h := by
  have hab : a ≤ b := by linarith
  have hsmall : a ≤ b - h := by linarith
  have htail : b - h ≤ b := by linarith
  have hgsmall : IntervalIntegrable (fun t => (g t) ^ 2) volume a (b - h) := by
    apply hg.mono_set
    rw [uIcc_of_le hsmall, uIcc_of_le hab]
    exact Icc_subset_Icc le_rfl htail
  have hgtail : IntervalIntegrable (fun t => (g t) ^ 2) volume (b - h) b := by
    apply hg.mono_set
    rw [uIcc_of_le htail, uIcc_of_le hab]
    exact Icc_subset_Icc hsmall le_rfl
  have hq := intervalIntegrable_forwardDifference_sq hh habh hf hfmeas
  have hsum := ((hq.const_mul 3).add (hδ₀.const_mul 3)).add (hδ₁.const_mul 3)
  have hp (t : ℝ) (ht : t ∈ Icc a (b - h)) :
      (g t) ^ 2 ≤ 3 * ((f (t + h) - f t) / h) ^ 2 +
        3 * (δ₀ t) ^ 2 + 3 * (δ₁ t) ^ 2 := by
    rw [hdecomp t ht]
    nlinarith [sq_nonneg ((f (t + h) - f t) / h + δ₀ t),
      sq_nonneg ((f (t + h) - f t) / h - δ₁ t),
      sq_nonneg (δ₀ t + δ₁ t)]
  have hi := intervalIntegral.integral_mono_on hsmall hgsmall hsum hp
  rw [intervalIntegral.integral_add ((hq.const_mul 3).add (hδ₀.const_mul 3))
      (hδ₁.const_mul 3),
    intervalIntegral.integral_add (hq.const_mul 3) (hδ₀.const_mul 3),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul] at hi
  have hqbound := integral_forwardDifference_sq_le hh habh hf hfmeas
  have hinterior : (∫ t in a..b - h, (g t) ^ 2) ≤
      12 / h ^ 2 * (∫ t in a..b, (f t) ^ 2) + 24 * L ^ 2 * h := by
    calc
      _ ≤ 3 * (∫ t in a..b - h, ((f (t + h) - f t) / h) ^ 2) +
        3 * (∫ t in a..b - h, (δ₀ t) ^ 2) +
        3 * (∫ t in a..b - h, (δ₁ t) ^ 2) := hi
      _ ≤ 3 * (4 / h ^ 2 * ∫ t in a..b, (f t) ^ 2) +
        3 * (4 * L ^ 2 * h) + 3 * (4 * L ^ 2 * h) := by linarith
      _ = _ := by ring
  have hboundary : (∫ t in b - h..b, (g t) ^ 2) ≤ 4 * L ^ 2 * h := by
    have hpt (t : ℝ) (ht : t ∈ Icc (b - h) b) : (g t) ^ 2 ≤ 4 * L ^ 2 := by
      have ht' : t ∈ Icc a b := ⟨hsmall.trans ht.1, ht.2⟩
      have hb := abs_le.mp (hbound t ht')
      nlinarith [sq_nonneg (2 * L - g t), mul_nonneg
        (show 0 ≤ 2 * L - g t by linarith) (show 0 ≤ 2 * L + g t by linarith)]
    have hi' := intervalIntegral.integral_mono_on htail hgtail
      (intervalIntegrable_const (c := 4 * L ^ 2)) hpt
    simpa only [intervalIntegral.integral_const, smul_eq_mul, sub_sub_cancel,
      mul_comm h] using hi'
  have heq := intervalIntegral.integral_add_adjacent_intervals hgsmall hgtail
  linarith

/-- On a slice shorter than the finite-difference increment, the uniform
bound alone suffices. -/
theorem slice_interpolation_short
    {f g : ℝ → ℝ} {a b h L : ℝ}
    (hab : a ≤ b) (hh : 0 < h) (hshort : b - a ≤ h)
    (_hf : IntervalIntegrable (fun t => (f t) ^ 2) volume a b)
    (hg : IntervalIntegrable (fun t => (g t) ^ 2) volume a b)
    (hbound : ∀ t ∈ Icc a b, |g t| ≤ 2 * L) :
    (∫ t in a..b, (g t) ^ 2) ≤
      12 / h ^ 2 * (∫ t in a..b, (f t) ^ 2) + 28 * L ^ 2 * h := by
  have hpt (t : ℝ) (ht : t ∈ Icc a b) : (g t) ^ 2 ≤ 4 * L ^ 2 := by
    have hb := abs_le.mp (hbound t ht)
    nlinarith [mul_nonneg (show 0 ≤ 2 * L - g t by linarith)
      (show 0 ≤ 2 * L + g t by linarith)]
  have hi := intervalIntegral.integral_mono_on hab hg
    (intervalIntegrable_const (c := 4 * L ^ 2)) hpt
  simp only [intervalIntegral.integral_const, smul_eq_mul] at hi
  have hfpos : 0 ≤ ∫ t in a..b, (f t) ^ 2 :=
    intervalIntegral.integral_nonneg_of_forall hab (fun t => sq_nonneg (f t))
  have hmain : 0 ≤ 12 / h ^ 2 * (∫ t in a..b, (f t) ^ 2) := by positivity
  have hb := mul_le_mul_of_nonneg_right hshort (by positivity : 0 ≤ 4 * L ^ 2)
  nlinarith [mul_nonneg (sq_nonneg L) hh.le]

/-- A measurable function bounded on a compact interval has integrable square. -/
theorem intervalIntegrable_sq_of_abs_le
    {g : ℝ → ℝ} {a b M : ℝ} (hab : a ≤ b) (_hM : 0 ≤ M)
    (hg : Measurable g) (hbound : ∀ t ∈ Icc a b, |g t| ≤ M) :
    IntervalIntegrable (fun t => (g t) ^ 2) volume a b := by
  apply (intervalIntegrable_const (c := M ^ 2) :
    IntervalIntegrable (fun _ : ℝ => M ^ 2) volume a b).mono_fun
  · exact (hg.pow_const 2).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht
    rw [uIoc_of_le hab] at ht
    have hb := abs_le.mp (hbound t ⟨ht.1.le, ht.2⟩)
    simp only [Real.norm_eq_abs, abs_sq]
    nlinarith [mul_nonneg (show 0 ≤ M - g t by linarith)
      (show 0 ≤ M + g t by linarith)]

/-- One-dimensional convex-gradient interpolation from the precise secant
inequalities. The statement allows every positive increment, including those
longer than the interval. -/
theorem slice_interpolation_of_secant_bounds_ae
    {u₀ u₁ g₀ g₁ : ℝ → ℝ} {a b h L : ℝ}
    (hab : a ≤ b) (hh : 0 < h) (hL : 0 ≤ L)
    (hu₀ : Measurable u₀) (hu₁ : Measurable u₁)
    (hg₀meas : Measurable g₀) (hg₁meas : Measurable g₁)
    (hf : IntervalIntegrable (fun t => (u₀ t - u₁ t) ^ 2) volume a b)
    (hg₀ : IntervalIntegrable g₀ volume a b)
    (hg₁ : IntervalIntegrable g₁ volume a b)
    (hbound₀ : ∀ t ∈ Icc a b, |g₀ t| ≤ L)
    (hbound₁ : ∀ t ∈ Icc a b, |g₁ t| ≤ L)
    (hsecant₀ : ∀ᵐ t ∂volume.restrict (Icc a (b - h)),
      0 ≤ (u₀ (t + h) - u₀ t) / h - g₀ t ∧
      (u₀ (t + h) - u₀ t) / h - g₀ t ≤ g₀ (t + h) - g₀ t)
    (hsecant₁ : ∀ᵐ t ∂volume.restrict (Icc a (b - h)),
      0 ≤ (u₁ (t + h) - u₁ t) / h - g₁ t ∧
      (u₁ (t + h) - u₁ t) / h - g₁ t ≤ g₁ (t + h) - g₁ t) :
    (∫ t in a..b, (g₀ t - g₁ t) ^ 2) ≤
      12 / h ^ 2 * (∫ t in a..b, (u₀ t - u₁ t) ^ 2) + 28 * L ^ 2 * h := by
  have hdiffBound (t : ℝ) (ht : t ∈ Icc a b) : |g₀ t - g₁ t| ≤ 2 * L := by
    have hb₀ := abs_le.mp (hbound₀ t ht)
    have hb₁ := abs_le.mp (hbound₁ t ht)
    apply abs_le.mpr
    constructor <;> linarith
  have hdiffInt : IntervalIntegrable (fun t => (g₀ t - g₁ t) ^ 2) volume a b :=
    intervalIntegrable_sq_of_abs_le hab (by positivity) (hg₀meas.sub hg₁meas) hdiffBound
  by_cases hlong : h ≤ b - a
  · let δ₀ : ℝ → ℝ := fun t => (u₀ (t + h) - u₀ t) / h - g₀ t
    let δ₁ : ℝ → ℝ := fun t => (u₁ (t + h) - u₁ t) / h - g₁ t
    have hδ₀meas : Measurable δ₀ := by dsimp [δ₀]; fun_prop
    have hδ₁meas : Measurable δ₁ := by dsimp [δ₁]; fun_prop
    have hδ₀bound : ∀ᵐ t ∂volume.restrict (Icc a (b - h)),
        0 ≤ δ₀ t ∧ δ₀ t ≤ 2 * L := by
      filter_upwards [hsecant₀, ae_restrict_mem measurableSet_Icc] with t hs ht
      have hb₀ := abs_le.mp (hbound₀ t (by constructor <;> linarith [ht.1, ht.2]))
      have hb₁ := abs_le.mp (hbound₀ (t + h) (by constructor <;> linarith [ht.1, ht.2]))
      dsimp [δ₀]
      exact ⟨hs.1, by linarith⟩
    have hδ₁bound : ∀ᵐ t ∂volume.restrict (Icc a (b - h)),
        0 ≤ δ₁ t ∧ δ₁ t ≤ 2 * L := by
      filter_upwards [hsecant₁, ae_restrict_mem measurableSet_Icc] with t hs ht
      have hb₀ := abs_le.mp (hbound₁ t (by constructor <;> linarith [ht.1, ht.2]))
      have hb₁ := abs_le.mp (hbound₁ (t + h) (by constructor <;> linarith [ht.1, ht.2]))
      dsimp [δ₁]
      exact ⟨hs.1, by linarith⟩
    apply slice_interpolation_of_errors (δ₀ := δ₀) (δ₁ := δ₁) hh hlong hL hf
      (hu₀.sub hu₁).aestronglyMeasurable hdiffInt
      (slice_error_sq_integrable_ae (by linarith) hL hδ₀meas.aestronglyMeasurable.restrict hδ₀bound)
      (slice_error_sq_integrable_ae (by linarith) hL hδ₁meas.aestronglyMeasurable.restrict hδ₁bound)
      (slice_error_sq_le_ae hh.le hlong hL hg₀ hbound₀ hδ₀meas.aestronglyMeasurable.restrict hsecant₀)
      (slice_error_sq_le_ae hh.le hlong hL hg₁ hbound₁ hδ₁meas.aestronglyMeasurable.restrict hsecant₁)
      _ hdiffBound
    intro t _
    dsimp [δ₀, δ₁]
    ring
  · exact slice_interpolation_short hab hh (le_of_not_ge hlong) hf hdiffInt hdiffBound

/-- Pointwise secant bounds are a special case of the almost-everywhere estimate. -/
theorem slice_interpolation_of_secant_bounds
    {u₀ u₁ g₀ g₁ : ℝ → ℝ} {a b h L : ℝ}
    (hab : a ≤ b) (hh : 0 < h) (hL : 0 ≤ L)
    (hu₀ : Measurable u₀) (hu₁ : Measurable u₁)
    (hg₀meas : Measurable g₀) (hg₁meas : Measurable g₁)
    (hf : IntervalIntegrable (fun t => (u₀ t - u₁ t) ^ 2) volume a b)
    (hg₀ : IntervalIntegrable g₀ volume a b)
    (hg₁ : IntervalIntegrable g₁ volume a b)
    (hbound₀ : ∀ t ∈ Icc a b, |g₀ t| ≤ L)
    (hbound₁ : ∀ t ∈ Icc a b, |g₁ t| ≤ L)
    (hsecant₀ : ∀ t ∈ Icc a (b - h),
      0 ≤ (u₀ (t + h) - u₀ t) / h - g₀ t ∧
      (u₀ (t + h) - u₀ t) / h - g₀ t ≤ g₀ (t + h) - g₀ t)
    (hsecant₁ : ∀ t ∈ Icc a (b - h),
      0 ≤ (u₁ (t + h) - u₁ t) / h - g₁ t ∧
      (u₁ (t + h) - u₁ t) / h - g₁ t ≤ g₁ (t + h) - g₁ t) :
    (∫ t in a..b, (g₀ t - g₁ t) ^ 2) ≤
      12 / h ^ 2 * (∫ t in a..b, (u₀ t - u₁ t) ^ 2) + 28 * L ^ 2 * h := by
  apply slice_interpolation_of_secant_bounds_ae hab hh hL hu₀ hu₁ hg₀meas hg₁meas
    hf hg₀ hg₁ hbound₀ hbound₁
  · exact (ae_restrict_mem measurableSet_Icc).mono fun t ht => hsecant₀ t ht
  · exact (ae_restrict_mem measurableSet_Icc).mono fun t ht => hsecant₁ t ht

end Problem358

end

noncomputable section

open MeasureTheory Set
open scoped NNReal

namespace Problem358

/-- The unsquared convex secant sandwich holds off a null set, simultaneously
at the two endpoints of a fixed positive increment. -/
theorem ae_convex_secant_bounds {u : ℝ → ℝ} {L : ℝ≥0}
    (hu : ConvexOn ℝ univ u) (hLip : LipschitzWith L u)
    {h : ℝ} (hh : 0 < h) :
    ∀ᵐ x : ℝ, 0 ≤ (u (x + h) - u x) / h - deriv u x ∧
      (u (x + h) - u x) / h - deriv u x ≤ deriv u (x + h) - deriv u x := by
  have hd : ∀ᵐ x : ℝ, DifferentiableAt ℝ u x := hLip.ae_differentiableAt
  have hshift : ∀ᵐ x : ℝ, DifferentiableAt ℝ u (x + h) :=
    (measurePreserving_add_right volume h).quasiMeasurePreserving.ae hd
  filter_upwards [hd, hshift] with x hx hxh
  have hb := convex_forwardQuotient_bounds hu (mem_univ x) (mem_univ (x + h)) hh
    hx.hasDerivAt hxh.hasDerivAt
  simp only [forwardQuotient] at hb
  constructor <;> linarith

/-- Concrete one-dimensional gradient interpolation for globally convex
Lipschitz potentials. No secant, differentiability, or integrability assumptions
are left as hypotheses. -/
theorem convex_lipschitz_slice_interpolation {u v : ℝ → ℝ} {L : ℝ≥0}
    (hu : ConvexOn ℝ univ u) (hv : ConvexOn ℝ univ v)
    (hLipU : LipschitzWith L u) (hLipV : LipschitzWith L v)
    {a b h : ℝ} (hab : a ≤ b) (hh : 0 < h) :
    (∫ t in a..b, (deriv u t - deriv v t) ^ 2) ≤
      12 / h ^ 2 * (∫ t in a..b, (u t - v t) ^ 2) + 28 * (L : ℝ) ^ 2 * h := by
  apply slice_interpolation_of_secant_bounds_ae hab hh L.coe_nonneg
    hLipU.continuous.measurable hLipV.continuous.measurable
    (measurable_deriv u) (measurable_deriv v)
    (((hLipU.continuous.sub hLipV.continuous).pow 2).intervalIntegrable a b)
    (intervalIntegrable_deriv_of_lipschitz hLipU a b)
    (intervalIntegrable_deriv_of_lipschitz hLipV a b)
  · intro t _
    simpa only [Real.norm_eq_abs] using norm_deriv_le_of_lipschitz (x₀ := t) hLipU
  · intro t _
    simpa only [Real.norm_eq_abs] using norm_deriv_le_of_lipschitz (x₀ := t) hLipV
  · exact ae_restrict_of_ae (ae_convex_secant_bounds hu hLipU hh)
  · exact ae_restrict_of_ae (ae_convex_secant_bounds hv hLipV hh)

end Problem358

end

end OAI
