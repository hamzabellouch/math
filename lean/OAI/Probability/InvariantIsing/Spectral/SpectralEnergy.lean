import OAI.Probability.InvariantIsing.Spectral.SpectralPrimitive
import OAI.Probability.InvariantIsing.Spectral.SpectralDensityContinuity
import OAI.Probability.InvariantIsing.Spectral.SpectralConvexity
import OAI.Probability.InvariantIsing.Fields.Field
import OAI.Probability.InvariantIsing.Core.TailOrder

namespace OAI

/-! Finite-spectrum interaction energy and its monotonicity. -/

noncomputable section

open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace InvariantIsing

variable {ι : Type*} [Fintype ι]

def finiteSpectralSlope (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) (x : ℝ) : ℝ :=
  ∑ a, eig a * projectedResolventDerivative ρ eig hρ hρsum a x

def finiteThermalScalar (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) (t x : ℝ) : ℝ :=
  x * finiteR ρ eig hρ hρsum (t * x)

def finiteInteractionEnergy (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) (t : ℝ) (p : OverlapPath) : ℝ :=
  spectralFunctional (fun x => finiteSpectralSlope ρ eig hρ hρsum (t * x)) p

theorem continuous_finiteR (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) : Continuous (finiteR ρ eig hρ hρsum) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  rcases lt_trichotomy x 0 with hx | hx | hx
  · have hc : ContinuousAt (fun _ : ℝ => ∑ a, ρ a * eig a) x := continuousAt_const
    apply hc.congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds hx] with y hy
    simp only [finiteR, ite_eq_right (not_lt.mpr (le_of_lt (show y < 0 from hy)))]
  · subst x
    exact continuousAt_finiteR_zero ρ eig hρ hρsum
  · exact (hasStrictDerivAt_finiteR ρ eig hρ hρsum hx).hasDerivAt.continuousAt

theorem continuous_finiteSpectralSlope (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) : Continuous (finiteSpectralSlope ρ eig hρ hρsum) := by
  exact continuous_finsetSum _ fun a _ => continuous_const.mul
    (continuous_projectedResolventDerivative ρ eig hρ hρsum a)

theorem finiteSpectralSlope_zero (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) :
    finiteSpectralSlope ρ eig hρ hρsum 0 = ∑ a, ρ a * eig a := by
  simp only [finiteSpectralSlope, projectedResolventDerivative, lt_self_iff_false, ite_false]
  apply Finset.sum_congr rfl
  intro a _
  ring

theorem finiteSpectralSlope_bounds (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) {l u : ℝ}
    (hl : ∀ a, l ≤ eig a) (hu : ∀ a, eig a ≤ u) (x : ℝ) :
    l ≤ finiteSpectralSlope ρ eig hρ hρsum x ∧ finiteSpectralSlope ρ eig hρ hρsum x ≤ u := by
  have hw := sum_projectedResolventDerivative ρ eig hρ hρsum x
  constructor
  · calc
      l = ∑ a, l * projectedResolventDerivative ρ eig hρ hρsum a x := by
        rw [← Finset.mul_sum, hw, mul_one]
      _ ≤ finiteSpectralSlope ρ eig hρ hρsum x := Finset.sum_le_sum fun a _ =>
        mul_le_mul_of_nonneg_right (hl a)
          (projectedResolventDerivative_pos ρ eig hρ hρsum a x).le
  · calc
      finiteSpectralSlope ρ eig hρ hρsum x ≤
          ∑ a, u * projectedResolventDerivative ρ eig hρ hρsum a x := Finset.sum_le_sum fun a _ =>
        mul_le_mul_of_nonneg_right (hu a)
          (projectedResolventDerivative_pos ρ eig hρ hρsum a x).le
      _ = u := by rw [← Finset.mul_sum, hw, mul_one]

theorem sum_eig_projectedResolvent (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) {x : ℝ} (hx : 0 ≤ x) :
    (∑ a, eig a * projectedResolvent ρ eig hρ hρsum a x) =
      x * finiteR ρ eig hρ hρsum x := by
  rcases hx.eq_or_lt with h | h
  · subst x
    simp only [projectedResolvent, lt_self_iff_false, ite_false, mul_zero,
      Finset.sum_const_zero, zero_mul]
  · let B := finiteInverse ρ eig hρ hρsum x
    have hs := finiteInverse_spec ρ eig hρ hρsum h
    have hterm : ∀ a, eig a * (ρ a / (B - eig a)) = B * (ρ a / (B - eig a)) - ρ a := by
      intro a
      have hgap : B - eig a ≠ 0 := (sub_pos.mpr (hs.1 a)).ne'
      field_simp [hgap]
      ring
    simp only [projectedResolvent, finiteR, ite_eq_left h]
    change (∑ a, eig a * (ρ a / (B - eig a))) = x * (B - 1 / x)
    simp_rw [hterm]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hρsum]
    change B * finiteResolvent ρ eig B - 1 = x * (B - 1 / x)
    rw [hs.2]
    field_simp

theorem hasDerivWithinAt_mul_finiteR_nonneg (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) {x : ℝ} (hx : 0 ≤ x) :
    HasDerivWithinAt (fun y => y * finiteR ρ eig hρ hρsum y)
      (finiteSpectralSlope ρ eig hρ hρsum x) (Ici 0) x := by
  have hd : HasDerivWithinAt
      (fun y => ∑ a, eig a * projectedResolvent ρ eig hρ hρsum a y)
      (finiteSpectralSlope ρ eig hρ hρsum x) (Ici 0) x := by
    convert! HasDerivWithinAt.fun_sum (u := Finset.univ) (fun a _ =>
      (hasDerivWithinAt_projectedResolvent_nonneg ρ eig hρ hρsum a hx).const_mul (eig a)) using 1
  exact hd.congr (fun y hy => (sum_eig_projectedResolvent ρ eig hρ hρsum hy).symm)
    (sum_eig_projectedResolvent ρ eig hρ hρsum hx).symm

theorem finiteSpectralSlope_monotoneOn (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) :
    MonotoneOn (finiteSpectralSlope ρ eig hρ hρsum) (Ici 0) := by
  intro x hx y hy hxy
  let c := y + 1
  have hc : 0 < c := by dsimp [c]; linarith [show 0 ≤ y from hy]
  have hdx : HasDerivWithinAt (fun z => z * finiteR ρ eig hρ hρsum z)
      (finiteSpectralSlope ρ eig hρ hρsum x) (Icc 0 c) x :=
    (hasDerivWithinAt_mul_finiteR_nonneg ρ eig hρ hρsum hx).mono (fun _ hz => hz.1)
  have hdy : HasDerivWithinAt (fun z => z * finiteR ρ eig hρ hρsum z)
      (finiteSpectralSlope ρ eig hρ hρsum y) (Icc 0 c) y :=
    (hasDerivWithinAt_mul_finiteR_nonneg ρ eig hρ hρsum hy).mono (fun _ hz => hz.1)
  have hdiff : DifferentiableOn ℝ (fun z => z * finiteR ρ eig hρ hρsum z) (Icc 0 c) := by
    intro z hz
    exact ((hasDerivWithinAt_mul_finiteR_nonneg ρ eig hρ hρsum hz.1).mono
      (fun _ hu => hu.1)).differentiableWithinAt
  have hmono := (convexOn_mul_finiteR ρ eig hρ hρsum).monotoneOn_derivWithin hdiff
  have hx' : x ∈ Icc 0 c := ⟨hx, by dsimp [c]; linarith⟩
  have hy' : y ∈ Icc 0 c := ⟨hy, by dsimp [c]; linarith⟩
  have h := hmono hx' hy' hxy
  rw [hdx.derivWithin (uniqueDiffOn_Icc hc x hx'),
    hdy.derivWithin (uniqueDiffOn_Icc hc y hy')] at h
  exact h

theorem hasDerivWithinAt_finiteThermalScalar (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) {t x : ℝ} (ht : 0 ≤ t) (hx : 0 ≤ x) :
    HasDerivWithinAt (finiteThermalScalar ρ eig hρ hρsum t)
      (finiteSpectralSlope ρ eig hρ hρsum (t * x)) (Ici 0) x := by
  rcases ht.eq_or_lt with h | h
  · subst t
    rw [zero_mul, finiteSpectralSlope_zero]
    have hd := (hasDerivAt_id x).mul_const (∑ a, ρ a * eig a)
    convert! hd.hasDerivWithinAt using 1
    · funext y
      simp [finiteThermalScalar, finiteR]
    · simp
  · have hdH := hasDerivWithinAt_mul_finiteR_nonneg ρ eig hρ hρsum (mul_nonneg h.le hx)
    have hdlin : HasDerivWithinAt (fun y : ℝ => t * y) t (Ici 0) x := by
      convert! ((hasDerivAt_id x).const_mul t).hasDerivWithinAt using 1
      ring
    have hd := (hdH.comp x hdlin (fun y hy => mul_nonneg h.le hy)).const_mul (1 / t)
    convert! hd using 1
    · funext y
      dsimp [finiteThermalScalar, Function.comp_def]
      field_simp [h.ne']
    · field_simp [h.ne']

theorem finiteInteractionEnergy_mono_deficit (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) {t : ℝ} (ht : 0 ≤ t) (p q : OverlapPath)
    (hD : ∀ r ∈ Icc (0 : ℝ) 1, deficit p r ≤ deficit q r) :
    finiteInteractionEnergy ρ eig hρ hρsum t p ≤ finiteInteractionEnergy ρ eig hρ hρsum t q := by
  have hc : Continuous (fun x => finiteSpectralSlope ρ eig hρ hρsum (t * x)) :=
    (continuous_finiteSpectralSlope ρ eig hρ hρsum).comp (continuous_const.mul continuous_id)
  unfold finiteInteractionEnergy spectralFunctional
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply integral_mono_ae (integrable_spectral_composition _ hc p) (integrable_spectral_composition _ hc q)
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
  have hp := deficit_mem_unit p ⟨hr.1.le, hr.2.le⟩
  have hq := deficit_mem_unit q ⟨hr.1.le, hr.2.le⟩
  exact finiteSpectralSlope_monotoneOn ρ eig hρ hρsum
    (mul_nonneg ht hp.1) (mul_nonneg ht hq.1)
    (mul_le_mul_of_nonneg_left (hD r ⟨hr.1.le, hr.2.le⟩) ht)

/-- The energy comparison in Section 4 follows from the upper-tail order,
including paths with atoms. -/
theorem finiteInteractionEnergy_mono_tail (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) {t : ℝ} (ht : 0 ≤ t) (p q : OverlapPath)
    (htail : ∀ s ∈ Icc (0 : ℝ) 1, pathTail q s ≤ pathTail p s) :
    finiteInteractionEnergy ρ eig hρ hρsum t p ≤ finiteInteractionEnergy ρ eig hρ hρsum t q := by
  exact finiteInteractionEnergy_mono_deficit ρ eig hρ hρsum ht p q
    (fun r _ => deficit_le_of_pathTail_le p q htail r)

theorem abs_finiteInteractionEnergy_le (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) {K : ℝ} (heig : ∀ a, |eig a| ≤ K)
    (t : ℝ) (p : OverlapPath) :
    |finiteInteractionEnergy ρ eig hρ hρsum t p| ≤ K / 2 := by
  have hb : ∀ x, |finiteSpectralSlope ρ eig hρ hρsum x| ≤ K := by
    intro x
    exact abs_le.mpr (finiteSpectralSlope_bounds ρ eig hρ hρsum
      (fun a => (abs_le.mp (heig a)).1) (fun a => (abs_le.mp (heig a)).2) x)
  have hi := norm_integral_le_of_norm_le_const (μ := pathMeasure)
    (f := fun r => finiteSpectralSlope ρ eig hρ hρsum (t * deficit p r))
    (C := K) (ae_of_all _ fun r => by simpa only [Real.norm_eq_abs] using hb (t * deficit p r))
  unfold finiteInteractionEnergy spectralFunctional
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  have hi' : |∫ r, finiteSpectralSlope ρ eig hρ hρsum (t * deficit p r) ∂pathMeasure| ≤ K := by
    simpa only [Real.norm_eq_abs, measureReal_def, pathMeasure_univ, ENNReal.toReal_one, mul_one] using hi
  nlinarith

end InvariantIsing

end

end OAI
