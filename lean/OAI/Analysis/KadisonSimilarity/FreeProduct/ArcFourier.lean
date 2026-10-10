import OAI.Analysis.KadisonSimilarity.FreeProduct.HankelBounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

namespace OAI

/-! The centered arc, its exact second moment, and its nonzero Fourier
coefficients, computed using normalized angular Lebesgue integration. -/

noncomputable section
namespace KadisonSimilarity

open MeasureTheory Set

/-- A representative of the centered arc indicator; endpoints have measure zero. -/
def centeredArc (θ x : ℝ) : ℝ :=
  (Ioc (-θ) θ).indicator (fun _ => (1 : ℝ)) x - θ / Real.pi

private theorem intervalIntegrable_indicator_of
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} {a b : ℝ} {s : Set ℝ}
    (hf : IntervalIntegrable f volume a b) (hs : MeasurableSet s) :
    IntervalIntegrable (s.indicator f) volume a b :=
  ⟨hf.1.indicator hs, hf.2.indicator hs⟩

private theorem integral_indicator_subinterval
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (f : ℝ → E) {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    (hac : a ≤ c) (hdb : d ≤ b) :
    (∫ x in a..b, (Ioc c d).indicator f x) = ∫ x in c..d, f x := by
  rw [intervalIntegral.integral_of_le hab, integral_indicator measurableSet_Ioc,
    Measure.restrict_restrict_of_subset, ← intervalIntegral.integral_of_le hcd]
  exact Ioc_subset_Ioc hac hdb

theorem centeredArc_integrable (θ a b : ℝ) :
    IntervalIntegrable (centeredArc θ) volume a b :=
  (intervalIntegrable_indicator_of intervalIntegrable_const measurableSet_Ioc).sub
    intervalIntegrable_const

theorem centeredArc_abs_le_one {θ : ℝ} (hθ : 0 ≤ θ) (hπ : θ ≤ Real.pi) (x : ℝ) :
    |centeredArc θ x| ≤ 1 := by
  have hr : 0 ≤ θ / Real.pi := div_nonneg hθ Real.pi_pos.le
  have hr' : θ / Real.pi ≤ 1 := (div_le_one Real.pi_pos).2 hπ
  by_cases hx : x ∈ Ioc (-θ) θ
  · simp only [centeredArc, indicator_of_mem hx]
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  · simp only [centeredArc, indicator_of_notMem hx, zero_sub, abs_neg]
    rwa [abs_of_nonneg hr]

theorem centeredArc_integral_zero {θ : ℝ} (hθ : 0 ≤ θ) (hπ : θ ≤ Real.pi) :
    (∫ x in -Real.pi..Real.pi, centeredArc θ x) = 0 := by
  simp only [centeredArc]
  rw [intervalIntegral.integral_sub
    (intervalIntegrable_indicator_of intervalIntegrable_const measurableSet_Ioc)
    intervalIntegrable_const,
    integral_indicator_subinterval _ (by linarith [Real.pi_pos]) (by linarith)
      (by linarith) hπ]
  simp only [intervalIntegral.integral_const, smul_eq_mul]
  field_simp
  ring

/-- The normalized second moment is the Bernoulli variance of the arc. -/
theorem centeredArc_second_moment {θ : ℝ} (hθ : 0 ≤ θ) (hπ : θ ≤ Real.pi) :
    (2 * Real.pi)⁻¹ * (∫ x in -Real.pi..Real.pi, centeredArc θ x ^ 2) =
      (θ / Real.pi) * (1 - θ / Real.pi) := by
  have hid : (fun x => centeredArc θ x ^ 2) =
      fun x => (1 - 2 * (θ / Real.pi)) *
        (Ioc (-θ) θ).indicator (fun _ => (1 : ℝ)) x + (θ / Real.pi) ^ 2 := by
    funext x
    by_cases hx : x ∈ Ioc (-θ) θ
    · simp only [centeredArc, indicator_of_mem hx]
      ring
    · simp only [centeredArc, indicator_of_notMem hx]
      ring
  rw [hid, intervalIntegral.integral_add
    ((intervalIntegrable_indicator_of intervalIntegrable_const
      measurableSet_Ioc).const_mul _) intervalIntegrable_const,
    intervalIntegral.integral_const_mul,
    integral_indicator_subinterval _ (by linarith [Real.pi_pos]) (by linarith)
      (by linarith) hπ]
  simp only [intervalIntegral.integral_const, smul_eq_mul]
  field_simp
  ring

theorem centeredArc_second_moment_le {θ : ℝ} (hθ : 0 ≤ θ) (hπ : θ ≤ Real.pi) :
    (2 * Real.pi)⁻¹ * (∫ x in -Real.pi..Real.pi, centeredArc θ x ^ 2) ≤ 4 * θ := by
  rw [centeredArc_second_moment hθ hπ]
  have hratio : θ / Real.pi ≤ 4 * θ := by
    apply (div_le_iff₀ Real.pi_pos).2
    nlinarith [Real.pi_gt_three]
  nlinarith [sq_nonneg (θ / Real.pi)]

/-- Nonzero frequency integration over a symmetric arc. -/
theorem integral_arc_exponential (θ r : ℝ) (hr : r ≠ 0) :
    (∫ x in -θ..θ, Complex.exp ((r * x : ℝ) * Complex.I)) =
      (2 * Real.sin (r * θ) / r : ℝ) := by
  have h := intervalIntegral.integral_comp_mul_left
    (fun x : ℝ => Complex.exp (x * Complex.I)) (a := -θ) (b := θ) hr
  rw [mul_neg, integral_exp_mul_I_eq_sin] at h
  simpa only [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_ofNat,
    Complex.ofReal_inv, Complex.real_smul, div_eq_mul_inv, mul_comm] using h

/-- The normalized angular Fourier transform of the actual centered arc. -/
def arcFourierIntegral (θ : ℝ) (l : ℤ) : ℂ :=
  ((2 * Real.pi)⁻¹ : ℝ) •
    ∫ x in -Real.pi..Real.pi,
      (centeredArc θ x : ℂ) * Complex.exp (((l : ℝ) * x : ℝ) * Complex.I)

@[simp] theorem arcFourierIntegral_zero {θ : ℝ} (hθ : 0 ≤ θ) (hπ : θ ≤ Real.pi) :
    arcFourierIntegral θ 0 = 0 := by
  simp only [arcFourierIntegral, Int.cast_zero, zero_mul, Complex.ofReal_zero,
    Complex.exp_zero, mul_one]
  rw [intervalIntegral.integral_ofReal, centeredArc_integral_zero hθ hπ]
  simp

theorem arcFourierIntegral_ne_zero {θ : ℝ} (hθ : 0 ≤ θ) (hπ : θ ≤ Real.pi)
    (l : ℤ) (hl : l ≠ 0) :
    arcFourierIntegral θ l = (Real.sin (l * θ) / (Real.pi * l) : ℝ) := by
  have hlr : (l : ℝ) ≠ 0 := by exact_mod_cast hl
  let g : ℝ → ℂ := fun x => Complex.exp (((l : ℝ) * x : ℝ) * Complex.I)
  have hg : IntervalIntegrable g volume (-Real.pi) Real.pi := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hid : (fun x => (centeredArc θ x : ℂ) * g x) =
      fun x => (Ioc (-θ) θ).indicator g x - (θ / Real.pi : ℝ) • g x := by
    funext x
    by_cases hx : x ∈ Ioc (-θ) θ <;>
      simp [centeredArc, hx, Complex.real_smul, sub_mul]
  unfold arcFourierIntegral
  change ((2 * Real.pi)⁻¹ : ℝ) • (∫ x in -Real.pi..Real.pi,
    (centeredArc θ x : ℂ) * g x) = _
  have hsg : IntervalIntegrable (fun x => (θ / Real.pi) • g x)
      volume (-Real.pi) Real.pi := hg.smul (θ / Real.pi)
  rw [hid, intervalIntegral.integral_sub
    (intervalIntegrable_indicator_of hg measurableSet_Ioc) hsg,
    intervalIntegral.integral_smul,
    integral_indicator_subinterval _ (by linarith [Real.pi_pos]) (by linarith)
      (by linarith) hπ]
  dsimp [g]
  rw [integral_arc_exponential _ _ hlr, integral_arc_exponential _ _ hlr,
    Real.sin_int_mul_pi]
  simp only [mul_zero, zero_div, Complex.ofReal_zero, sub_zero, ← Complex.ofReal_mul]
  congr 1
  field_simp

/-- The positive entries used in the finite Hankel block are these Fourier coefficients. -/
theorem arcFourierIntegral_eq_arcCoefficient {N : ℕ} (hN : 0 < N)
    {l : ℕ} (hl : 0 < l) :
    arcFourierIntegral (arcWidth N) l = (arcCoefficient N l : ℂ) := by
  rw [arcFourierIntegral_ne_zero (arcWidth_pos hN).le]
  · simp [arcCoefficient]
  · have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have hwidth : arcWidth N ≤ 1 := by
      unfold arcWidth
      apply (div_le_one (by positivity)).2
      linarith
    linarith [Real.pi_gt_three]
  · exact_mod_cast hl.ne'

/-- The real Fourier coefficient, including the centered zero frequency. -/
def realArcFourierCoefficient (θ : ℝ) (l : ℤ) : ℝ :=
  if l = 0 then 0 else Real.sin (l * θ) / (Real.pi * l)

theorem arcFourierIntegral_eq_real {θ : ℝ} (hθ : 0 ≤ θ) (hπ : θ ≤ Real.pi)
    (l : ℤ) : arcFourierIntegral θ l = (realArcFourierCoefficient θ l : ℂ) := by
  by_cases hl : l = 0
  · subst l
    simp [hθ, hπ, realArcFourierCoefficient]
  · rw [arcFourierIntegral_ne_zero hθ hπ l hl, realArcFourierCoefficient, ite_eq_right hl]

theorem realArcFourierCoefficient_pos_index {N : ℕ} {l : ℕ} (hl : 0 < l) :
    realArcFourierCoefficient (arcWidth N) l = arcCoefficient N l := by
  have h : (l : ℤ) ≠ 0 := by exact_mod_cast hl.ne'
  simp only [realArcFourierCoefficient, ite_eq_right h, arcCoefficient, Int.cast_natCast]

end KadisonSimilarity

end

end OAI
