import Mathlib

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff Matrix InnerProductSpace Matrix.Norms.Elementwise
open scoped NNReal ENNReal
open FourierTransform TemperedDistribution
open scoped SchwartzMap BoundedContinuousFunction
open Function ContinuousLinearMap
open scoped Convolution
open Matrix
open scoped RealInnerProductSpace

namespace HarmonicCounterexample

def a : ℝ := 24 / 25

def theta (t : ℝ) : ℝ := Real.smoothTransition (5 * t - 5 / 2)

def sigma (r : ℝ) : ℝ := Real.smoothTransition (2 * r - 5 / 2)

def beta : ℝ → ℝ := deriv sigma

lemma theta_smooth : ContDiff ℝ ∞ theta := by
  exact Real.smoothTransition.contDiff.comp (by fun_prop)

lemma theta_nonneg (t : ℝ) : 0 ≤ theta t := Real.smoothTransition.nonneg _
lemma theta_le_one (t : ℝ) : theta t ≤ 1 := Real.smoothTransition.le_one _

lemma theta_zero {t : ℝ} (ht : t ≤ 1 / 2) : theta t = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  linarith

lemma theta_one {t : ℝ} (ht : 7 / 10 ≤ t) : theta t = 1 := by
  apply Real.smoothTransition.one_of_one_le
  linarith

lemma sigma_smooth : ContDiff ℝ ∞ sigma := by
  exact Real.smoothTransition.contDiff.comp (by fun_prop)

lemma sigma_nonneg (r : ℝ) : 0 ≤ sigma r := Real.smoothTransition.nonneg _
lemma sigma_le_one (r : ℝ) : sigma r ≤ 1 := Real.smoothTransition.le_one _

lemma sigma_zero {r : ℝ} (hr : r ≤ 5 / 4) : sigma r = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  linarith

lemma sigma_one {r : ℝ} (hr : 7 / 4 ≤ r) : sigma r = 1 := by
  apply Real.smoothTransition.one_of_one_le
  linarith

lemma sigma_monotone : Monotone sigma := by
  intro x y hxy
  exact Real.smoothTransition.monotone (by linarith)

lemma beta_smooth : ContDiff ℝ ∞ beta := by
  exact sigma_smooth.deriv'

lemma beta_nonneg (r : ℝ) : 0 ≤ beta r := by
  exact sigma_monotone.deriv_nonneg

lemma beta_zero_left {r : ℝ} (hr : r < 5 / 4) : beta r = 0 := by
  have hd : HasDerivAt sigma 0 r := by
    apply (hasDerivAt_const r (0 : ℝ)).congr_of_eventuallyEq
    filter_upwards [eventually_lt_nhds hr] with x hx
    exact sigma_zero hx.le
  exact hd.deriv

lemma beta_zero_right {r : ℝ} (hr : 7 / 4 < r) : beta r = 0 := by
  have hd : HasDerivAt sigma 0 r := by
    apply (hasDerivAt_const r (1 : ℝ)).congr_of_eventuallyEq
    filter_upwards [lt_mem_nhds hr] with x hx
    exact sigma_one hx.le
  exact hd.deriv

lemma beta_support : Function.support beta ⊆ Icc (5/4) (7/4) := by
  intro r hr
  constructor
  · by_contra h
    exact hr (beta_zero_left (lt_of_not_ge h))
  · by_contra h
    exact hr (beta_zero_right (lt_of_not_ge h))

lemma beta_compactSupport : HasCompactSupport beta :=
  HasCompactSupport.of_support_subset_isCompact isCompact_Icc beta_support

lemma beta_normalization : ∫ r, beta r = (1 : ℝ) := by
  have hs : Function.support beta ⊆ Ioc 1 2 := by
    intro r hr
    have h := beta_support hr
    constructor <;> linarith [h.1, h.2]
  calc
    (∫ r, beta r) = ∫ r in (1 : ℝ)..2, beta r :=
      (intervalIntegral.integral_eq_integral_of_support_subset hs).symm
    _ = sigma 2 - sigma 1 :=
      intervalIntegral.integral_deriv_of_contDiffOn_uIcc
        (sigma_smooth.of_le (by simp)).contDiffOn
    _ = 1 := by rw [sigma_one (by norm_num), sigma_zero (by norm_num)]; norm_num

def tailDensity (J t : ℝ) : ℝ := theta (t / J) * t ^ (-(3 / 2 : ℝ))

def tailMass (J : ℝ) : ℝ := ∫ t in Ioi (J / 2), tailDensity J t

def compactLoss (C J : ℝ) : ℝ := 1 - a - C * tailMass J

def tailPrimitive (J t : ℝ) : ℝ := ∫ v in (0 : ℝ)..t, tailDensity J v

def radialPrimitive (J r : ℝ) : ℝ :=
  if r ≤ 1 then 0 else tailPrimitive J (Real.log r)

def slope (C J r : ℝ) : ℝ :=
  1 - compactLoss C J * sigma r - C * radialPrimitive J r

def warping (C J r : ℝ) : ℝ := ∫ x in (0 : ℝ)..r, slope C J x

def b (C J t : ℝ) : ℝ := Real.exp (-t) * warping C J (Real.exp t)

end HarmonicCounterexample

end

end OAI
