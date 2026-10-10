import OAI.NumberTheory.JointDickman.Analysis.CharacterRieszKernel
import PrimeNumberTheoremAnd.ResidueCalcOnRectangles

namespace OAI

/-! # A contour shift without a singular term for nonprincipal characters -/
namespace JointDickman
open Complex Set MeasureTheory

theorem characterRieszKernel_finite_shift {q : ℕ} (χ : DirichletCharacter ℂ q)
    {z L δ c T : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1)
    (hδ : 0 < δ) (hδ4 : δ ≤ 1/4) (hc : 0 < c) (hc1 : c ≤ 1/2) (hT : 0 < T)
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f (zetaOpenRectangle δ (2*T))) :
    VIntegral (characterRieszKernel χ z L f) c (-T) T =
      VIntegral (characterRieszKernel χ z L f) (-δ/2) (-T) T +
      HIntegral (characterRieszKernel χ z L f) (-δ/2) c T -
      HIntegral (characterRieszKernel χ z L f) (-δ/2) c (-T) := by
  have has := characterContourSeries_analyticOnNhd χ hz hz1 hδ4 hf
  have hhol : DifferentiableOn ℂ (characterRieszKernel χ z L f)
      (Rectangle (-((δ/2:ℝ):ℂ)-(T:ℂ)*I) ((c:ℂ)+(T:ℂ)*I)) := by
    intro w hw
    have hrect := (mem_Rect (by simpa using (show -(δ/2) ≤ c by linarith))
      (by simpa using (show -T ≤ T by linarith)) w).mp hw
    have hre : -(δ/2) ≤ w.re ∧ w.re ≤ c := by simpa using And.intro hrect.1 hrect.2.1
    have him : -T ≤ w.im ∧ w.im ≤ T := by simpa using hrect.2.2
    have hmem : 1+w ∈ zetaOpenRectangle δ (2*T) := by
      change (1-δ < (1+w).re ∧ (1+w).re < 2) ∧
        (-(2*T) < (1+w).im ∧ (1+w).im < 2*T)
      simp only [add_re, one_re, add_im, one_im, zero_add]
      constructor <;> constructor <;> linarith [hre.1,hre.2,him.1,him.2]
    have hne1 : (1:ℂ)+w ≠ 0 := by
      intro he
      have hh := congrArg Complex.re he
      simp only [add_re, one_re, zero_re] at hh
      linarith [hre.1]
    have hne2 : (2:ℂ)+w ≠ 0 := by
      intro he
      have hh := congrArg Complex.re he
      norm_num at hh
      linarith [hre.1]
    have ha : AnalyticAt ℂ (fun v => characterContourSeries χ z f (1+v)) w :=
      (has (1+w) hmem).comp (analyticAt_const.add analyticAt_id)
    exact ((ha.mul ((analyticAt_const.mul analyticAt_id).cexp)).div
      ((analyticAt_const.add analyticAt_id).mul (analyticAt_const.add analyticAt_id))
      (mul_ne_zero hne1 hne2)).differentiableAt.differentiableWithinAt
  have he := HolomorphicOn.vanishesOnRectangle (U := Rectangle _ _) hhol subset_rfl
  simp only [RectangleIntegral, add_re, sub_re, neg_re, ofReal_re, ofReal_im,
    I_re, I_im, mul_re, mul_im, neg_zero, mul_zero, mul_one, zero_add,
    add_zero, sub_zero, zero_sub, add_im, sub_im, neg_im] at he
  simp only [neg_div] at he ⊢
  linear_combination he

theorem characterNormalizedPerron_finite_shift {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {z L δ c T : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1)
    (hδ : 0 < δ) (hδ4 : δ ≤ 1/4) (hc : 0 < c) (hc1 : c ≤ 1/2) (hT : 0 < T)
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f (zetaOpenRectangle δ (2*T)))
    (hf0 : f (3/2) = primeCharacterLog χ (3/2))
    (he : ∀ s ∈ zetaOpenRectangle δ (2*T), exp (f s) = χ.LFunction s) :
    VIntegral (characterNormalizedPerron χ z L) c (-T) T =
      VIntegral (characterRieszKernel χ z L f) (-δ/2) (-T) T +
      HIntegral (characterRieszKernel χ z L f) (-δ/2) c T -
      HIntegral (characterRieszKernel χ z L f) (-δ/2) c (-T) := by
  rw [←characterRieszKernel_finite_shift χ hz hz1 hδ hδ4 hc hc1 hT hf]
  unfold VIntegral
  congr 1
  apply intervalIntegral.integral_congr
  intro t ht
  have htt : -T ≤ t ∧ t ≤ T := by
    simpa only [uIcc_of_le (by linarith : -T ≤ T), mem_Icc] using ht
  have hmem : 1+((c:ℂ)+(t:ℂ)*I) ∈ zetaOpenRectangle 0 (2*T) := by
    change (1-0 < (1+((c:ℂ)+(t:ℂ)*I)).re ∧ (1+((c:ℂ)+(t:ℂ)*I)).re < 2) ∧
      (-(2*T) < (1+((c:ℂ)+(t:ℂ)*I)).im ∧ (1+((c:ℂ)+(t:ℂ)*I)).im < 2*T)
    simp only [sub_zero, add_re, add_im, one_re, one_im, ofReal_re, ofReal_im,
      mul_re, mul_im, I_re, I_im, mul_zero, mul_one, sub_zero, add_zero, zero_add]
    constructor <;> constructor <;> linarith [htt.1,htt.2]
  unfold characterNormalizedPerron characterRieszKernel
  dsimp only
  rw [characterContourSeries_eq_LSeries χ hz hz1 hδ (by linarith) hf hf0 he hmem]

end JointDickman

end OAI
