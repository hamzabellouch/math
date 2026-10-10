import OAI.NumberTheory.CubicMoment.Estimates.ArithmeticMellinKernel

namespace OAI

/-! Reflection of the actual Mellin kernel is obtained by conjugating its
original radial weight. This handles the reverse character row without
adding an analytic hypothesis. -/
noncomputable section
open scoped ContDiff FourierTransform SchwartzMap
open MeasureTheory
namespace CubicFirstMoment

lemma star_fourierChar (x : ℝ) :
    star (Real.fourierChar x : ℂ) = (Real.fourierChar (-x) : ℂ) := by
  rw [AddChar.map_neg_eq_inv, Circle.coe_inv_eq_conj]
  rfl

lemma traceFourier_conj (f : ℂ → ℂ) (w : ℂ) :
    traceFourier (fun z => star (f z)) w = star (traceFourier f (-w)) := by
  unfold traceFourier
  calc
    _ = ∫ z : ℂ, star ((Real.fourierChar (-tracePair z (-w)) : ℂ)*f z) := by
      apply integral_congr_ae
      filter_upwards with z
      rw [star_mul,star_fourierChar]
      simp only [tracePair,mul_neg,Complex.neg_re,neg_neg]
      ring
    _ = _ := integral_conj

lemma normProfileFourier_conj (V : ℝ → ℂ) (w : ℂ) :
    normProfileFourier (fun x => star (V x)) w = star (normProfileFourier V w) := by
  unfold normProfileFourier
  rw [traceFourier_conj]
  have he := normProfileFourier_eq_of_normSq_eq V
    (show Complex.normSq (-w) = Complex.normSq w by simp)
  change (2 / Real.sqrt 3 : ℝ) • star (traceFourier (fun z => V (Complex.normSq z)) (-w)) = _
  calc
    _ = star ((2 / Real.sqrt 3 : ℝ) •
        traceFourier (fun z => V (Complex.normSq z)) (-w)) := by
      simp only [star_smul,star_trivial]
    _ = _ := congrArg star he

lemma normDenominatorLogSchwartz_conj (M : ℝ) (hM : 0 < M) (V : ℝ → ℂ)
    (hV : HasCompactSupport V) (hV' : ContDiff ℝ ∞ V)
    (hVc : HasCompactSupport (fun x => star (V x)))
    (hVc' : ContDiff ℝ ∞ (fun x => star (V x))) (ρ u : ℝ) :
    normDenominatorLogSchwartz M hM (fun x => star (V x)) hVc hVc' ρ u =
      star (normDenominatorLogSchwartz M hM V hV hV' ρ u) := by
  simp only [normDenominatorLogSchwartz_apply,wideGramLogKernel,
    normProfileFourier_conj,star_mul,star_smul,star_trivial]
  rw [show star (Real.exp (u/2) : ℂ) = (Real.exp (u/2) : ℂ) from RCLike.conj_ofReal _]
  ring

lemma real_fourier_conj (f : ℝ → ℂ) (t : ℝ) :
    𝓕 (fun x => star (f x)) t = star (𝓕 f (-t)) := by
  rw [Real.fourier_eq,Real.fourier_eq]
  calc
    _ = ∫ x : ℝ, star ((Real.fourierChar (-inner ℝ x (-t)) : ℂ)*f x) := by
      apply integral_congr_ae
      filter_upwards with x
      simp only [Circle.smul_def,smul_eq_mul,star_mul,star_fourierChar,inner_neg_right,
        neg_neg]
      ring
    _ = _ := integral_conj

lemma arithmeticMellinCoefficient_conj (M : ℝ) (hM : 0 < M) (V : ℝ → ℂ)
    (hV : HasCompactSupport V) (hV' : ContDiff ℝ ∞ V)
    (hVc : HasCompactSupport (fun x => star (V x)))
    (hVc' : ContDiff ℝ ∞ (fun x => star (V x))) (ρ t : ℝ) :
    arithmeticMellinCoefficient M hM (fun x => star (V x)) hVc hVc' ρ t =
      star (arithmeticMellinCoefficient M hM V hV hV' ρ (-t)) := by
  unfold arithmeticMellinCoefficient normDenominatorMellinCoefficient
  rw [SchwartzMap.fourier_coe,SchwartzMap.fourier_coe]
  have he : (normDenominatorLogSchwartz M hM (fun x => star (V x)) hVc hVc' ρ : ℝ → ℂ) =
      fun x => star (normDenominatorLogSchwartz M hM V hV hV' ρ x) := by
    funext x
    exact normDenominatorLogSchwartz_conj M hM V hV hV' hVc hVc' ρ x
  rw [he,real_fourier_conj,neg_div]

end CubicFirstMoment

end

end OAI
