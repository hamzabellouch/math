import OAI.Analysis.LipschitzHilbert.Fourier.LineConjugationDerivative

namespace OAI

/-! Integrating the strong conjugation derivative with a uniform bound. -/
noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace LipschitzHilbert.PacketRepresentation

variable (u : ℝ → ℝ) (hu : LipschitzWith 1 u)
  (hc : ContDiff ℝ ∞ u) (hcompact : HasCompactSupport u)
  (B : ℝ) (hB : 0≤B) (hb : ∀ x, |u x|≤B)

def lineConjugationL2 (m : SchwartzMap ℝ ℂ) (s : ℝ) :
    Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ) :=
  (lineSamplingL2Path u hu s).comp
    ((lineL2Projection m 1 (by norm_num)).comp (lineSamplingInverseL2Path u hu B hB hb s))

theorem lineConjugation_derivative_bound (m : SchwartzMap ℝ ℂ)
    (A : ℝ) (hA : 0≤A) (hm : ∀ r≤3, ∀ eta, |eta|^r*‖iteratedDeriv r m eta‖≤A)
    (t : ℝ) (ht : |t|≤1/2) (f : SchwartzMap ℝ ℂ) :
    ‖(lineSamplingSchwartz u hu hc hcompact t ht
        (lineSchwartzCommutator m (lineSamplingGeneratorSchwartz u hu hc hcompact B hB hb t ht)
          (schwartzDerivative 1 (lineSamplingInverseSchwartz u hu hc hcompact B hB hb t ht f)))).toLp 2 volume‖≤
      8*lineCommutatorNormConstant*A*‖f.toLp 2 volume‖ := by
  let I := lineSamplingInverseSchwartz u hu hc hcompact B hB hb t ht f
  let b := lineSamplingGeneratorSchwartz u hu hc hcompact B hB hb t ht
  let D := lineDerivativeCommutatorL2 m b
  have hD : ‖D‖≤2*lineCommutatorNormConstant*A :=
    lineSamplingGenerator_commutator_bound m A hA hm u hu hc hcompact B hB hb t ht
  have hI : ‖I.toLp 2 volume‖≤2*‖f.toLp 2 volume‖ := by
    have hh := (lineSamplingInverseL2Path u hu B hB hb t).le_opNorm (f.toLp 2 volume)
    have hi := lineSamplingInverseL2Path_bound u hu B hB hb t
    rw [lineSamplingInverseL2Path_onSchwartz u hu hc hcompact B hB hb] at hh
    simpa only [lineSamplingInversePath,dite_eq_left ht,I] using
      hh.trans (mul_le_mul_of_nonneg_right hi (norm_nonneg _))
  have hDc : D (I.toLp 2 volume)=(lineSchwartzCommutator m b (schwartzDerivative 1 I)).toLp 2 volume :=
    lineDerivativeCommutatorL2_onSchwartz m b I A 2 hA hm
      (lineSamplingGeneratorSchwartz_lipschitz u hu hc hcompact B hB hb t ht)
  have hC : lineSamplingL2Path u hu t (D (I.toLp 2 volume))=
      (lineSamplingSchwartz u hu hc hcompact t ht
        (lineSchwartzCommutator m b (schwartzDerivative 1 I))).toLp 2 volume := by
    rw [hDc,lineSamplingL2Path_onSchwartz u hu hc hcompact]
    simp only [lineSamplingPath,dite_eq_left ht]
  change ‖(lineSamplingSchwartz u hu hc hcompact t ht
    (lineSchwartzCommutator m b (schwartzDerivative 1 I))).toLp 2 volume‖≤_
  rw [←hC]
  calc
    _ ≤ 2*‖D (I.toLp 2 volume)‖ :=
      ((lineSamplingL2Path u hu t).le_opNorm _).trans
        (mul_le_mul_of_nonneg_right (lineSamplingL2Path_bound u hu t) (norm_nonneg _))
    _ ≤ 2*((2*lineCommutatorNormConstant*A)*‖I.toLp 2 volume‖) :=
      mul_le_mul_of_nonneg_left ((D.le_opNorm _).trans
        (mul_le_mul_of_nonneg_right hD (norm_nonneg _))) (by norm_num)
    _ ≤ 2*((2*lineCommutatorNormConstant*A)*(2*‖f.toLp 2 volume‖)) := by
      gcongr
      exact mul_nonneg (mul_nonneg (by norm_num) lineCommutatorNormConstant_nonneg) hA
    _ = _ := by ring

include hc hcompact in
theorem lineConjugation_zero (m : SchwartzMap ℝ ℂ) (f : SchwartzMap ℝ ℂ) :
    lineConjugationL2 u hu B hB hb m 0 (f.toLp 2 volume)=
      lineL2Projection m 1 (by norm_num) (f.toLp 2 volume) := by
  have hforward (g : SchwartzMap ℝ ℂ) : lineSamplingPath u hu hc hcompact 0 g=g := by
    ext y
    rw [lineSamplingPath_apply u hu hc hcompact 0 (by norm_num)]
    simp only [lineSampling,zero_mul,sub_zero]
  have hinverse : lineSamplingInversePath u hu hc hcompact B hB hb 0 f=f := by
    ext y
    rw [lineSamplingInversePath_apply u hu hc hcompact B hB hb 0 (by norm_num)]
    have hh := lineSamplingInverse_apply u hu 0 (by norm_num) y
    simpa only [lineSampling,zero_mul,sub_zero] using congrArg f hh
  simp only [lineConjugationL2,ContinuousLinearMap.comp_apply,
    lineSamplingInverseL2Path_onSchwartz u hu hc hcompact B hB hb,hinverse,
    lineL2Projection_onSchwartz,lineSamplingL2Path_onSchwartz u hu hc hcompact,hforward]

include hc hcompact in
theorem lineConjugation_difference_bound (m : SchwartzMap ℝ ℂ)
    (A : ℝ) (hA : 0≤A) (hm : ∀ r≤3, ∀ eta, |eta|^r*‖iteratedDeriv r m eta‖≤A)
    (t : ℝ) (ht : |t|≤1/4) (f : SchwartzMap ℝ ℂ) :
    ‖lineConjugationL2 u hu B hB hb m t (f.toLp 2 volume)-
      lineL2Projection m 1 (by norm_num) (f.toLp 2 volume)‖≤
        8*lineCommutatorNormConstant*A*|t| *‖f.toLp 2 volume‖ := by
  let F := fun s => lineConjugationL2 u hu B hB hb m s (f.toLp 2 volume)
  have hsmall (s : ℝ) (hs : s∈Icc (-(1/4:ℝ)) (1/4)) : |s|<1/2 := by
    have hh := abs_le.mpr hs
    linarith
  have hd (s : ℝ) (hs : s∈Icc (-(1/4:ℝ)) (1/4)) : DifferentiableAt ℝ F s :=
    (lineConjugation_L2_hasDerivAt u hu hc hcompact B hB hb m s (hsmall s hs) f).differentiableAt
  have hbound (s : ℝ) (hs : s∈Icc (-(1/4:ℝ)) (1/4)) :
      ‖deriv F s‖≤8*lineCommutatorNormConstant*A*‖f.toLp 2 volume‖ := by
    have he := (lineConjugation_L2_hasDerivAt u hu hc hcompact B hB hb m s (hsmall s hs) f).deriv
    change deriv F s=_ at he
    rw [he]
    exact lineConjugation_derivative_bound u hu hc hcompact B hB hb m A hA hm s (hsmall s hs).le f
  have hh := Convex.norm_image_sub_le_of_norm_deriv_le hd hbound (convex_Icc _ _)
    (show (0:ℝ)∈Icc (-(1/4:ℝ)) (1/4) by norm_num) (abs_le.mp ht)
  change ‖F t-F 0‖≤_ at hh
  dsimp only [F] at hh
  rw [lineConjugation_zero u hu hc hcompact B hB hb] at hh
  simpa only [sub_zero,Real.norm_eq_abs,mul_assoc,mul_left_comm,mul_comm] using hh

end LipschitzHilbert.PacketRepresentation

end

end OAI
