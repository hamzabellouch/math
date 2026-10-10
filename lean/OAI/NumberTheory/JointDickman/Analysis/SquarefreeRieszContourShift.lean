import OAI.NumberTheory.JointDickman.Analysis.SquarefreeRieszContourGeometry
import OAI.NumberTheory.JointDickman.Analysis.SquarefreePerronNormalization

namespace OAI

/-! # Finite contour shift for the actual normalized squarefree Perron integral -/
namespace JointDickman
open Complex Set MeasureTheory

theorem squarefreeRiesz_finite_contour_shift {z L δ c T : ℝ}
    (hz : 0 ≤ z) (hz1 : z < 1) (hδ : 0 < δ) (hδ4 : δ ≤ 1/4)
    (hc : 0 < c) (hcδ : c ≤ δ/4) (hT : 1 < T)
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f (zetaOpenRectangle δ (2*T))) (hf1 : f 1 = 0)
    (he : ∀ s ∈ zetaOpenRectangle δ (2*T), exp (f s) = zetaPoleFactor s) :
    (1/(2*(Real.pi:ℂ)*I))*VIntegral (squarefreeNormalizedPerron z L) c (-T) T =
      (1/(2*(Real.pi:ℂ)*I)) *
        (VIntegral (fractionalContourIntegrand z (squarefreeRieszKernel z L f)) (-δ/4) (-T) T +
         HIntegral (fractionalContourIntegrand z (squarefreeRieszKernel z L f)) (-δ/4) c T -
         HIntegral (fractionalContourIntegrand z (squarefreeRieszKernel z L f)) (-δ/4) c (-T)) +
      (Real.sin (Real.pi*z)/Real.pi) •
        (∫ t : ℝ in Ioc 0 (δ/4), (t^(-z):ℝ) • squarefreeRieszKernel z L f (-(t:ℂ))) := by
  obtain ⟨hrect,hlocal⟩ := squarefreeRieszKernel_contour_regular (L := L)
    hz hz1.le hδ hδ4 hc hcδ hT hf
  have hshift := fractionalContourShift hz hz1 (by linarith : 0 < δ/4) hc hcδ
    (by linarith : 0 < T) (by linarith : 2*(δ/4) < 3*δ/4) hrect hlocal
  have hright : VIntegral (squarefreeNormalizedPerron z L) c (-T) T =
      VIntegral (fractionalContourIntegrand z (squarefreeRieszKernel z L f)) c (-T) T := by
    unfold VIntegral
    congr 1
    apply intervalIntegral.integral_congr
    intro t ht
    have htt : -T ≤ t ∧ t ≤ T := by
      simpa only [uIcc_of_le (by linarith : -T ≤ T),mem_Icc] using ht
    apply squarefreeNormalizedPerron_eq_continuation hz hz1.le hδ (by linarith : 0 < 2*T) hf hf1 he
    change (1-0 < (1+((c:ℂ)+(t:ℂ)*I)).re ∧ (1+((c:ℂ)+(t:ℂ)*I)).re < 2) ∧
      (-(2*T) < (1+((c:ℂ)+(t:ℂ)*I)).im ∧ (1+((c:ℂ)+(t:ℂ)*I)).im < 2*T)
    simp only [sub_zero,add_re,add_im,one_re,one_im,ofReal_re,ofReal_im,mul_re,mul_im,
      I_re,I_im,mul_zero,mul_one,sub_zero,add_zero,zero_add]
    constructor <;> constructor <;> linarith [htt.1,htt.2]
  rw [←hright] at hshift
  simpa only [neg_div] using hshift

end JointDickman

end OAI
