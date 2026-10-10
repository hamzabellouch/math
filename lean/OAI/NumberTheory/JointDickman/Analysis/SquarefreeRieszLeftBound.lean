import OAI.NumberTheory.JointDickman.Analysis.RieszContourBounds
import OAI.NumberTheory.JointDickman.Analysis.ZetaContourBounds

namespace OAI

/-! # The left vertical error in the squarefree Riesz contour -/
namespace JointDickman
open Complex Set MeasureTheory

theorem squarefreeRiesz_left_bound {z : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    ∃ A C G : ℝ, A ∈ Ioc 0 (1/2) ∧ 0 < C ∧ 0 < G ∧
      ∀ (δ T L : ℝ) (f : ℂ → ℂ), 0 < δ → δ ≤ 1/4 → 4 ≤ T → δ ≤ A/Real.log T →
      (∀ t ∈ Icc (-T) T, exp (f (1+(((-δ:ℝ):ℂ)+(t:ℂ)*I))) =
        zetaPoleFactor (1+(((-δ:ℝ):ℂ)+(t:ℂ)*I))) →
      ‖VIntegral (fractionalContourIntegrand z (squarefreeRieszKernel z L f)) (-δ) (-T) T‖ ≤
        (5*G*(C/δ)^z*Real.exp (-(L*δ)))*Real.pi := by
  obtain ⟨A,C,hA,hC,hζ⟩ := zeta_left_contour_bound
  obtain ⟨G,hG,hGb⟩ := squarefreeAnalyticFactor_uniform_bound hz hz1 (by norm_num : (1/2:ℝ) < 3/4)
  refine ⟨A,C,G,hA,hC,hG,?_⟩
  intro δ T L f hδ hδ4 hT hδA hf
  apply verticalIntegral_bound_by_cauchy (by linarith : 0 ≤ T) (by positivity)
  intro t ht
  let w : ℂ := ((-δ:ℝ):ℂ)+(t:ℂ)*I
  have hw : w ≠ 0 := by
    intro h
    have hr := congrArg Complex.re h
    simp only [w,add_re,ofReal_re,mul_re,ofReal_im,I_re,I_im,mul_zero,zero_mul,
      sub_zero,add_zero,zero_re] at hr
    linarith
  have hsr : (3/4:ℝ) ≤ (1+w).re := by
    simp only [w,add_re,one_re,ofReal_re,mul_re,ofReal_im,I_re,I_im,mul_zero,
      zero_mul,sub_zero,add_zero]
    linarith
  have hζw : ‖riemannZeta (1+w)‖ ≤ C/δ := by
    have htT : |t| ≤ T := abs_le.mpr ⟨ht.1.le,ht.2⟩
    have h := hζ δ T hδ hδ4 hT hδA t htT
    have heq : (1:ℂ)+w = ((1-δ:ℝ):ℂ)+(t:ℂ)*I := by
      simp only [w,Complex.ofReal_sub,Complex.ofReal_one,Complex.ofReal_neg]
      ring
    rw [heq]
    exact h
  have he := squarefreeRieszKernel_bound (L := L) hz hw (by linarith : (1/2:ℝ) ≤ (1+w).re)
    (hf t ⟨ht.1.le,ht.2⟩) (hGb (1+w) hsr) hζw
  simpa only [w,add_re,ofReal_re,mul_re,ofReal_im,I_re,I_im,mul_zero,zero_mul,
    sub_zero,add_zero,add_im,mul_im,mul_one,zero_add,mul_neg] using he

end JointDickman

end OAI
