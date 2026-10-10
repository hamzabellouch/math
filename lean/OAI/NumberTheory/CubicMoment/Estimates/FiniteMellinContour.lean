import OAI.NumberTheory.CubicMoment.Estimates.MellinContour

namespace OAI

/-! Finite contour displacement with an explicit horizontal-edge error.
Only holomorphy on the finite rectangle is required. -/
noncomputable section
open MeasureTheory Set
namespace CubicFirstMoment

def finiteMellinBox (a b T : ℝ) : Set ℂ := Icc a b ×ℂ Icc (-T) T

theorem finite_mellin_rectangle_identity {a b T : ℝ} (hab : a ≤ b) (hT : 0 ≤ T)
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f (finiteMellinBox a b T)) :
    (∫ x in a..b, f (x-(T:ℂ)*Complex.I))-
      (∫ x in a..b, f (x+(T:ℂ)*Complex.I))+
      Complex.I*(∫ y in -T..T, f (b+(y:ℂ)*Complex.I))-
      Complex.I*(∫ y in -T..T, f (a+(y:ℂ)*Complex.I))=0 := by
  have hd : DifferentiableOn ℂ f (uIcc a b ×ℂ uIcc (-T) T) := by
    simpa only [uIcc_of_le hab,uIcc_of_le (show -T ≤ T by linarith),finiteMellinBox] using hf
  have h := Complex.integral_boundary_rect_eq_zero_of_differentiableOn f
    ((a:ℂ)-(T:ℂ)*Complex.I) ((b:ℂ)+(T:ℂ)*Complex.I)
  simp only [Complex.sub_re,Complex.add_re,Complex.ofReal_re,
    Complex.mul_re,Complex.mul_im,Complex.ofReal_im,Complex.I_re,
    Complex.I_im,Complex.sub_im,Complex.add_im,mul_zero,
    sub_zero,add_zero,zero_sub,mul_one,zero_add] at h
  simpa only [Complex.sub_re,Complex.add_re,Complex.ofReal_re,
    Complex.mul_re,Complex.mul_im,Complex.ofReal_im,Complex.I_re,
    Complex.I_im,Complex.sub_im,Complex.add_im,mul_zero,zero_mul,
    sub_zero,add_zero,zero_sub,mul_one,zero_add,Complex.ofReal_neg,
    neg_mul,add_neg_cancel,sub_self,smul_eq_mul,sub_eq_add_neg] using h hd

theorem finite_mellin_shift_bound {a b T H : ℝ} (hab : a ≤ b) (hT : 0 ≤ T)
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f (finiteMellinBox a b T))
    (hTop : ∀ x ∈ Icc a b, ‖f (x+(T:ℂ)*Complex.I)‖ ≤ H)
    (hBot : ∀ x ∈ Icc a b, ‖f (x-(T:ℂ)*Complex.I)‖ ≤ H) :
    ‖(∫ y in -T..T, f (b+(y:ℂ)*Complex.I))-
      (∫ y in -T..T, f (a+(y:ℂ)*Complex.I))‖ ≤ 2*H*(b-a) := by
  have he := finite_mellin_rectangle_identity hab hT f hf
  have h1 : ‖∫ x in a..b, f (x+(T:ℂ)*Complex.I)‖ ≤ H*(b-a) := by
    calc
      _ ≤ H*|b-a| := intervalIntegral.norm_integral_le_of_norm_le_const (fun x hx =>
        hTop x (by rw [uIoc_of_le hab] at hx; exact ⟨hx.1.le,hx.2⟩))
      _ = _ := by rw [abs_of_nonneg (sub_nonneg.mpr hab)]
  have h2 : ‖∫ x in a..b, f (x-(T:ℂ)*Complex.I)‖ ≤ H*(b-a) := by
    calc
      _ ≤ H*|b-a| := intervalIntegral.norm_integral_le_of_norm_le_const (fun x hx =>
        hBot x (by rw [uIoc_of_le hab] at hx; exact ⟨hx.1.le,hx.2⟩))
      _ = _ := by rw [abs_of_nonneg (sub_nonneg.mpr hab)]
  have hid : Complex.I*((∫ y in -T..T, f (b+(y:ℂ)*Complex.I))-
      (∫ y in -T..T, f (a+(y:ℂ)*Complex.I)))=
      (∫ x in a..b, f (x+(T:ℂ)*Complex.I))-
        (∫ x in a..b, f (x-(T:ℂ)*Complex.I)) := by linear_combination he
  have hn := norm_sub_le (∫ x in a..b, f (x+(T:ℂ)*Complex.I))
    (∫ x in a..b, f (x-(T:ℂ)*Complex.I))
  rw [←hid,norm_mul,Complex.norm_I,one_mul] at hn
  linarith

end CubicFirstMoment

end

end OAI
