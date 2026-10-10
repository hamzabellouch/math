import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialIntegralRegularity
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialSquareEquation

namespace OAI

/-! Smoothness preservation by the nonsingular squared-radius integral. -/

open Set MeasureTheory
namespace DefocusingNLS

noncomputable def radialSquareKernel (k : ℕ) (a b : ℝ) (q : ℝ → ℂ) (p : ℝ × ℝ) : ℂ :=
  (p.2 : ℂ)^11*Complex.exp (Complex.I*(p.1*(p.2^2-1)/4 : ℝ))*
    radialComplexSource k a b (q (p.1*p.2^2))

noncomputable def radialSquareIntegral (k : ℕ) (a b : ℝ) (q : ℝ → ℂ) (x : ℝ) : ℂ :=
  (∫ t in Icc (0 : ℝ) 1, radialSquareKernel k a b q (x,t))/2

theorem radialSquareKernel_contDiffOn (k : ℕ) (a b R : ℝ) (n : ℕ)
    (q : ℝ → ℂ) (hq : ContDiffOn ℝ n q (Icc 0 R)) :
    ContDiffOn ℝ n (radialSquareKernel k a b q) (Icc 0 R ×ˢ Icc 0 1) := by
  let S : Set (ℝ × ℝ) := Icc 0 R ×ˢ Icc 0 1
  have hm : MapsTo (fun p : ℝ × ℝ => p.1*p.2^2) S (Icc 0 R) := by
    intro p hp
    have ht : p.2^2 ≤ 1 := by nlinarith [hp.2.1,hp.2.2]
    exact ⟨mul_nonneg hp.1.1 (sq_nonneg _),(mul_le_of_le_one_right hp.1.1 ht).trans hp.1.2⟩
  have harg : ContDiffOn ℝ n (fun p : ℝ × ℝ => p.1*p.2^2) S := by fun_prop
  have hqc := hq.comp harg hm
  have hN := ((contDiff_oddPowerNonlinearity k).of_le (show (n : WithTop ℕ∞) ≤ ⊤ from le_top)).comp_contDiffOn hqc
  have hS : ContDiffOn ℝ n (fun p : ℝ × ℝ => radialComplexSource k a b (q (p.1*p.2^2))) S :=
    hN.sub (contDiffOn_const.mul hqc)
  have ht : ContDiffOn ℝ n (fun p : ℝ × ℝ => (p.2 : ℂ)) S :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn contDiff_snd.contDiffOn
  have he0 : ContDiffOn ℝ n (fun p : ℝ × ℝ => p.1*(p.2^2-1)/4) S := by fun_prop
  have he : ContDiffOn ℝ n (fun p : ℝ × ℝ =>
      Complex.exp (Complex.I*(p.1*(p.2^2-1)/4 : ℝ))) S :=
    (contDiffOn_const.mul (Complex.ofRealCLM.contDiff.comp_contDiffOn he0)).cexp
  exact ((ht.pow 11).mul he).mul hS

theorem radialSquareIntegral_contDiffOn (k : ℕ) (a b R : ℝ) (hR : 0 < R) (n : ℕ)
    (q : ℝ → ℂ) (hq : ContDiffOn ℝ n q (Icc 0 R)) :
    ContDiffOn ℝ n (radialSquareIntegral k a b q) (Icc 0 R) :=
  (radial_rectangle_integral_contDiffOn R hR n _ (radialSquareKernel_contDiffOn k a b R n q hq)).div_const 2

theorem radialSquareSlope_eq_integral (k : ℕ) (a b x : ℝ) (hx : 0 ≤ x) (Q : ℝ → ℂ) :
    radialSquareSlope k a b Q x=radialSquareIntegral k a b (radialSquareProfile Q) x := by
  rw [radialSquareSlope_integral k a b x hx Q]
  rw [intervalIntegral.integral_of_le (by norm_num),← integral_Icc_eq_integral_Ioc]
  rfl

end DefocusingNLS

end OAI
