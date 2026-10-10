import OAI.MathematicalPhysics.DefocusingNLS.Certificates.HighAngularArc
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

namespace OAI

/-! The two actual pieces of the high-angular contour and their tangent vectors. -/

namespace DefocusingNLS

noncomputable def highArcPoint (Z h t : ℝ) : ℂ :=
  (highArcU (2*t) : ℂ)-Complex.I*(h : ℂ)*(highArcV Z (2*t) : ℂ)
noncomputable def highArcTangent (h t : ℝ) : ℂ :=
  (Real.cos (2*t) : ℂ)-Complex.I*(h*Real.sin (2*t) : ℝ)
noncomputable def highRayPoint (Z h t : ℝ) : ℂ :=
  (highRayU t : ℂ)-Complex.I*(h : ℂ)*(highRayV Z t : ℂ)
noncomputable def highRayTangent (h : ℝ) : ℂ :=
  (99/101 : ℂ)-Complex.I*(h*(20/101) : ℝ)

theorem hasDerivAt_highArcPoint (Z h t : ℝ) :
    HasDerivAt (highArcPoint Z h) (highArcTangent h t) t := by
  have hu : HasDerivAt (fun r : ℝ => highArcU (2*r)) (Real.cos (2*t)) t := by
    convert! ((((hasDerivAt_id t).const_mul 2).sin).div_const 2) using 1
    simp only [id_eq,mul_one]
    ring
  have hv : HasDerivAt (fun r : ℝ => highArcV Z (2*r)) (Real.sin (2*t)) t := by
    convert! (((((hasDerivAt_id t).const_mul 2).cos).const_sub 1).div_const 2).const_add Z using 1
    simp only [id_eq,mul_one]
    ring
  convert! hu.ofReal_comp.sub (hv.ofReal_comp.const_mul (Complex.I*(h : ℂ))) using 1
  simp only [highArcTangent,Complex.ofReal_mul]
  ring

theorem hasDerivAt_highRayPoint (Z h t : ℝ) :
    HasDerivAt (highRayPoint Z h) (highRayTangent h) t := by
  have hu : HasDerivAt highRayU (99/101) t := by
    convert! ((hasDerivAt_id t).const_mul (99/101)).const_add (10/101) using 1
    simp only [mul_one]
  have hv : HasDerivAt (highRayV Z) (20/101) t := by
    convert! ((hasDerivAt_id t).const_mul (20/101)).const_add (Z+1/101) using 1
    simp only [mul_one]
  convert! hu.ofReal_comp.sub (hv.ofReal_comp.const_mul (Complex.I*(h : ℂ))) using 1
  norm_num [highRayTangent,Complex.ofReal_mul]
  ring

theorem highArcTangent_normSq (h t : ℝ) (hh : h=1 ∨ h= -1) :
    Complex.normSq (highArcTangent h t) = 1 := by
  rcases hh with rfl | rfl <;>
    simp only [highArcTangent,Complex.normSq_apply,Complex.sub_re,Complex.sub_im,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
      Complex.I_re,Complex.I_im] <;> nlinarith [Real.sin_sq_add_cos_sq (2*t)]

theorem highRayTangent_normSq (h : ℝ) (hh : h=1 ∨ h= -1) :
    Complex.normSq (highRayTangent h) = 1 := by
  rcases hh with rfl | rfl <;> norm_num [highRayTangent,Complex.normSq_apply]

theorem highContour_join (Z h : ℝ) :
    highArcPoint Z h (highArcAngle/2) = highRayPoint Z h 0 ∧
      highArcTangent h (highArcAngle/2) = highRayTangent h := by
  have hc : Real.cos highArcAngle = 99/101 := Real.cos_arccos (by norm_num) (by norm_num)
  have hs : Real.sin highArcAngle = 20/101 := by
    norm_num [highArcAngle,Real.sin_arccos]
  have ht : 2*(highArcAngle/2)=highArcAngle := by ring
  constructor
  · simp only [highArcPoint,highRayPoint,highArcU,highArcV,highRayU,highRayV,ht,hc,hs]
    push_cast
    ring
  · norm_num [highArcTangent,highRayTangent,ht,hc,hs]

end DefocusingNLS

end OAI
