import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialSpliceDerivative
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul

namespace OAI

/-! A twice differentiable replacement for the squared positive part in core/shell barriers. -/

namespace DefocusingNLS

noncomputable def radialRampInner (δ : ℝ) : ℝ → ℝ :=
  radialSplice δ (fun t => t^3/(3*δ)) (fun t => t^2-δ*t+δ^2/3)

noncomputable def radialRampInnerD (δ : ℝ) : ℝ → ℝ :=
  radialSplice δ (fun t => t^2/δ) (fun t => 2*t-δ)

noncomputable def radialRampInnerDD (δ : ℝ) : ℝ → ℝ :=
  radialSplice δ (fun t => 2*t/δ) (fun _ => 2)

noncomputable def radialSmoothRamp (δ : ℝ) : ℝ → ℝ :=
  radialSplice 0 (fun _ => 0) (radialRampInner δ)

noncomputable def radialSmoothRampD (δ : ℝ) : ℝ → ℝ :=
  radialSplice 0 (fun _ => 0) (radialRampInnerD δ)

noncomputable def radialSmoothRampDD (δ : ℝ) : ℝ → ℝ :=
  radialSplice 0 (fun _ => 0) (radialRampInnerDD δ)

theorem hasDerivAt_radialRampInner (δ : ℝ) (hδ : 0 < δ) (x : ℝ) :
    HasDerivAt (radialRampInner δ) (radialRampInnerD δ x) x := by
  apply hasDerivAt_radialSplice
  · intro t
    convert! ((hasDerivAt_id t).pow 3).div_const (3*δ) using 1
    norm_num
    field_simp
  · intro t
    convert! (((hasDerivAt_id t).pow 2).sub ((hasDerivAt_id t).const_mul δ)).add_const (δ^2/3) using 1
    norm_num
  · field_simp
    ring
  · field_simp
    ring

theorem hasDerivAt_radialRampInnerD (δ : ℝ) (hδ : 0 < δ) (x : ℝ) :
    HasDerivAt (radialRampInnerD δ) (radialRampInnerDD δ x) x := by
  apply hasDerivAt_radialSplice
  · intro t
    convert! ((hasDerivAt_id t).pow 2).div_const δ using 1
    norm_num
  · intro t
    convert! ((hasDerivAt_id t).const_mul 2).sub_const δ using 1
    simp only [mul_one]
  · field_simp
    ring
  · field_simp

theorem hasDerivAt_radialSmoothRamp (δ : ℝ) (hδ : 0 < δ) (x : ℝ) :
    HasDerivAt (radialSmoothRamp δ) (radialSmoothRampD δ x) x := by
  apply hasDerivAt_radialSplice
  · intro t
    exact hasDerivAt_const t 0
  · exact hasDerivAt_radialRampInner δ hδ
  · simp only [radialRampInner,radialSplice,ite_eq_left hδ.le,zero_pow (by omega : (3 : ℕ) ≠ 0),
      zero_div]
  · simp only [radialRampInnerD,radialSplice,ite_eq_left hδ.le,zero_pow (by omega : (2 : ℕ) ≠ 0),
      zero_div]

theorem hasDerivAt_radialSmoothRampD (δ : ℝ) (hδ : 0 < δ) (x : ℝ) :
    HasDerivAt (radialSmoothRampD δ) (radialSmoothRampDD δ x) x := by
  apply hasDerivAt_radialSplice
  · intro t
    exact hasDerivAt_const t 0
  · exact hasDerivAt_radialRampInnerD δ hδ
  · simp only [radialRampInnerD,radialSplice,ite_eq_left hδ.le,zero_pow (by omega : (2 : ℕ) ≠ 0),
      zero_div]
  · simp only [radialRampInnerDD,radialSplice,ite_eq_left hδ.le,mul_zero,zero_div]

end DefocusingNLS

end OAI
