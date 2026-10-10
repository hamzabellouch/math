import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialSquareKernel

namespace OAI

/-! Bootstrap the regular integral equation to all orders through the origin. -/

open scoped ContDiff
open Set
namespace DefocusingNLS

theorem radialSquareProfile_hasDerivWithinAt (k : ℕ) (a b R : ℝ) (hR : 0 < R)
    (Q : ℝ → ℂ) (hQ : Differentiable ℝ Q)
    (hd : ∀ r ∈ Ioc 0 R, deriv Q r=(r : ℂ)*radialComplexAverage k a b Q r)
    (x : ℝ) (hx : x ∈ Icc 0 (R^2)) :
    HasDerivWithinAt (radialSquareProfile Q)
      (radialSquareIntegral k a b (radialSquareProfile Q) x) (Icc 0 (R^2)) x := by
  rw [← radialSquareSlope_eq_integral k a b x hx.1 Q]
  rcases hx.1.eq_or_lt with rfl | hx0
  · have hh := (radialSquareProfile_hasDerivWithinAt_zero k a b R hR Q hQ hd).mono
      (s := Icc 0 (R^2)) Icc_subset_Ici_self
    convert hh using 1
    simp only [radialSquareSlope,Real.sqrt_zero,radialComplexAverage_zero]
    ring
  · exact (radialSquareProfile_hasDerivAt k a b R hR Q hQ hd x ⟨hx0,hx.2⟩).hasDerivWithinAt

theorem radialSquareProfile_contDiffOn (k : ℕ) (a b R : ℝ) (hR : 0 < R)
    (Q : ℝ → ℂ) (hQ : Differentiable ℝ Q)
    (hd : ∀ r ∈ Ioc 0 R, deriv Q r=(r : ℂ)*radialComplexAverage k a b Q r) :
    ContDiffOn ℝ ∞ (radialSquareProfile Q) (Icc 0 (R^2)) := by
  rw [contDiffOn_infty]
  intro n
  induction n with
  | zero =>
    rw [Nat.cast_zero,contDiffOn_zero]
    exact (hQ.continuous.comp Real.continuous_sqrt).continuousOn
  | succ n ih =>
    rw [Nat.cast_succ]
    have hR2 : 0 < R^2 := sq_pos_of_pos hR
    have hU := uniqueDiffOn_Icc hR2
    have hI := radialSquareIntegral_contDiffOn k a b (R^2) hR2 n (radialSquareProfile Q) ih
    apply (contDiffOn_succ_iff_derivWithin hU).2
    refine ⟨fun x hx => (radialSquareProfile_hasDerivWithinAt k a b R hR Q hQ hd x hx).differentiableWithinAt,
      by simp,?_⟩
    apply hI.congr
    intro x hx
    exact (radialSquareProfile_hasDerivWithinAt k a b R hR Q hQ hd x hx).derivWithin (hU x hx)

end DefocusingNLS

end OAI
