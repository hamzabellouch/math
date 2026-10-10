import OAI.NumberTheory.Ostmann.ZeroDensity.SmoothFiniteRegularization
import OAI.NumberTheory.Ostmann.ZeroDensity.RectangleGeometry

namespace OAI

/-! # The finite rectangle identity for the actual smooth character integrand -/

namespace Ostmann

open Complex Set
open scoped Interval BigOperators Classical

/-- The finite contour-shift identity, with the genuine analytic zero orders.
The hypotheses specify only which finite set contains the rectangle's zeros
and that its points are interior; no residue or integral identity is assumed. -/
theorem smoothContour_rectangle_residues (χ : PrimitiveComplexCharacter)
    (X : ℝ) (hX : 0 < X) (a b c d : ℝ) (S : Finset ℂ)
    (hinside : ∀ z ∈ S, a < z.re ∧ z.re < b ∧ c < z.im ∧ z.im < d)
    (hzeros : ∀ z ∈ uIcc a b ×ℂ uIcc c d, χ.L z = 0 → z ∈ S) :
    rectangleBoundaryIntegral
      (fun z => (-deriv χ.L z / χ.L z) * smoothContourWeight X z) a b c d =
      -(2 * (Real.pi : ℂ) * I) *
        ∑ z ∈ S, (analyticOrderNatAt χ.L z : ℂ) * smoothContourWeight X z := by
  let f : ℂ → ℂ := fun z => (-deriv χ.L z / χ.L z) * smoothContourWeight X z
  let C : ℂ → ℂ := fun z => (analyticOrderNatAt χ.L z : ℂ) * smoothContourWeight X z
  let g : ℂ → ℂ := fun s => ∑ z ∈ S, C z * (s - z)⁻¹
  obtain ⟨F, hF, heF⟩ := smoothContour_finite_regularization χ X hX
    (uIcc a b ×ℂ uIcc c d) S hzeros
  have hnot (w : ℂ) (hw : w ∈ contourRectangleBoundary a b c d) : w ∉ S := by
    intro hmem
    exact contourBoundary_ne_interior (hinside w hmem) hw rfl
  have hnonzero (w : ℂ) (hw : w ∈ contourRectangleBoundary a b c d) : χ.L w ≠ 0 := by
    intro hzero
    exact hnot w hw (hzeros w ⟨hw.1, hw.2.1⟩ hzero)
  have hf : RectangleIntegrable f a b c d := by
    apply rectangleIntegrable_of_continuousOn
    intro w hw
    exact (((χ.L_analytic w).deriv.neg.div (χ.L_analytic w) (hnonzero w hw)).mul
      ((smoothContourWeight_differentiable X hX).analyticAt w)).continuousAt.continuousWithinAt
  have hterm (z : ℂ) (hz : z ∈ S) :
      RectangleIntegrable (fun s => C z * (s - z)⁻¹) a b c d :=
    (rectangleIntegrable_sub_inv (hinside z hz)).const_mul (C z)
  have hg : RectangleIntegrable g a b c d := RectangleIntegrable.sum S hterm
  have hfg : rectangleBoundaryIntegral F a b c d =
      rectangleBoundaryIntegral (fun z => f z + g z) a b c d := by
    apply rectangleBoundaryIntegral_congr
    intro z hz
    simpa only [f, g, C, div_eq_mul_inv] using heF z (hnot z hz)
  have hgvalue : rectangleBoundaryIntegral g a b c d =
      (2 * (Real.pi : ℂ) * I) * ∑ z ∈ S, C z := by
    rw [show g = (fun s => ∑ z ∈ S, C z * (s - z)⁻¹) from rfl,
      rectangleBoundaryIntegral_sum S hterm, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro z hz
    rw [rectangleBoundaryIntegral_const_mul,
      rectangleBoundaryIntegral_sub_inv z a b c d (hinside z hz).1
        (hinside z hz).2.1 (hinside z hz).2.2.1 (hinside z hz).2.2.2]
    ring
  have hzero := rectangleBoundaryIntegral_eq_zero hF
  rw [hfg, rectangleBoundaryIntegral_add hf hg, hgvalue] at hzero
  change rectangleBoundaryIntegral f a b c d = -(2 * (Real.pi : ℂ) * I) * ∑ z ∈ S, C z
  linear_combination hzero

end Ostmann

end OAI
