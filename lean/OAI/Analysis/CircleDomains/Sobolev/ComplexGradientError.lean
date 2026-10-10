import OAI.Analysis.CircleDomains.Sobolev.ComplexScalarEnergy

namespace OAI

/-! A smooth approximation is controlled by the two scalar weak-gradient
components and their actual coordinate errors. -/
open Set Function Filter MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem complexCovector_norm_le_abs (L : ℂ →L[ℝ] ℝ) :
    ‖L‖ ≤ |L 1|+|L Complex.I| := by
  have h := complexCovector_norm_sq L
  nlinarith [norm_nonneg L, abs_nonneg (L 1), abs_nonneg (L Complex.I),
    sq_abs (L 1), sq_abs (L Complex.I), mul_nonneg (abs_nonneg (L 1)) (abs_nonneg (L Complex.I))]

 theorem complex_scalar_gradient_error {u : EuclideanPlane → ℝ}
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) (p : EuclideanPlane) (a b : ℝ) :
    ‖fderiv ℝ (u ∘ complexPlaneCoordinates.symm) (complexPlaneCoordinates p)‖ ≤
      |a|+|b| + (|fderiv ℝ u p (EuclideanSpace.single 0 1)-a|+
        |fderiv ℝ u p (EuclideanSpace.single 1 1)-b|) := by
  have h := complexCovector_norm_le_abs
    (fderiv ℝ (u ∘ complexPlaneCoordinates.symm) (complexPlaneCoordinates p))
  dsimp only [Function.comp_def] at h
  rw [← complexPlaneCoordinates_zero, physical_complex_partial hu,
    ← complexPlaneCoordinates_one, physical_complex_partial hu] at h
  have h0 : |fderiv ℝ u p (EuclideanSpace.single 0 1)| ≤
      |a|+|fderiv ℝ u p (EuclideanSpace.single 0 1)-a| := by
    calc
      _ = |a+(fderiv ℝ u p (EuclideanSpace.single 0 1)-a)| := by congr 1; ring
      _ ≤ _ := abs_add_le _ _
  have h1 : |fderiv ℝ u p (EuclideanSpace.single 1 1)| ≤
      |b|+|fderiv ℝ u p (EuclideanSpace.single 1 1)-b| := by
    calc
      _ = |b+(fderiv ℝ u p (EuclideanSpace.single 1 1)-b)| := by congr 1; ring
      _ ≤ _ := abs_add_le _ _
  dsimp only [Function.comp_def]
  linarith

end CircleDomainRigidity

end

end OAI
