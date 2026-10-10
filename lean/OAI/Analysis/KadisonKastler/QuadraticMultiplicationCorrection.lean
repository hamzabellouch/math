import OAI.Analysis.KadisonKastler.MultiplicationNewtonStep
import OAI.Analysis.KadisonKastler.CompleteLinearOperations

namespace OAI

/-! # Quantitative quadratic correction of an associative multiplication -/

namespace KadisonKastler

noncomputable section

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem quadratic_correction_half_bound {q : ℝ} (hq : 0 ≤ q) (hq1 : q ≤ 1 / 11) :
    (4 * q ^ 2) / (1 - q) ^ 2 ≤ q / 2 := by
  have hden : 0 < 1 - q := by linarith
  apply (div_le_iff₀ (sq_pos_of_pos hden)).mpr
  have hpoly : 0 ≤ 1 - 10 * q + q ^ 2 := by nlinarith [sq_nonneg q]
  nlinarith [mul_nonneg hq hpoly]

/-- A cochain with unit complete bound and quadratic coboundary error gives
an invertible, star-preserving correction which halves the error. -/
theorem quadratic_multiplication_half_step
    (m : A →ₗ[ℂ] A →ₗ[ℂ] A)
    (hm : ∀ x y z, m (m x y) z = m x (m y z))
    (hmstar : ∀ x y, star (m x y) = m (star y) (star x))
    {q : ℝ} (hq : 0 ≤ q) (hq1 : q ≤ 1 / 11)
    (hbound : HaagerupBound (m - LinearMap.mul ℂ A) q)
    (D : A →ₗ[ℂ] A) (hD : CompletelyBoundedBy D q)
    (hDstar : ∀ x, D (star x) = star (D x))
    (hres : HaagerupBound (m - LinearMap.mul ℂ A - linearCoboundary D) (2 * q ^ 2)) :
    ∃ L : A ≃ₗ[ℂ] A,
      L.toLinearMap = LinearMap.id + D ∧
      (∀ x, L (star x) = star (L x)) ∧
      CompletelyBoundedBy (L.toLinearMap - LinearMap.id) q ∧
      (∀ x y z, conjugatedBilinear L m (conjugatedBilinear L m x y) z =
        conjugatedBilinear L m x (conjugatedBilinear L m y z)) ∧
      (∀ x y, star (conjugatedBilinear L m x y) =
        conjugatedBilinear L m (star y) (star x)) ∧
      HaagerupBound (conjugatedBilinear L m - LinearMap.mul ℂ A) (q / 2) := by
  have hq_lt : q < 1 := by linarith
  obtain ⟨L, hL⟩ := hD.exists_equiv_add_id hq hq_lt
  have hLstar (x : A) : L (star x) = star (L x) := by
    change L.toLinearMap (star x) = star (L.toLinearMap x)
    simp only [hL, LinearMap.add_apply, LinearMap.id_apply, hDstar, star_add]
  refine ⟨L, hL, hLstar, ?_, conjugatedBilinear_assoc L m hm,
    conjugatedBilinear_star L hLstar m hmstar, ?_⟩
  · simpa only [hL, add_sub_cancel_left] using hD
  · have hnew := conjugatedBilinear_defect_bound m D L hL hq hq_lt hq
      (by positivity) hD hbound hres
    have hconstant : (2 * q ^ 2 + q * q + q ^ 2) / (1 - q) ^ 2 ≤ q / 2 := by
      convert quadratic_correction_half_bound hq hq1 using 1
      ring
    intro p r s X Y
    exact (hnew p r s X Y).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hconstant (norm_nonneg X)) (norm_nonneg Y))

end

end KadisonKastler

end OAI
