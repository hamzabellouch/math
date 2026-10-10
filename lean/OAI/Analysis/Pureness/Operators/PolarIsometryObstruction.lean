import OAI.Analysis.Pureness.Operators.NearIsometryObstruction
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic

namespace OAI
noncomputable section
namespace CuntzPureness
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem nonunitary_isometry_of_nonunit_square (y : A)
    (hsq : IsUnit (star y * y)) (hy : ¬ IsUnit y) :
    ∃ u : A, star u * u = 1 ∧ u * star u ≠ 1 := by
  obtain ⟨s, hs⟩ := (CFC.isUnit_sqrt_iff (star y * y) (star_mul_self_nonneg y)).mpr hsq
  have hfactor : star y * y = star (s : A) * (s : A) := by
    rw [hs, (CFC.sqrt_nonneg (star y * y)).star_eq,
      CFC.sqrt_mul_sqrt_self _ (star_mul_self_nonneg y)]
  let u : A := y * (↑s⁻¹ : A)
  have hu : star u * u = 1 := by
    calc
      _ = star (↑s⁻¹ : A) * (star y * y) * (↑s⁻¹ : A) := by
        simp only [u, star_mul, mul_assoc]
      _ = star ((s : A) * (↑s⁻¹ : A)) * ((s : A) * (↑s⁻¹ : A)) := by
        rw [hfactor]
        simp only [star_mul, mul_assoc]
      _ = 1 := by simp
  refine ⟨u, hu, ?_⟩
  intro hh
  have hunit : IsUnit u := ⟨⟨u, star u, hh, hu⟩, rfl⟩
  have he : y = u * (s : A) := by simp [u, mul_assoc]
  exact hy (he ▸ hunit.mul s.isUnit)
end CuntzPureness

end

end OAI
