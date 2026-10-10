import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.PlanarWellMatrix
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.PlanarSobolev

namespace OAI

/-! A well at any center has an off-diagonal matrix bound from the actual
orbital overlap. This also controls the small depth counterterms. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem planarWellMatrix_le_overlap (u v w : PlanarPosition) :
    |planarWellMatrix u v w| ≤ PlanarSobolev.wellBound * planarModeOverlap u v := by
  have hi := (planarModeOverlap_integrable u v).const_mul PlanarSobolev.wellBound
  have h := norm_integral_le_of_norm_le (f := fun r =>
    normalizedPlanarMode (r - u) * manufacturedPlanarWell (r - w) * normalizedPlanarMode (r - v))
    hi (Filter.Eventually.of_forall (fun r => by
    rw [norm_mul, norm_mul, Real.norm_of_nonneg (normalizedPlanarMode_positive _).le,
      Real.norm_of_nonneg (normalizedPlanarMode_positive _).le]
    have hp := mul_le_mul_of_nonneg_right (PlanarSobolev.wellBound_spec (r - w))
      (mul_nonneg (normalizedPlanarMode_positive (r - u)).le (normalizedPlanarMode_positive (r - v)).le)
    convert hp using 1
    ring))
  simpa only [Real.norm_eq_abs, integral_const_mul, planarWellMatrix, planarModeOverlap] using h

theorem planarWellMatrix_overlap_decay (u v w : PlanarPosition) :
    |planarWellMatrix u v w| ≤
      (PlanarSobolev.wellBound * planarOverlapConstant) * Real.exp (-(9 / 10 : ℝ) * ‖u - v‖) := by
  exact (planarWellMatrix_le_overlap u v w).trans ((mul_le_mul_of_nonneg_left
    (planarModeOverlap_decay u v) PlanarSobolev.wellBound_nonnegative).trans_eq (mul_assoc _ _ _).symm)

end ContinuumCoulomb

end

end OAI
