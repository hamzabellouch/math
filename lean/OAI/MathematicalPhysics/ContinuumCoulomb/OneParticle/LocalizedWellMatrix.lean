import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.PlanarWellMatrix
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.SplitCoordinates

namespace OAI

/-! Actual three-dimensional well matrix elements equal the planar ones:
the transverse Gaussian contributes exactly its unit squared mass. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

def localizedWellIntegrand (freq : ℝ) (u v w : PlanarPosition) (x : Position) : ℝ :=
  continuumLocalizedMode freq u x * manufacturedPlanarWell ((positionSplitCoordinates x).1 - w) *
    continuumLocalizedMode freq v x

theorem localizedWellIntegrand_split (freq : ℝ) (u v w : PlanarPosition) (x : Position) :
    localizedWellIntegrand freq u v w x =
      (normalizedPlanarMode ((positionSplitCoordinates x).1 - u) *
        manufacturedPlanarWell ((positionSplitCoordinates x).1 - w) *
        normalizedPlanarMode ((positionSplitCoordinates x).1 - v)) *
        verticalMode freq (positionSplitCoordinates x).2 ^ 2 := by
  unfold localizedWellIntegrand continuumLocalizedMode localizedMode
  ring

theorem localizedWellIntegrand_integrable {freq : ℝ} (hfreq : 0 < freq) (u v w : PlanarPosition) :
    Integrable (localizedWellIntegrand freq u v w) := by
  have hi : Integrable (fun p : SplitPosition =>
      (normalizedPlanarMode (p.1 - u) * manufacturedPlanarWell (p.1 - w) * normalizedPlanarMode (p.1 - v)) *
        verticalMode freq p.2 ^ 2) := by
    rw [Measure.volume_eq_prod]
    exact (planarWellMatrix_integrable u v w).mul_prod (verticalMode_square_integrable hfreq)
  have h := positionSplitCoordinates_measurePreserving.integrable_comp_of_integrable hi
  simpa only [Function.comp_def, ← localizedWellIntegrand_split] using h

theorem localizedWellIntegrand_integral {freq : ℝ} (hfreq : 0 < freq) (u v w : PlanarPosition) :
    (∫ x, localizedWellIntegrand freq u v w x) = planarWellMatrix u v w := by
  simp_rw [localizedWellIntegrand_split]
  rw [positionSplitCoordinates_integral (fun p =>
      (normalizedPlanarMode (p.1 - u) * manufacturedPlanarWell (p.1 - w) * normalizedPlanarMode (p.1 - v)) *
        verticalMode freq p.2 ^ 2), Measure.volume_eq_prod, integral_prod_mul
      (fun r => normalizedPlanarMode (r - u) * manufacturedPlanarWell (r - w) * normalizedPlanarMode (r - v))
      (fun z => verticalMode freq z ^ 2), verticalMode_normalized hfreq, mul_one]
  rfl

end ContinuumCoulomb

end

end OAI
