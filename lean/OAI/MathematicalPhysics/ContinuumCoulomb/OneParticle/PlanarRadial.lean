import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.PlanarHopping
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

namespace OAI

/-! Rotation/reflection invariance of the actual manufactured planar data.
The hopping between arbitrary translated centers depends only on distance. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem planarForcing_isometry (L : PlanarPosition ≃ₗᵢ[ℝ] PlanarPosition) (r : PlanarPosition) :
    planarForcing (L r) = planarForcing r := by
  simp only [planarForcing, L.norm_map]

theorem planarResolventKernel_isometry (L : PlanarPosition ≃ₗᵢ[ℝ] PlanarPosition)
    (r : PlanarPosition) : planarResolventKernel (L r) = planarResolventKernel r := by
  simp only [planarResolventKernel, planarResolventIntegrand, planarHeatKernel, L.norm_map]

theorem planarResolventMode_isometry (L : PlanarPosition ≃ₗᵢ[ℝ] PlanarPosition)
    (r : PlanarPosition) : planarResolventMode (L r) = planarResolventMode r := by
  unfold planarResolventMode
  rw [← MeasureTheory.integral_comp L
    (fun b => planarResolventKernel b * planarForcing (L r - b))]
  apply integral_congr_ae
  filter_upwards [] with b
  rw [planarResolventKernel_isometry, ← L.map_sub, planarForcing_isometry]

theorem normalizedPlanarMode_isometry (L : PlanarPosition ≃ₗᵢ[ℝ] PlanarPosition)
    (r : PlanarPosition) : normalizedPlanarMode (L r) = normalizedPlanarMode r := by
  simp only [normalizedPlanarMode, planarResolventMode_isometry]

theorem manufacturedPlanarWell_isometry (L : PlanarPosition ≃ₗᵢ[ℝ] PlanarPosition)
    (r : PlanarPosition) : manufacturedPlanarWell (L r) = manufacturedPlanarWell r := by
  simp only [manufacturedPlanarWell, planarResolventMode_isometry, planarForcing_isometry]

theorem planarResolventMode_radial {r s : PlanarPosition} (h : ‖r‖ = ‖s‖) :
    planarResolventMode r = planarResolventMode s := by
  have hi := planarResolventMode_isometry ((ℝ ∙ (r - s))ᗮ.reflection) r
  rw [Submodule.reflection_sub h] at hi
  exact hi.symm

theorem normalizedPlanarMode_radial {r s : PlanarPosition} (h : ‖r‖ = ‖s‖) :
    normalizedPlanarMode r = normalizedPlanarMode s := by
  simp only [normalizedPlanarMode, planarResolventMode_radial h]

theorem manufacturedPlanarWell_radial {r s : PlanarPosition} (h : ‖r‖ = ‖s‖) :
    manufacturedPlanarWell r = manufacturedPlanarWell s := by
  simp only [manufacturedPlanarWell, planarResolventMode_radial h, planarForcing, h]

def planarHoppingAt (u : PlanarPosition) : ℝ :=
  (∫ r, planarForcing r * planarResolventMode (r - u)) /
    (2 * ∫ r, planarResolventMode r ^ 2)

theorem planarHoppingAt_isometry (L : PlanarPosition ≃ₗᵢ[ℝ] PlanarPosition)
    (u : PlanarPosition) : planarHoppingAt (L u) = planarHoppingAt u := by
  unfold planarHoppingAt
  congr 1
  rw [← MeasureTheory.integral_comp L
    (fun r => planarForcing r * planarResolventMode (r - L u))]
  apply integral_congr_ae
  filter_upwards [] with r
  rw [planarForcing_isometry, ← L.map_sub, planarResolventMode_isometry]

theorem planarHoppingAt_norm (u : PlanarPosition) : planarHoppingAt u = planarHopping ‖u‖ := by
  have hn : ‖‖u‖ • planarAxis 0‖ = ‖u‖ := by
    rw [norm_smul, planarAxis_zero_norm, mul_one, Real.norm_of_nonneg (norm_nonneg u)]
  have h := planarHoppingAt_isometry ((ℝ ∙ (‖u‖ • planarAxis 0 - u))ᗮ.reflection)
    (‖u‖ • planarAxis 0)
  rw [Submodule.reflection_sub hn] at h
  exact h

end ContinuumCoulomb

end

end OAI
