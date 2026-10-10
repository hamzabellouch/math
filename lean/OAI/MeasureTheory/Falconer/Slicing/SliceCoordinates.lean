import OAI.MeasureTheory.Falconer.Graphs.AllDimensionalGraphGeometry
import Mathlib.Analysis.Normed.Module.Normalize

namespace OAI

/-! # Isometric Euclidean coordinates on the actual finite-dimensional slice -/

namespace Falconer
open NormedSpace
variable {d m : ℕ}

noncomputable def sliceCoordinates (V : Submodule ℝ (Space d))
    (hm : Module.finrank ℝ V = m) : V ≃ₗᵢ[ℝ] Space m :=
  ((stdOrthonormalBasis ℝ V).reindex (finCongr hm)).repr

noncomputable def slicePointCoordinates (V : Submodule ℝ (Space d))
    (hm : Module.finrank ℝ V = m) (x : Space d) : Space m :=
  sliceCoordinates V hm (V.orthogonalProjectionOnto x)

theorem slicePointCoordinates_continuous (V : Submodule ℝ (Space d))
    (hm : Module.finrank ℝ V = m) : Continuous (slicePointCoordinates V hm) :=
  (sliceCoordinates V hm).continuous.comp V.orthogonalProjectionOnto.continuous

theorem slicePointCoordinates_norm (V : Submodule ℝ (Space d))
    (hm : Module.finrank ℝ V = m) (x : Space d) :
    ‖slicePointCoordinates V hm x‖ = ‖V.starProjection x‖ := by
  rw [slicePointCoordinates,(sliceCoordinates V hm).norm_map]
  rfl

theorem slicePointCoordinates_sub (V : Submodule ℝ (Space d))
    (hm : Module.finrank ℝ V = m) (x y : Space d) :
    slicePointCoordinates V hm (x-y) = slicePointCoordinates V hm x-slicePointCoordinates V hm y := by
  simp only [slicePointCoordinates,map_sub]

theorem slicePointCoordinates_dist (V : Submodule ℝ (Space d))
    (hm : Module.finrank ℝ V = m) (x y : Space d) :
    dist (slicePointCoordinates V hm x) (slicePointCoordinates V hm y) =
      dist (V.starProjection x) (V.starProjection y) := by
  rw [dist_eq_norm,← slicePointCoordinates_sub,slicePointCoordinates_norm,map_sub,dist_eq_norm]

theorem sliceCoordinates_normalize (V : Submodule ℝ (Space d))
    (hm : Module.finrank ℝ V = m) (x : V) :
    sliceCoordinates V hm (normalize x) = normalize (sliceCoordinates V hm x) := by
  simp only [NormedSpace.normalize,map_smul,(sliceCoordinates V hm).norm_map]

theorem sliceCoordinates_perpendicularPart (V : Submodule ℝ (Space d))
    (hm : Module.finrank ℝ V = m) (w x : V) :
    sliceCoordinates V hm (perpendicularPart w x) =
      perpendicularPart (sliceCoordinates V hm w) (sliceCoordinates V hm x) := by
  simp only [perpendicularPart,map_sub,map_smul,(sliceCoordinates V hm).inner_map_map]

end Falconer

end OAI
