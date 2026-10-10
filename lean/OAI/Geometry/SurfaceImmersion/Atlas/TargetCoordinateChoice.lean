import OAI.Geometry.SurfaceImmersion.Atlas.ScalarCoordinateAugmentation
import Mathlib.LinearAlgebra.Dual.Lemmas

namespace OAI

/-! A nonzero derivative has a nonzero scalar target coordinate, which
can be completed to a linear isomorphism of the target. -/
noncomputable section
open Set
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]

theorem target_coordinate_choice (hdim : Module.finrank ℝ F = Module.finrank ℝ G + 1)
    (D : E →L[ℝ] F) (hD : D ≠ 0) :
    ∃ e : F ≃L[ℝ] (ℝ × G), (ContinuousLinearMap.fst ℝ ℝ G).comp
      (e.toContinuousLinearMap.comp D) ≠ 0 := by
  obtain ⟨v,hv⟩ := DFunLike.ne_iff.mp hD
  obtain ⟨ℓ,hℓ⟩ := Module.Projective.exists_dual_eq_one ℝ (show D v ≠ 0 by simpa using hv)
  let L : F →L[ℝ] ℝ := ℓ.toContinuousLinearMap
  have hL : Function.Surjective L := by
    intro t
    refine ⟨t • D v,?_⟩
    change ℓ (t • D v) = t
    rw [map_smul,hℓ,smul_eq_mul,mul_one]
  obtain ⟨R,hR⟩ := scalar_coordinate_augmentation hdim L hL
  let e := ContinuousLinearEquiv.ofBijective (L.prod R)
    (LinearMap.ker_eq_bot.mpr hR.1) (LinearMap.range_eq_top.mpr hR.2)
  refine ⟨e,?_⟩
  intro hzero
  have hh := congrArg (fun A : E →L[ℝ] ℝ => A v) hzero
  change L (D v) = 0 at hh
  have hh' : L (D v) = 1 := hℓ
  linarith

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
