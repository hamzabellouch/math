import OAI.Geometry.SurfaceImmersion.Atlas.GridCutoffSupport
import OAI.Geometry.SurfaceImmersion.Correction.GoodSmoothingAtlas
import OAI.Geometry.Immersion.ClosedSurface.AtlasWeights
import OAI.Geometry.Immersion.ClosedSurface.LengthMargins

namespace OAI

/-! Transfer the selected cell's normal geometry to its exact local support. -/
noncomputable section
open Set Manifold
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseGrid PhaseGeometry RealModes
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

lemma cellChartCompact_normal_geometry (i : A.centers) (a : Finset Index) (h : ℝ) (k : Index)
    (F : M → Space)
    (houter : ∀ p, p ∈ tsupport (A.weight i) → A.outer i =ᶠ[𝓝 p] (fun _ => 1))
    (ξ : SmallModes.Base) (D : ℝ)
    (hgood : ∀ p ∈ tsupport (refinedCutoff (i : M) (A.weight i) a h k),
      Good (atlasSecondTensor F (i : M) p) ξ)
    (hn : ∀ p ∈ tsupport (refinedCutoff (i : M) (A.weight i) a h k),
      ‖secondQuadratic (atlasSecondTensor F (i : M) p) (-ξ.2,ξ.1)‖⁻¹ ≤ D) :
    ∀ x ∈ (modeSupport (A.cellChartCompact i a h k) : Set SmallModes.Base),
      Good (realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead i F) x) ξ ∧
      ‖secondQuadratic (realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead i F) x)
        (-ξ.2,ξ.1)‖⁻¹ ≤ D := by
  rintro x ⟨y,⟨p,hp,rfl⟩,rfl⟩
  have hpw := refinedCutoff_tsupport_outer (i : M) (A.weight i) a h k hp
  have he := (realSecondTensor_eventuallyEq
    (A.vectorPlaneRead_eventually_coordinateMap F i houter hpw)).eq_of_nhds
  change realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead i F)
    (planeCoordinateIsometry (chart (i : M) p)) = atlasSecondTensor F (i : M) p at he
  rw [he]
  exact ⟨hgood p hp,hn p hp⟩

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
