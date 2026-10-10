import OAI.Geometry.SurfaceImmersion.Atlas.GlobalPhaseGerms
import OAI.Geometry.SurfaceImmersion.Correction.GoodSmoothingAtlas
import OAI.Geometry.SurfaceImmersion.Atlas.QualitativePhaseTransfer
import OAI.Geometry.Immersion.ClosedSurface.ImmersionJets

namespace OAI

/-! Pure global phases remain good when read in any overlapping atlas
chart. This supplies the geometric input to the compact weight choice. -/
noncomputable section
open Set Manifold
open scoped ContDiff Manifold Topology

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open SmallModes RealModes PhaseGeometry
open JetPolynomial (planeCoordinateIsometry)
open JetPolynomial.Perturbation (modeSupport)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem linearAtlasPhase_unit_read_good {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F) (Q : A.centers → PhaseBasis)
    (houter : ∀ i x, x ∈ tsupport (A.weight i) → A.outer i =ᶠ[𝓝 x] (fun _ => 1))
    (hImm : ∀ i x, x ∈ (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base) →
      Function.Injective (fderiv ℝ (spaceCoordinates ∘ A.vectorPlaneRead i F) x))
    (hpure : ∀ i j x, x ∈ (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base) →
      Good (realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead i F) x) ((Q i).ξ j))
    (a : A.centers × Fin 3) (k : A.centers)
    {p : M} (hpa : p ∈ tsupport (A.weight a.1)) (hpk : p ∈ tsupport (A.weight k)) :
    Good (realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead k F) (coordinateChart (k : M) p))
      (phaseDerivative (A.vectorPlaneRead k (A.linearAtlasPhase Q (fun _ _ => 1) a))
        (coordinateChart (k : M) p)) := by
  have hpA : p ∈ (coordinateChart (a.1 : M)).source := by
    simpa only [coordinateChart_source,chart_source] using A.weight_support a.1 hpa
  have hpK : p ∈ (coordinateChart (k : M)).source := by
    simpa only [coordinateChart_source,chart_source] using A.weight_support k hpk
  have hxA : coordinateChart (a.1 : M) p ∈
      (modeSupport (A.chartWeightCompact a.1) : Set SmallModes.Base) := by
    exact ⟨chart (a.1 : M) p,⟨p,hpa,rfl⟩,rfl⟩
  have heA := A.vectorPlaneRead_eventually_coordinateMap F a.1 (houter a.1) hpa
  have hdA := heA.fderiv_eq (𝕜 := ℝ)
  have hsA := (realSecondTensor_eventuallyEq heA).eq_of_nhds
  have hi := hImm a.1 _ hxA
  have hg := hpure a.1 a.2 _ hxA
  change fderiv ℝ (spaceCoordinates ∘ A.vectorPlaneRead a.1 F) (coordinateChart (a.1 : M) p) =
    fderiv ℝ (coordinateMap F (a.1 : M)) (coordinateChart (a.1 : M) p) at hdA
  change realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead a.1 F) (coordinateChart (a.1 : M) p) =
    realSecondTensor (coordinateMap F (a.1 : M)) (coordinateChart (a.1 : M) p) at hsA
  rw [hdA] at hi
  rw [hsA] at hg
  have ht := actual_phase_good_at hF (a.1 : M) (k : M) hpK hpA ((Q a.1).ξ a.2)
    (gramDet_ne_zero_of_injective _ hi) hg
  have heK := A.vectorPlaneRead_eventually_coordinateMap F k (houter k) hpk
  have hsK := (realSecondTensor_eventuallyEq heK).eq_of_nhds
  change realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead k F) (coordinateChart (k : M) p) =
    realSecondTensor (coordinateMap F (k : M)) (coordinateChart (k : M) p) at hsK
  rw [hsK,A.linearAtlasPhase_read_phaseDerivative Q (fun _ _ => 1) a k houter hpa hpk,
    one_smul]
  exact ht

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
