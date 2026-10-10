import OAI.Geometry.SurfaceImmersion.Geometry.GenericSurfaceLevels
import OAI.Geometry.SurfaceImmersion.Geometry.RegularPairCovectors

namespace OAI

/-! The regular-value condition in Euclidean surface charts implies the
nonzero determinant of the actual two covectors in our real coordinates. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open PublishedInputs PhaseGeometry SmallModes
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M] [IsManifold planeModel ∞ M]
variable {ι : Type*} [Fintype ι]

lemma surface_regular_pair_covectors
    (ρ : ι → M → ℝ) (hρ : ∀ i, ContMDiff planeModel 𝓘(ℝ) ∞ (ρ i))
    (i j : ι) (q : M) {p : M} (hp : p ∈ (chartAt Plane q).source)
    (hreg : Function.Surjective (fderiv ℝ (fun y => radiusPairProjection i j
      (fun k => ρ k ((chartAt Plane q).symm y))) (chartAt Plane q p))) :
    covectorDet
      (phaseDerivative (ρ i ∘ (coordinateChart q).symm) (coordinateChart q p))
      (phaseDerivative (ρ j ∘ (coordinateChart q).symm) (coordinateChart q p)) ≠ 0 := by
  let x : Plane := chartAt Plane q p
  let z : CurvePlane := coordinateChart q p
  let F : Plane → Plane := fun y => radiusPairProjection i j (fun k => ρ k ((chartAt Plane q).symm y))
  have hx : x ∈ (chartAt Plane q).target := (chartAt Plane q).map_source hp
  have hd (k : ι) : DifferentiableAt ℝ (fun y => ρ k ((chartAt Plane q).symm y)) x :=
    (((hρ k).comp_contMDiffOn (contMDiffOn_chart_symm (I := planeModel) (x := q))).contDiffOn
      x hx).contDiffAt ((chartAt Plane q).open_target.mem_nhds hx) |>.differentiableAt (by simp)
  have hF : DifferentiableAt ℝ F x :=
    (radiusPairProjection i j).differentiableAt.comp x (differentiableAt_pi.mpr hd)
  have hfx : planeCoordinates.symm z = x := by
    change planeCoordinates.symm (planeCoordinates (chartAt Plane q p)) = x
    exact planeCoordinates.symm_apply_apply x
  have heq : (fun y => (ρ i ((coordinateChart q).symm y),ρ j ((coordinateChart q).symm y))) =
      planeCoordinates ∘ F ∘ planeCoordinates.symm := by
    funext y
    apply Prod.ext <;> rfl
  have hFx : HasFDerivAt F (fderiv ℝ F x) (planeCoordinates.symm z) := by
    rw [hfx]
    exact hF.hasFDerivAt
  have hinner := hFx.comp z planeCoordinates.symm.hasFDerivAt
  have hcomp := planeCoordinates.hasFDerivAt.comp z hinner
  have hsurj : Function.Surjective (fderiv ℝ
      (fun y => (ρ i ((coordinateChart q).symm y),ρ j ((coordinateChart q).symm y))) z) := by
    rw [heq,hcomp.fderiv]
    exact planeCoordinates.surjective.comp (hreg.comp planeCoordinates.symm.surjective)
  have hsmall (k : ι) : DifferentiableAt ℝ (ρ k ∘ (coordinateChart q).symm) z := by
    have hk : DifferentiableAt ℝ (fun y => ρ k ((chartAt Plane q).symm y))
        (planeCoordinates.symm z) := by rw [hfx]; exact hd k
    exact hk.comp z planeCoordinates.symm.differentiableAt
  exact regular_pair_covectors (hsmall i) (hsmall j) hsurj

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
