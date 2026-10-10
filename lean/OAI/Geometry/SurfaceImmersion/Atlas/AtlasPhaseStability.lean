import OAI.Geometry.SurfaceImmersion.Atlas.AtlasPhaseJetBounds

namespace OAI

/-! Fixed local good-phase charts persist under a global C2 perturbation. -/
noncomputable section
open Set Manifold
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial PhaseGeometry WeightedEstimates RealModes
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

omit [CompactSpace M] in
lemma vectorPlaneRead_sub {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (i : A.centers) (F G : M → V) :
    A.vectorPlaneRead i (F-G) = A.vectorPlaneRead i F - A.vectorPlaneRead i G := by
  funext x
  by_cases hx : planeCoordinateIsometry.symm x ∈ (chart (i : M)).target <;>
    simp [vectorPlaneRead,vectorChartRead,localize,hx,smul_sub]

theorem phaseChart_global_C2_stability (i : A.centers)
    {F : M → Space} (hF : ContMDiff planeModel spaceModel ∞ F)
    {φ : SmallModes.Base → ℝ}
    (e : GoodPhaseChart (spaceCoordinates ∘ A.vectorPlaneRead i F) φ) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ (G : M → Space), ContMDiff planeModel spaceModel ∞ G →
      ∀ B : ℝ, 0 ≤ B → B < ρ → A.WeightedBound 1 2 B (G-F) →
      RealModeDomain ((spaceCoordinates ∘ A.vectorPlaneRead i G) ∘ e.chart.symm)
        e.chart.target := by
  obtain ⟨r,Q,hr,_,_,hnear⟩ := e.uniform_jet_neighborhood
    (spaceCoordinates.contDiff.comp (A.vectorPlaneRead_smooth i hF))
  obtain ⟨D,hD,hd⟩ := A.vectorPlaneRead_bound (V := Space) i 2
  let L := ‖spaceCoordinates.toContinuousLinearMap‖*D
  have hL : 0 ≤ L := mul_nonneg (norm_nonneg _) hD
  have hLp : 0 < 1+L := by linarith
  refine ⟨r/(1+L),div_pos hr hLp,?_⟩
  intro G hG B hB hBr hb
  have hread := hd (G-F) 1 B zero_lt_one le_rfl hB (hG.sub hF) hb
  have hlocal := hread.linear uniqueDiffOn_univ zero_le_one
    (A.vectorPlaneRead_smooth i (hG.sub hF)).contDiffOn spaceCoordinates.toContinuousLinearMap
  simp only [ContinuousLinearEquiv.coe_coe] at hlocal
  change WeightedEstimates.WeightedBound univ 1 2 _
    (spaceCoordinates ∘ A.vectorPlaneRead i (G-F)) at hlocal
  have he : spaceCoordinates ∘ A.vectorPlaneRead i (G-F) =
      (spaceCoordinates ∘ A.vectorPlaneRead i G) -
        (spaceCoordinates ∘ A.vectorPlaneRead i F) := by
    rw [A.vectorPlaneRead_sub]
    funext x
    exact map_sub spaceCoordinates _ _
  rw [he] at hlocal
  have hsize : L*B < r := by
    have hh : B*(1+L) < r := (lt_div_iff₀ hLp).mp hBr
    nlinarith
  exact (hnear (spaceCoordinates ∘ A.vectorPlaneRead i G)
    (spaceCoordinates.contDiff.comp (A.vectorPlaneRead_smooth i hG))
    (L*B) (mul_nonneg hL hB) hsize (by simpa only [L,mul_assoc] using hlocal)).2

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
