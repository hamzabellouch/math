import OAI.Geometry.SurfaceImmersion.Correction.AtlasRestoredPolynomialDirection
import OAI.Geometry.SurfaceImmersion.Geometry.LocalAnsatzSupport

namespace OAI

/-! The supported finite periodic ansatz is a genuine global smooth map,
with exactly the intended coordinate jets on its chosen chart. -/
noncomputable section
open Set Manifold
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation LocalPeriodicExpansion CovarianceCorrector
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

def periodicAtlasAnsatz (i : A.centers) (F : M → Space)
    {O : TopologicalSpace.Opens JetPolynomial.Base} (U : ℕ → Family O Space)
    (ℓ : JetPolynomial.Base →L[ℝ] ℝ) (L : ℕ) (z : ℝ) : M → Space :=
  F+restore (i : M) (A.outer i)
    (finiteAnsatz (A.vectorChartRead i F) U ℓ L z-A.vectorChartRead i F)

lemma jetChartMap_restored_supported (i : A.centers) (H : JetPolynomial.Base → Space)
    (hH : tsupport H ⊆ (A.chartWeightCompact i : Set JetPolynomial.Base)) :
    A.jetChartMap i (restore (i : M) (A.outer i) H) = spaceCoordinates ∘ H := by
  let X : RealModes.RField 4 := spaceCoordinates ∘ H ∘ planeCoordinateIsometry.symm
  have hx : tsupport X ⊆ (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base) := by
    have hs := tsupport_comp_subset (g := spaceCoordinates) (map_zero _)
      (H ∘ planeCoordinateIsometry.symm)
    have ht := tsupport_comp_preimage H planeCoordinateIsometry.symm planeCoordinateIsometry.symm.continuous
    intro x hxx
    have hh := hH (ht (hs hxx))
    exact ⟨planeCoordinateIsometry.symm x,hh,planeCoordinateIsometry.apply_symm_apply x⟩
  have he : (spaceCoordinates.symm ∘ X) ∘ planeCoordinateIsometry = H := by
    funext x
    simp [X]
  have hh := A.jetChartMap_restored_direction i X hx
  rw [he] at hh
  funext x
  simpa only [X,Function.comp_apply,planeCoordinateIsometry.symm_apply_apply] using congrFun hh x

lemma periodicAtlasAnsatz_smooth (i : A.centers) {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F)
    {O : TopologicalSpace.Opens JetPolynomial.Base} (U : ℕ → Family O Space)
    {K : Set JetPolynomial.Base} (hK : IsClosed K) (hKO : K ⊆ O)
    (hzero : ∀ j x, x ∉ K → (U j).val x = 0)
    (ℓ : JetPolynomial.Base →L[ℝ] ℝ) (L : ℕ) (z : ℝ) :
    ContMDiff planeModel spaceModel ∞ (A.periodicAtlasAnsatz i F U ℓ L z) := by
  have hlocal := finiteAnsatz_smooth_global (A.vectorChartRead_smooth i hF) U hK hKO
    (fun j x _ hx => hzero j x hx) ℓ L z
  exact hF.add (restore_smooth (i : M) (A.outer_smooth i) (A.outer_support i)
    (hlocal.sub (A.vectorChartRead_smooth i hF)))

/-- This equality is global in the chart coordinates and therefore also
identifies every derivative used by the periodic metric expansion. -/
lemma periodicAtlasAnsatz_coordinate (i : A.centers) (F : M → Space)
    {O : TopologicalSpace.Opens JetPolynomial.Base} (U : ℕ → Family O Space)
    {K : Set JetPolynomial.Base} (hK : IsClosed K)
    (hKA : K ⊆ (A.chartWeightCompact i : Set JetPolynomial.Base))
    (hzero : ∀ j x, x ∉ K → (U j).val x = 0)
    (ℓ : JetPolynomial.Base →L[ℝ] ℝ) (L : ℕ) (z : ℝ) :
    A.jetChartMap i (A.periodicAtlasAnsatz i F U ℓ L z) =
      spaceCoordinates ∘ finiteAnsatz (A.vectorChartRead i F) U ℓ L z := by
  have hs := (finiteAnsatz_tsupport_sub (A.vectorChartRead i F) U hK hzero ℓ L z).trans hKA
  unfold periodicAtlasAnsatz
  have hr := A.jetChartMap_restored_supported i
    (finiteAnsatz (A.vectorChartRead i F) U ℓ L z-A.vectorChartRead i F) hs
  rw [A.jetChartMap_add,hr]
  funext x
  change spaceCoordinates (A.vectorChartRead i F x)+
    spaceCoordinates (finiteAnsatz (A.vectorChartRead i F) U ℓ L z x-A.vectorChartRead i F x) = _
  rw [map_sub]
  change _ = spaceCoordinates (finiteAnsatz (A.vectorChartRead i F) U ℓ L z x)
  abel

/-- Outside the original chart support the global ansatz retains the exact
baseline germ, including all boundary jets on the exterior. -/
lemma periodicAtlasAnsatz_eventuallyEq (i : A.centers) (F : M → Space)
    {O : TopologicalSpace.Opens JetPolynomial.Base} (U : ℕ → Family O Space)
    {K : Set JetPolynomial.Base} (hK : IsClosed K)
    (hKA : K ⊆ (A.chartWeightCompact i : Set JetPolynomial.Base))
    (hzero : ∀ j x, x ∉ K → (U j).val x = 0)
    (ℓ : JetPolynomial.Base →L[ℝ] ℝ) (L : ℕ) (z : ℝ)
    {p : M} (hp : p ∉ tsupport (A.weight i)) :
    A.periodicAtlasAnsatz i F U ℓ L z =ᶠ[𝓝 p] F := by
  let H := finiteAnsatz (A.vectorChartRead i F) U ℓ L z-A.vectorChartRead i F
  have hs := (finiteAnsatz_tsupport_sub (A.vectorChartRead i F) U hK hzero ℓ L z).trans hKA
  have hs' : tsupport (H ∘ planeCoordinateIsometry.symm) ⊆
      (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base) := by
    intro x hx
    have hh := hs (tsupport_comp_preimage H planeCoordinateIsometry.symm planeCoordinateIsometry.symm.continuous hx)
    exact ⟨planeCoordinateIsometry.symm x,hh,planeCoordinateIsometry.apply_symm_apply x⟩
  have he : (H ∘ planeCoordinateIsometry.symm) ∘ planeCoordinateIsometry = H := by
    funext x
    simp
  have ht := A.restore_plane_tsupport i (H ∘ planeCoordinateIsometry.symm) hs'
  rw [he] at ht
  have hz := notMem_tsupport_iff_eventuallyEq.mp (fun hx => hp (ht hx))
  filter_upwards [hz] with x hx
  change F x+restore (i : M) (A.outer i) H x = F x
  rw [hx]
  exact add_zero _

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
