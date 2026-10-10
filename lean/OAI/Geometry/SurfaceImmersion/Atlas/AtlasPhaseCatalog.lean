import OAI.Geometry.SurfaceImmersion.Correction.FiniteAtlasFreeMetric
import OAI.Geometry.SurfaceImmersion.Atlas.AtlasQuadraticTargets
import OAI.Geometry.SurfaceImmersion.Atlas.QuadraticPhaseCatalog

namespace OAI

/-! Fixed finite catalogs for the actual restored global grid phases and
their readings in every atlas chart. -/
noncomputable section
open Set Manifold
open scoped ContDiff Manifold BigOperators
namespace ClosedSurfaceR4.PhaseGeometry

def weightedCovectorCatalog (P : Finset PhaseBasis) (W : Finset ℝ) :
    Finset SmallModes.Base := by
  classical
  exact P.biUnion fun Q => W.biUnion fun w => Finset.univ.image (fun j : Fin 3 => w • Q.ξ j)

lemma mem_weightedCovectorCatalog (P : Finset PhaseBasis) (W : Finset ℝ)
    {Q : PhaseBasis} (hQ : Q ∈ P) {w : ℝ} (hw : w ∈ W) (j : Fin 3) :
    w • Q.ξ j ∈ weightedCovectorCatalog P W := by
  classical
  exact Finset.mem_biUnion.mpr ⟨Q,hQ,Finset.mem_biUnion.mpr
    ⟨w,hw,Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩⟩⟩

end ClosedSurfaceR4.PhaseGeometry
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open PhaseGeometry JetPolynomial JetPolynomial.Perturbation
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

def linearPhaseCatalog (V : Finset SmallModes.Base) : Finset (M → ℝ) := by
  classical
  exact Finset.univ.biUnion fun i : A.centers => V.image fun v =>
    restore (i : M) (A.outer i) (phaseLinear v ∘ planeCoordinateIsometry)

lemma restored_linear_phase_mem_catalog (V : Finset SmallModes.Base)
    (i : A.centers) {v : SmallModes.Base} (hv : v ∈ V) :
    restore (i : M) (A.outer i) (phaseLinear v ∘ planeCoordinateIsometry) ∈
      A.linearPhaseCatalog V := by
  classical
  exact Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,Finset.mem_image.mpr ⟨v,hv,rfl⟩⟩

lemma linearPhaseCatalog_smooth (V : Finset SmallModes.Base) :
    ∀ f ∈ A.linearPhaseCatalog V, ContMDiff planeModel 𝓘(ℝ) ∞ f := by
  classical
  intro f hf
  obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp hf
  obtain ⟨v,_,rfl⟩ := Finset.mem_image.mp hi
  exact restore_smooth (i : M) (A.outer_smooth i) (A.outer_support i)
    ((phaseLinear v).contDiff.comp planeCoordinateIsometry.contDiff)

lemma finiteGlobalPhase_mem_catalog (V : Finset SmallModes.Base)
    {ι : A.centers → Type*} (φ : ∀ i, ι i → JetPolynomial.Base → ℝ)
    (i : A.centers) (j : ι i) {v : SmallModes.Base} (hv : v ∈ V)
    (hφ : coordinatePhase (φ i j) = phaseLinear v) :
    A.finiteGlobalPhase (φ := φ) i j ∈ A.linearPhaseCatalog V := by
  have he : φ i j = phaseLinear v ∘ planeCoordinateIsometry := by
    funext x
    have hh := congrFun hφ (planeCoordinateIsometry x)
    simpa only [coordinatePhase,Function.comp_apply,LinearIsometryEquiv.symm_apply_apply] using hh
  simpa only [finiteGlobalPhase,he] using A.restored_linear_phase_mem_catalog V i hv

def localQuadraticPhaseCatalog (V : Finset SmallModes.Base) (k : A.centers) :
    Finset (SmallModes.Base → ℝ) := by
  classical
  exact RealModes.quadraticPhaseCatalog ((A.linearPhaseCatalog V).image (A.vectorPlaneRead k))

lemma globalQuadraticPhase_mem_catalog (V : Finset SmallModes.Base)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (φ : ι → M → ℝ)
    (hφ : ∀ a, φ a ∈ A.linearPhaseCatalog V) (k : A.centers)
    (l : RealModes.QuadraticLabel ι) :
    coordinatePhase (A.globalQuadraticPhase φ k l) ∈ A.localQuadraticPhaseCatalog V k := by
  classical
  have he : coordinatePhase (A.globalQuadraticPhase φ k l) =
      RealModes.quadraticPhase (fun a => A.vectorPlaneRead k (φ a)) l := by
    funext x
    simp only [coordinatePhase,globalQuadraticPhase,Function.comp_apply,
      LinearIsometryEquiv.apply_symm_apply]
  rw [he]
  apply RealModes.quadraticPhase_mem_catalog
  intro a
  exact Finset.mem_image.mpr ⟨φ a,hφ a,rfl⟩

variable [CompactSpace M]

lemma localQuadraticPhaseCatalog_smooth (V : Finset SmallModes.Base) (k : A.centers) :
    ∀ f ∈ A.localQuadraticPhaseCatalog V k, ContDiff ℝ ∞ f := by
  classical
  apply RealModes.quadraticPhaseCatalog_smooth
  intro f hf
  obtain ⟨g,hg,rfl⟩ := Finset.mem_image.mp hf
  exact A.vectorPlaneRead_smooth k (A.linearPhaseCatalog_smooth V g hg)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
