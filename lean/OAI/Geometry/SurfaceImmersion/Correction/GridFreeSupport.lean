import OAI.Geometry.SurfaceImmersion.Atlas.GridCutoffSupport
import OAI.Geometry.SurfaceImmersion.Atlas.GridRestoredGeometry
import OAI.Geometry.SurfaceImmersion.Correction.FiniteAtlasFreeMetric

namespace OAI

/-! The actual free amplitudes have precisely the global grid supports
used in the quadratic cancellation theorem. -/
noncomputable section
open Set Manifold
open scoped ContDiff Manifold Topology NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean PhaseGrid PhaseGeometry
local instance gridFreeSupportFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance gridFreeSupportFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance gridFreeSupportDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance gridFreeSupportDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance gridFreeSupportSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance gridFreeSupportSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

lemma finiteGlobalAmplitude_grid_support
    {a : A.centers → Finset Index} {h : ℝ}
    {G : A.centers → JetPolynomial.Base → JetPolynomial.Space} {hG : ∀ i, ContDiff ℝ ∞ (G i)}
    {φ : ∀ i, ((a i) × Fin 3) → JetPolynomial.Base → ℝ} {τ : ℝ} {s : ℝ≥0}
    {c : ∀ i j, PolynomialSolveData emptyMetricPolynomial 0 (G i) (hG i) (φ i j)
      (A.cellChartCompact i (a i) h j.1.val) τ s}
    {r : A.centers → ℝ} {ρ R : ℝ} {reference : A.centers → SmallModes.Base → Tensor}
    (d : ∀ i j, ChartedMeanData (c i j) (r i) ρ R (reference i))
    (hρ : 0 < ρ) (δ : ℝ) (q : ℕ) (u : ∀ x : M, CovariantTwoTensor x)
    (i : A.centers) (j : (a i) × Fin 3) :
    tsupport (A.finiteGlobalAmplitude d hρ δ q u i j) ⊆
      A.gridPhaseSupport h ⟨i,j⟩ := by
  exact A.restore_cell_tsupport i (a i) h j.1.val
    ((d i j).freeAmplitude hρ δ q (A.tensorPlaneRead i u))
    ((d i j).freeAmplitude hρ δ q (A.tensorPlaneRead i u)).tsupport_subset

omit [CompactSpace M] in
lemma finiteGlobalPhase_eq_gridRestoredPhase
    {a : A.centers → Finset Index}
    (φ : ∀ i, ((a i) × Fin 3) → JetPolynomial.Base → ℝ)
    (ξ : AtlasCellPhase (ι := A.centers) → SmallModes.Base)
    (w : AtlasCellPhase (ι := A.centers) → ℝ)
    (hφ : ∀ i j, φ i j = phaseLinear (w (i,j.1.val,j.2) • ξ (i,j.1.val,j.2)) ∘
      planeCoordinateIsometry) (i : A.centers) (j : (a i) × Fin 3) :
    A.finiteGlobalPhase (ι := fun i => (a i) × Fin 3) (φ := φ) i j = A.gridRestoredPhase (s := a) ξ w ⟨i,j⟩ := by
  simp only [finiteGlobalPhase,hφ,gridRestoredPhase,gridPhaseLabel]

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
