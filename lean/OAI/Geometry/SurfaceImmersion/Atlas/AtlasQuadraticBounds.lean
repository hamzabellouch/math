import OAI.Geometry.SurfaceImmersion.Atlas.AtlasQuadraticTargets
import OAI.Geometry.SurfaceImmersion.Atlas.CutoffQuadraticBounds

namespace OAI

/-! Uniform delta-squared bounds for the actual global quadratic targets. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean

local instance atlasQuadraticBoundsFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance atlasQuadraticBoundsFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance atlasQuadraticBoundsDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance atlasQuadraticBoundsDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance atlasQuadraticBoundsSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance atlasQuadraticBoundsSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
theorem globalQuadraticTarget_bound (k : A.centers) (m : ℕ) (A₀ P₀ : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (τ s δ : ℝ) (φ : ι → M → ℝ) (Z : ι → M → Fin 4 → ℂ)
      (hφ : ∀ a, ContMDiff planeModel 𝓘(ℝ) ∞ (φ a))
      (hZ : ∀ a, ContMDiff planeModel 𝓘(ℝ,Fin 4 → ℂ) ∞ (Z a)),
      0 < τ → 0 < s → τ ≤ s → s ≤ 1 → 0 ≤ δ → 0 ≤ A₀ → 0 ≤ P₀ →
      (∀ a, WeightedEstimates.WeightedBound univ s (m+1) (A₀*(δ*τ)) (A.vectorPlaneRead k (Z a))) →
      (∀ a v, ‖v‖ ≤ 1 → WeightedEstimates.WeightedBound univ s m P₀
        (SmallModes.coordDeriv v (A.vectorPlaneRead k (φ a)))) →
      ∀ l : RealModes.QuadraticLabel ι, WeightedEstimates.WeightedBound univ s m (B*δ^2)
        (A.globalQuadraticTarget τ φ Z hφ hZ k l) := by
  obtain ⟨B,hB,hb⟩ := cutoff_quadratic_bound (ι := ι) (A.supportedPlaneWeight k) m A₀ P₀
  refine ⟨B,hB,?_⟩
  intro τ s δ φ Z hφ hZ hτ hs hτs hs1 hδ hA hP hz hp l
  exact hb τ s δ (fun a => A.vectorPlaneRead k (φ a)) (fun a => A.vectorPlaneRead k (Z a))
    (fun a => A.vectorPlaneRead_smooth k (hφ a)) (fun a => A.vectorPlaneRead_smooth k (hZ a))
    hτ hs hτs hs1 hδ hA hP hz hp l

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
