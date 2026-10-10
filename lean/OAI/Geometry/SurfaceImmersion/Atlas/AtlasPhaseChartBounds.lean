import OAI.Geometry.SurfaceImmersion.Atlas.AtlasPhaseReadBounds

namespace OAI

/-! Fixed smooth phases have uniform directional-derivative bounds in every atlas chart. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean

local instance phaseChartReadBoundFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance phaseChartReadBoundFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance phaseChartReadBoundDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance phaseChartReadBoundDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance phaseChartReadBoundSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance phaseChartReadBoundSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

/-- The coordinate derivatives used by the polynomial phase estimates obey
fixed profiles as the slow scale varies. -/
theorem phase_chart_gradient_bound {ι : Type*} [Fintype ι]
    (φ : ι → M → ℝ) (hφ : ∀ a, ContMDiff planeModel 𝓘(ℝ) ∞ (φ a)) (m : ℕ) :
    ∃ P : ℝ, 0 ≤ P ∧ ∀ k a (s : ℝ), 0 ≤ s → s ≤ 1 → ∀ v : Fin 2,
      WeightedEstimates.WeightedBound univ s m P
        (fun x => fderiv ℝ (A.vectorChartRead k (φ a)) x (coordinateVector v)) := by
  classical
  choose C hC hc using fun (k : A.centers) (a : ι) => compact_smooth_bound
    (A.vectorChartRead_smooth k (hφ a))
    (localize_compact (k : M) (A.outer_support k) (φ a)) (m+1)
  let P := ∑ k : A.centers, ∑ a : ι, C k a
  have hP : 0 ≤ P := Finset.sum_nonneg (fun k _ => Finset.sum_nonneg (fun a _ => hC k a))
  refine ⟨P,hP,?_⟩
  intro k a s hs hs1 v
  have hd := (hc k a).directional isOpen_univ (by norm_num : (0:ℝ)<1)
    (A.vectorChartRead_smooth k (hφ a)).contDiffOn (coordinateVector v)
  have hv : ‖coordinateVector v‖ = 1 := by simp only [coordinateVector,Pi.norm_single,norm_one]
  have hd' := hd.mono_const (show ‖coordinateVector v‖*(C k a/1) ≤ C k a by rw [hv]; simp)
  apply (hd'.shrink_scale hs hs1).mono_const
  exact (Finset.single_le_sum (fun b _ => hC k b) (Finset.mem_univ a)).trans
    (Finset.single_le_sum (fun j _ => Finset.sum_nonneg (fun b _ => hC j b)) (Finset.mem_univ k))

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
