import OAI.Geometry.SurfaceImmersion.Geometry.VectorReadBounds
import OAI.Geometry.SurfaceImmersion.Geometry.CompactSectionBounds

namespace OAI

/-! Fixed smooth phases have uniform directional-derivative bounds in every atlas chart. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean

local instance phaseReadBoundFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance phaseReadBoundFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance phaseReadBoundDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance phaseReadBoundDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance phaseReadBoundSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance phaseReadBoundSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem phase_read_gradient_bound {ι : Type*} [Fintype ι]
    (φ : ι → M → ℝ) (hφ : ∀ a, ContMDiff planeModel 𝓘(ℝ) ∞ (φ a)) (m : ℕ) :
    ∃ P : ℝ, 0 ≤ P ∧ ∀ k a (s : ℝ), 0 ≤ s → s ≤ 1 →
      ∀ v : SmallModes.Base, ‖v‖ ≤ 1 → WeightedEstimates.WeightedBound univ s m P
        (SmallModes.coordDeriv v (A.vectorPlaneRead k (φ a))) := by
  classical
  choose C hC hc using fun (k : A.centers) (a : ι) => compact_smooth_bound
    (A.vectorChartRead_smooth k (hφ a))
    (localize_compact (k : M) (A.outer_support k) (φ a)) (m+1)
  let P := ∑ k : A.centers, ∑ a : ι, C k a
  have hP : 0 ≤ P := Finset.sum_nonneg (fun k _ => Finset.sum_nonneg (fun a _ => hC k a))
  refine ⟨P,hP,?_⟩
  intro k a s hs hs1 v hv
  have hb := weightedBound_comp_isometry planeCoordinateIsometry.symm
    (A.vectorChartRead_smooth k (hφ a)) (hc k a)
  change WeightedEstimates.WeightedBound univ 1 (m+1) (C k a) (A.vectorPlaneRead k (φ a)) at hb
  have hd := hb.directional isOpen_univ (by norm_num : (0:ℝ)<1)
    (A.vectorPlaneRead_smooth k (hφ a)).contDiffOn v
  have hsize : ‖v‖*(C k a/1) ≤ C k a := by
    simpa only [div_one] using mul_le_of_le_one_left (hC k a) hv
  have hd' := (hd.mono_const hsize).shrink_scale hs hs1
  apply hd'.mono_const
  have h₁ : C k a ≤ ∑ b : ι, C k b := Finset.single_le_sum
    (fun b _ => hC k b) (Finset.mem_univ a)
  have h₂ : (∑ b : ι, C k b) ≤ P := Finset.single_le_sum
    (fun j _ => Finset.sum_nonneg (fun b _ => hC j b)) (Finset.mem_univ k)
  exact h₁.trans h₂

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
