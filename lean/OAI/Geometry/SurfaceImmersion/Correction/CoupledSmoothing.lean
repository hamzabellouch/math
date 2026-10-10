import OAI.Geometry.SurfaceImmersion.Correction.TensorSmoothing
import OAI.Geometry.SurfaceImmersion.Correction.GlobalShiftedSmoothing

namespace OAI

/-! The joint map/tensor input bound and its actual two-scale smoothing tail. -/
noncomputable section
open scoped ContDiff Manifold Topology

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold Bundle
open JetPolynomial (Base)

local instance coupledModelNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance coupledModelSpace : NormedSpace ℝ TensorFiber := inferInstance
local instance coupledModelComplete : CompleteSpace TensorFiber := inferInstance

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

/-- The map carries a two-derivative prefix, while the metric defect has none. -/
def InputBound (t : ℝ) (m : ℕ) (C : ℝ) (G : M → Space)
    (H : ∀ p : M, CovariantTwoTensor p) : Prop :=
  A.ShiftedBound 2 m t C G ∧ A.TensorWeightedBound t m C H

/-- The two smoothing errors obey the finite-input estimate together, with
only linear dependence on the possibly large higher input norm. -/
theorem coupled_smoothing_tail (r m : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (G : M → Space) (H : ∀ p : M, CovariantTwoTensor p)
      (s t τ B C : ℝ),
      0 < τ → τ ≤ s → s ≤ t → t ≤ 1 → 0 ≤ B → 0 ≤ C →
      ContMDiff planeModel spaceModel ∞ G →
      ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
        (fun p => TotalSpace.mk' TensorFiber p (H p)) →
      A.InputBound t r B G H → A.InputBound t m C G H →
      A.InputBound τ m
        (D * tailConstant r * (B * (s / t) ^ r + C * (τ / t) ^ r))
        (G - A.smooth r s G) (fun p => H p - A.tensorSmooth r s H p) := by
  obtain ⟨DG, hDG, hG⟩ := A.smoothing_shifted_tail (V := Space) r 2 m
  obtain ⟨DH, hDH, hH⟩ := A.tensor_smoothing_tail r m
  refine ⟨DG + DH, add_nonneg hDG hDH, ?_⟩
  intro G H s t τ B C hτ hτs hst ht1 hB hC hGs hHs hbr hcm
  have hs : 0 < s := hτ.trans_le hτs
  have ht : 0 < t := hs.trans_le hst
  have hsize : 0 ≤ B * (s / t) ^ r + C * (τ / t) ^ r := by positivity
  have hg := hG G s t τ B C hτ hτs hst ht1 hB hC hGs hbr.1 hcm.1
  have hh := hH H s t τ B C hτ hτs hst ht1 hB hC hHs hbr.2 hcm.2
  constructor
  · intro i j hj x
    exact (hg i j hj x).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hDH) (tailConstant_nonneg r)) hsize)
  · intro i
    exact (hh i).mono_const (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hDG) (tailConstant_nonneg r)) hsize)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
