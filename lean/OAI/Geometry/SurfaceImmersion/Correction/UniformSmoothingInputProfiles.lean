import OAI.Geometry.SurfaceImmersion.Correction.CoupledSmoothing

namespace OAI

/-! The fixed low input norm supplies all profiles of the smoothed map
and tensor, before the true input or either scale is chosen. -/
noncomputable section
open Set Manifold Bundle MeasureTheory
open scoped ContDiff Manifold Topology

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open WeightedEstimates

local instance smoothingProfileFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance smoothingProfileFiberSpace : NormedSpace ℝ TensorFiber := inferInstance

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

local instance smoothingProfileDualAdd : ∀ p : M,
    ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance smoothingProfileDualSmul : ∀ p : M,
    ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance smoothingProfileSectionNormed (p : M) :
    NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance smoothingProfileSectionSpace (p : M) :
    NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem uniform_smoothing_input_profiles (r : ℕ) (B : ℝ) (hB : 0 ≤ B) :
    ∃ P C : ℕ → ℝ, (∀ m, 0 ≤ P m) ∧ (∀ m, 1 ≤ C m) ∧
      ∀ (G : M → Space) (H : ∀ x : M, CovariantTwoTensor x) (t s : ℝ),
        0 < t → t ≤ 1 → 0 < s → s ≤ 1 →
        ContMDiff planeModel spaceModel ∞ G →
        ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
          (fun x => TotalSpace.mk' TensorFiber x (H x)) →
        A.InputBound t r B G H →
        (∀ m, A.ShiftedBound 2 m s (P m) (A.smooth r s G)) ∧
        (∀ m, A.TensorWeightedBound s m (C m) (A.tensorSmooth r s H)) := by
  classical
  choose DG hDG hg using fun m => A.smoothing_shifted_gain (V := Space) r 2 m
  choose DH hDH hh using fun m => A.tensor_smoothing_bounds r m
  let P : ℕ → ℝ := fun m =>
    DG m * ((1 + (1 + ∫ y, ‖kernel 0 y‖) ^ r) + weightedGainConstant r m) * B
  let C : ℕ → ℝ := fun m => 1 + DH m * weightedGainConstant r m * B
  have hker : 0 ≤ ∫ y, ‖kernel 0 y‖ := integral_nonneg (fun _ => norm_nonneg _)
  have hP (m : ℕ) : 0 ≤ P m := by
    have := hDG m
    have := weightedGainConstant_nonneg r m
    dsimp [P]
    positivity
  have hC (m : ℕ) : 1 ≤ C m := by
    have ht := mul_nonneg (mul_nonneg (hDH m) (weightedGainConstant_nonneg r m)) hB
    dsimp [C]
    linarith
  refine ⟨P,C,hP,hC,?_⟩
  intro G H t s _ht _ht1 hs hs1 hG hH hinput
  have hprefix : A.ShiftedBound 2 0 1 B G := by
    intro i j hj x
    have hj2 : j ≤ 2 := by omega
    have hjr : j ≤ 2 + r := by omega
    have hb := hinput.1 i j hjr x
    simpa only [Nat.sub_eq_zero_of_le hj2,pow_zero,one_mul] using hb
  refine ⟨fun m => hg m G s B hs hs1 hB hG hprefix,?_⟩
  intro m i
  have hzero : A.TensorWeightedBound t 0 B H :=
    fun k => (hinput.2 k).mono_order (Nat.zero_le r)
  exact ((hh m).2 H s t B hs hs1 hB hH hzero i).mono_const (by
    change DH m * weightedGainConstant r m * B ≤ 1 + DH m * weightedGainConstant r m * B
    linarith)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
