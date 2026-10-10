import OAI.Geometry.SurfaceImmersion.Correction.UniformSmoothingInputProfiles
import OAI.Geometry.SurfaceImmersion.Correction.PolynomialMeanIteration

namespace OAI

/-! Polynomial bounds for smoothed inputs with a polynomial finite input budget. -/
noncomputable section
open Set Manifold Bundle MeasureTheory
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open WeightedEstimates RealModes
local instance polySmoothingProfileFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance polySmoothingProfileFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance polySmoothingProfileDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance polySmoothingProfileDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance polySmoothingProfileSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance polySmoothingProfileSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem polynomial_smoothing_input_profiles (r : ℕ) (B : ℝ → ℝ) (hB : HasPolynomialBound B) :
    ∃ P C : ℕ → ℝ → ℝ,
      (∀ m, HasPolynomialBound (P m)) ∧ (∀ m, HasPolynomialBound (C m)) ∧
      (∀ m x, 1 ≤ x → 1 ≤ C m x) ∧
    ∀ x : ℝ, 1 ≤ x →
      ∀ (G : M → Space) (H : ∀ y : M, CovariantTwoTensor y) (t s : ℝ),
      0 < t → t ≤ 1 → 0 < s → s ≤ 1 →
      ContMDiff planeModel spaceModel ∞ G →
      ContMDiff planeModel (planeModel.prod 𝓘(ℝ,TensorFiber)) ∞
        (fun y => TotalSpace.mk' TensorFiber y (H y)) →
      A.InputBound t r (B x) G H →
      (∀ m, A.ShiftedBound 2 m s (P m x) (A.smooth r s G)) ∧
      (∀ m, A.TensorWeightedBound s m (C m x) (A.tensorSmooth r s H)) := by
  classical
  choose DG hDG hg using fun m => A.smoothing_shifted_gain (V := Space) r 2 m
  choose DH hDH hh using fun m => A.tensor_smoothing_bounds r m
  let U := fun m => DG m*((1+(1+∫ y, ‖kernel 0 y‖)^r)+weightedGainConstant r m)
  let V := fun m => DH m*weightedGainConstant r m
  have hker : 0 ≤ ∫ y, ‖kernel 0 y‖ := integral_nonneg (fun _ => norm_nonneg _)
  have hU (m : ℕ) : 0 ≤ U m := by
    have hd := hDG m
    have hg := weightedGainConstant_nonneg r m
    dsimp [U]; positivity
  have hV (m : ℕ) : 0 ≤ V m := mul_nonneg (hDH m) (weightedGainConstant_nonneg r m)
  let P := fun m x => U m*B x
  let C := fun m x => 1+V m*B x
  refine ⟨P,C,fun m => (polynomialBound_const (hU m)).mul hB,
    fun m => (polynomialBound_const zero_le_one).add ((polynomialBound_const (hV m)).mul hB),?_,?_⟩
  · intro m x hx
    have hh := mul_nonneg (hV m) (hB.nonneg hx)
    dsimp [C]; linarith
  · intro x hx G H t s _ht _ht1 hs hs1 hG hH hinput
    have hb := hB.nonneg hx
    have hprefix : A.ShiftedBound 2 0 1 (B x) G := by
      intro i j hj y
      have hj2 : j ≤ 2 := by omega
      have hjr : j ≤ 2+r := by omega
      simpa only [Nat.sub_eq_zero_of_le hj2,pow_zero,one_mul] using hinput.1 i j hjr y
    refine ⟨fun m => hg m G s (B x) hs hs1 hb hG hprefix,?_⟩
    intro m i
    have hzero : A.TensorWeightedBound t 0 (B x) H :=
      fun k => (hinput.2 k).mono_order (Nat.zero_le r)
    apply (((hh m).2 H s t (B x) hs hs1 hb hH hzero) i).mono_const
    change V m*B x ≤ 1+V m*B x
    linarith

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
