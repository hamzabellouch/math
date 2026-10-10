import OAI.Geometry.SurfaceImmersion.Correction.PolynomialBudgetAlgebra
import OAI.Geometry.SurfaceImmersion.Geometry.TensorDecodedBounds

namespace OAI


/-! One polynomial profile for all actual grid amplitudes, before the variable family. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial PhaseMean RealModes
local instance polynomialTensorReadFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance polynomialTensorReadFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance polynomialTensorReadDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance polynomialTensorReadDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance polynomialTensorReadSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance polynomialTensorReadSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)


theorem polynomial_tensor_read_budget (B : ℕ → ℝ → ℝ)
    (hB : ∀ m, HasPolynomialBound (B m)) :
    ∃ R : ℕ → ℝ → ℝ, (∀ m, HasPolynomialBound (R m)) ∧
      (∀ m x, 1 ≤ x → 1 ≤ R m x ∧ B m x ≤ R m x) ∧
    ∀ x : ℝ, 1 ≤ x → ∀ s : ℝ, 0 < s → s ≤ 1 →
    ∀ u : ∀ y : M, CovariantTwoTensor y,
      ContMDiff planeModel (planeModel.prod 𝓘(ℝ,TensorFiber)) ∞
        (fun y => TotalSpace.mk' TensorFiber y (u y)) →
      (∀ m, A.TensorWeightedBound s m (B m x) u) →
      ∀ i m, WeightedEstimates.WeightedBound univ s m (R m x) (A.tensorPlaneRead i u) := by
  classical
  choose D hD hread using A.tensorPlaneRead_decode_bound
  let R := fun m x => 1+B m x+D m*B m x
  have hR (m : ℕ) : HasPolynomialBound (R m) :=
    ((polynomialBound_const zero_le_one).add (hB m)).add
      ((polynomialBound_const (zero_le_one.trans (hD m))).mul (hB m))
  have hB0 (m : ℕ) (x : ℝ) (hx : 1 ≤ x) : 0 ≤ B m x := by
    obtain ⟨_,_,_,hh⟩ := hB m
    exact (hh x hx).1
  refine ⟨R,hR,?_,?_⟩
  · intro m x hx
    have hb := hB0 m x hx
    have hd := zero_le_one.trans (hD m)
    dsimp [R]
    constructor <;> nlinarith
  · intro x hx s hs hs1 u hu hb i m
    have he := A.tensorEncode_bound hu hs (hB0 m x hx) (hb m)
    have hh := hread m i (A.tensorEncode u) s (B m x) hs hs1 (hB0 m x hx)
      (A.tensorEncode_smooth hu) he
    rw [A.tensorDecode_encode] at hh
    apply hh.mono_const
    dsimp [R]
    linarith [hB0 m x hx]

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
