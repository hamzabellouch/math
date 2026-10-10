import OAI.Geometry.SurfaceImmersion.Correction.CoupledSmoothing
import OAI.Geometry.SurfaceImmersion.Correction.TensorMeanCoordinates

namespace OAI

/-! A fixed low input bound controls the map's C2 smoothing error and
the encoded tensor smoothing error with the same positive scale power. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open WeightedEstimates

local instance inputClosenessFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance inputClosenessFiberSpace : NormedSpace ℝ TensorFiber := inferInstance

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

local instance inputClosenessDualAdd : ∀ p : M,
    ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance inputClosenessDualSmul : ∀ p : M,
    ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance inputClosenessSectionNormed (p : M) :
    NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance inputClosenessSectionSpace (p : M) :
    NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem smoothed_input_closeness (r : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧
      ∀ (G : M → Space) (H : ∀ x : M, CovariantTwoTensor x) (B t s : ℝ),
        0 ≤ B → 0 < s → s ≤ t → t ≤ 1 →
        ContMDiff planeModel spaceModel ∞ G →
        ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
          (fun x => TotalSpace.mk' TensorFiber x (H x)) →
        A.InputBound t r B G H →
        A.WeightedBound 1 2 (D*B*(s/t)^r) (G - A.smooth r s G) ∧
        ∀ x, ‖A.tensorEncode H x - A.tensorEncode (A.tensorSmooth r s H) x‖ ≤ D*B*(s/t)^r := by
  obtain ⟨D,hD,htail⟩ := A.coupled_smoothing_tail r 0
  refine ⟨2*D*tailConstant r,mul_nonneg (mul_nonneg (by norm_num) hD) (tailConstant_nonneg r),?_⟩
  intro G H B t s hB hs hst ht1 hG hH hinput
  have ht : 0 < t := hs.trans_le hst
  have hzero : A.InputBound t 0 B G H := by
    constructor
    · intro i j hj x
      exact hinput.1 i j (by omega) x
    · exact fun i => (hinput.2 i).mono_order (Nat.zero_le r)
  have hb := htail G H s t s B B hs le_rfl hst ht1 hB hB hG hH hinput hzero
  have he : D * tailConstant r * (B * (s/t)^r + B * (s/t)^r) =
      (2*D*tailConstant r)*B*(s/t)^r := by ring
  rw [he] at hb
  have hC : 0 ≤ (2*D*tailConstant r)*B*(s/t)^r :=
    mul_nonneg (mul_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) hD) (tailConstant_nonneg r)) hB)
      (pow_nonneg (div_nonneg hs.le ht.le) r)
  constructor
  · intro i j hj x _hx
    have hh := hb.1 i j (by omega) x
    simpa only [Nat.sub_eq_zero_of_le hj,pow_zero,one_pow,one_mul,
      iteratedFDerivWithin_univ] using hh
  · have hdiff := hH.sub_section (A.tensorSmooth_smooth r hs hH)
    have henc := A.tensorEncode_bound hdiff hs hC hb.2
    intro x
    have hh := henc.norm_le (mem_univ x)
    simpa only [A.tensorEncode_sub,Pi.sub_apply] using hh

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
