import OAI.Geometry.SurfaceImmersion.Correction.PositiveSmoothingAtlas
import OAI.Geometry.SurfaceImmersion.Atlas.TensorPhaseDifferential

namespace OAI

/-! The normalized atlas gives an actual finite positive primitive family.
The amplitudes are smooth and supported in the original chart supports;
their rank-one tensors sum exactly to the given symmetric tensor. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open PhaseMean PhaseGeometry

local instance positivePrimitiveFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance positivePrimitiveFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]
local instance positivePrimitiveDualAdd : ∀ p : M,
    ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance positivePrimitiveDualSmul : ∀ p : M,
    ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance positivePrimitiveSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance positivePrimitiveSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)

namespace SmoothingAtlas
variable (A : SmoothingAtlas M) (P : A.centers → PhaseBasis)
  (u : ∀ p : M, CovariantTwoTensor p)

def positivePrimitiveAmplitude (a : A.centers × Fin 3) : M → ℝ :=
  A.positiveAtlas.rootPhaseAmplitude a.1 ((P a.1).Q a.2) 1 u

def positivePrimitiveTensor (a : A.centers × Fin 3) (p : M) : CovariantTwoTensor p :=
  (A.positivePrimitiveAmplitude P u a p)^2 •
    A.bundleRestore A.tensorTriv a.1
      (fun _ => fiberFromThree (covectorSquare ((P a.1).ξ a.2))) p

lemma positivePrimitiveAmplitude_nonneg (a : A.centers × Fin 3) (p : M) :
    0 ≤ A.positivePrimitiveAmplitude P u a p := by
  exact mul_nonneg (A.positiveWeight_nonneg a.1 p)
    (div_nonneg (Real.sqrt_nonneg _) zero_le_one)

lemma positivePrimitiveAmplitude_support (a : A.centers × Fin 3) :
    tsupport (A.positivePrimitiveAmplitude P u a) ⊆ tsupport (A.weight a.1) := by
  simpa only [positivePrimitiveAmplitude, A.positiveAtlas_weight_tsupport] using
    A.positiveAtlas.rootPhaseAmplitude_support a.1 ((P a.1).Q a.2) 1 u

lemma positivePrimitiveAmplitude_pos_iff
    (hpos : ∀ i j p, p ∈ tsupport (A.weight i) →
      0 < (P i).Q j (A.tensorChartRead i u (chart (i : M) p)))
    (a : A.centers × Fin 3) (p : M) :
    0 < A.positivePrimitiveAmplitude P u a p ↔ A.weight a.1 p ≠ 0 := by
  constructor
  · intro hp hw
    have hz : A.positivePrimitiveAmplitude P u a p = 0 := by
      simp only [positivePrimitiveAmplitude, rootPhaseAmplitude, positiveAtlas,
        positiveWeight, hw, zero_pow (by decide : 2 ≠ 0), zero_div, zero_mul]
    exact (ne_of_gt hp) hz
  · intro hp
    have hq := hpos a.1 a.2 p (subset_tsupport _ hp)
    exact mul_pos ((A.positiveWeight_pos_iff a.1 p).mpr hp)
      (div_pos (Real.sqrt_pos.mpr hq) zero_lt_one)

lemma positivePrimitiveAmplitude_tsupport
    (hpos : ∀ i j p, p ∈ tsupport (A.weight i) →
      0 < (P i).Q j (A.tensorChartRead i u (chart (i : M) p)))
    (a : A.centers × Fin 3) :
    tsupport (A.positivePrimitiveAmplitude P u a) = tsupport (A.weight a.1) := by
  change closure (Function.support _) = closure (Function.support _)
  congr 1
  ext p
  change A.positivePrimitiveAmplitude P u a p ≠ 0 ↔ A.weight a.1 p ≠ 0
  constructor
  · intro ha
    exact (A.positivePrimitiveAmplitude_pos_iff P u hpos a p).mp
      (lt_of_le_of_ne (A.positivePrimitiveAmplitude_nonneg P u a p) (Ne.symm ha))
  · intro hw
    exact ne_of_gt ((A.positivePrimitiveAmplitude_pos_iff P u hpos a p).mpr hw)

lemma positivePrimitiveTensor_apply (a : A.centers × Fin 3) (p : M)
    (v w : TangentSpace planeModel p) :
    A.positivePrimitiveTensor P u a p v w =
      (A.positivePrimitiveAmplitude P u a p)^2 *
        (show ℝ from mfderiv planeModel 𝓘(ℝ) (atlasPhase (a.1 : M) ((P a.1).ξ a.2)) p v) *
        (show ℝ from mfderiv planeModel 𝓘(ℝ) (atlasPhase (a.1 : M) ((P a.1).ξ a.2)) p w) := by
  by_cases ha : A.positivePrimitiveAmplitude P u a p = 0
  · simp only [positivePrimitiveTensor, ha, zero_pow (by decide : 2 ≠ 0),
      zero_smul, zero_apply]
    let dv : ℝ := mfderiv planeModel 𝓘(ℝ) (atlasPhase (a.1 : M) ((P a.1).ξ a.2)) p v
    let dw : ℝ := mfderiv planeModel 𝓘(ℝ) (atlasPhase (a.1 : M) ((P a.1).ξ a.2)) p w
    change (0 : ℝ) = (0 : ℝ) * dv * dw
    exact ((congrArg (fun x : ℝ => x * dw) (zero_mul dv)).trans (zero_mul dw)).symm
  · have hp := A.positivePrimitiveAmplitude_support P u a (subset_tsupport _ ha)
    change (A.positivePrimitiveAmplitude P u a p)^2 *
      A.bundleRestore A.tensorTriv a.1
        (fun _ => fiberFromThree (covectorSquare ((P a.1).ξ a.2))) p v w = _
    rw [A.tensorRestore_covectorSquare a.1 _ (A.weight_support a.1 hp), A.outer_one a.1 p hp]
    ring

lemma positivePrimitiveTensor_symmetric (a : A.centers × Fin 3) (p : M)
    (v w : TangentSpace planeModel p) :
    A.positivePrimitiveTensor P u a p v w = A.positivePrimitiveTensor P u a p w v := by
  rw [A.positivePrimitiveTensor_apply, A.positivePrimitiveTensor_apply]
  ring

lemma positivePrimitiveTensor_nonneg (a : A.centers × Fin 3) (p : M)
    (v : TangentSpace planeModel p) : 0 ≤ A.positivePrimitiveTensor P u a p v v := by
  rw [A.positivePrimitiveTensor_apply]
  nlinarith [sq_nonneg (A.positivePrimitiveAmplitude P u a p *
    (show ℝ from mfderiv planeModel 𝓘(ℝ) (atlasPhase (a.1 : M) ((P a.1).ξ a.2)) p v))]

theorem sum_positivePrimitiveTensor
    (hu : ∀ p v w, u p v w = u p w v)
    (hpos : ∀ i j p, p ∈ tsupport (A.weight i) →
      0 ≤ (P i).Q j (A.tensorChartRead i u (chart (i : M) p))) (p : M) :
    (∑ a : A.centers × Fin 3, A.positivePrimitiveTensor P u a p) = u p := by
  have hp : ∀ i j p, p ∈ tsupport (A.positiveAtlas.weight i) →
      0 ≤ (P i).Q j (A.positiveAtlas.tensorChartRead i u (chart (i : M) p)) := by
    intro i j p hp
    exact hpos i j p ((A.positiveAtlas_weight_tsupport i) ▸ hp)
  rw [← Finset.univ_product_univ, Finset.sum_product]
  have hd := A.positiveAtlas.global_rootPhase_decomposition P (fun _ _ => 1) u hu
    (fun _ _ => one_ne_zero) hp p
  simp only [one_pow, mul_one] at hd
  convert hd using 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rfl

variable [CompactSpace M]

lemma positivePrimitiveAmplitude_hasCompactSupport (a : A.centers × Fin 3) :
    HasCompactSupport (A.positivePrimitiveAmplitude P u a) :=
  (isClosed_tsupport _).isCompact

lemma positivePrimitiveAmplitude_smooth
    (hu : ContMDiff planeModel (planeModel.prod 𝓘(ℝ,TensorFiber)) ∞
      (fun p => TotalSpace.mk' TensorFiber p (u p)))
    (hpos : ∀ i j p, p ∈ tsupport (A.weight i) →
      0 < (P i).Q j (A.tensorChartRead i u (chart (i : M) p)))
    (a : A.centers × Fin 3) :
    ContMDiff planeModel 𝓘(ℝ) ∞ (A.positivePrimitiveAmplitude P u a) := by
  apply A.positiveAtlas.rootPhaseAmplitude_smooth a.1 ((P a.1).Q a.2) 1 hu
  intro p hp
  exact hpos a.1 a.2 p ((A.positiveAtlas_weight_tsupport a.1) ▸ hp)

lemma positivePrimitiveTensor_smooth
    (hu : ContMDiff planeModel (planeModel.prod 𝓘(ℝ,TensorFiber)) ∞
      (fun p => TotalSpace.mk' TensorFiber p (u p)))
    (hpos : ∀ i j p, p ∈ tsupport (A.weight i) →
      0 < (P i).Q j (A.tensorChartRead i u (chart (i : M) p)))
    (a : A.centers × Fin 3) :
    ContMDiff planeModel (planeModel.prod 𝓘(ℝ,TensorFiber)) ∞
      (fun p => TotalSpace.mk' TensorFiber p (A.positivePrimitiveTensor P u a p)) := by
  exact ((A.positivePrimitiveAmplitude_smooth P u hu hpos a).pow 2).smul_section
    (A.bundleRestore_smooth A.tensorTriv A.tensorTriv_domain a.1 contDiff_const)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
