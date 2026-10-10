import OAI.Geometry.SurfaceImmersion.Correction.TensorFiniteMean
import OAI.Geometry.SurfaceImmersion.Correction.PolynomialMeanThreshold

namespace OAI

/-! An explicit polynomial threshold for the actual global tensor iteration. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open PhaseMean RealModes WeightedEstimates FiniteMean
open JetPolynomial (Base)
local instance polynomialTensorMeanFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance polynomialTensorMeanFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance polynomialTensorMeanDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance polynomialTensorMeanDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance polynomialTensorMeanSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance polynomialTensorMeanSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem polynomial_tensor_mean_threshold (L : ℕ) (p : ℕ → ℕ) (C : ℕ → ℝ)
    (G H : ℕ → ℝ → ℝ) (hC : ∀ m, 0 ≤ C m)
    (hG : ∀ m, HasPolynomialBound (G m)) (hH : ∀ m, HasPolynomialBound (H m)) (steps : ℕ) :
    ∃ d : ℕ, ∃ E : ℝ, 1 ≤ E ∧ ∀ x : ℝ, 1 ≤ x →
      ∀ {s : ℝ}, 0 < s → ∀ reference f : ∀ y : M, CovariantTwoTensor y,
      ContMDiff planeModel (planeModel.prod 𝓘(ℝ,TensorFiber)) ∞
        (fun y => TotalSpace.mk' TensorFiber y (f y)) →
      ∀ r₀ r : ℝ, r₀ < r →
      (∀ y, ‖A.tensorEncode f y-A.tensorEncode reference y‖ ≤ r₀) →
      (∀ m, 1 ≤ H m x) → (∀ m, A.TensorWeightedBound s m (H m x) f) →
      ∀ η : ℝ, 0 < η → η ≤ min 1 ((r-r₀)/(2*(E*x^d))) →
      ∀ T : (∀ y : M, CovariantTwoTensor y) → ∀ y : M, CovariantTwoTensor y,
      MeanBounds univ s (A.tensorEncode reference) r L
        (rescaledMean η (A.tensorMeanOperator T))
        (polynomialMeanProfile p C (fun m => G m x))
        (polynomialMeanProfile p C (fun m => G m x)) →
      ∀ j ≤ steps,
        ContMDiff planeModel (planeModel.prod 𝓘(ℝ,TensorFiber)) ∞
          (fun y => TotalSpace.mk' TensorFiber y (A.tensorMeanTrial f T j y)) ∧
        InTrialBall univ (A.tensorEncode reference) r (A.tensorEncode (A.tensorMeanTrial f T j)) ∧
        (∀ m, A.TensorWeightedBound s m (polynomialMeanSize L p C G H j m x)
          (A.tensorMeanTrial f T j)) ∧
        (∀ m, A.TensorWeightedBound s m (polynomialMeanDifference L p C G H j m x*η^(j+1))
          (A.tensorMeanTrial f T j+T (A.tensorMeanTrial f T j)-f)) := by
  obtain ⟨d,E,hE,hvalue⟩ := polynomialMean_threshold_budget L p C G H hC hG hH steps
  refine ⟨d,E,hE,?_⟩
  intro x hx s hs reference f hf r₀ r hgap hnear hH1 hbound η hη hsmall T hT j hj
  have henc := A.tensorEncode_smooth hf
  have hh := finite_substitution_with_threshold uniqueDiffOn_univ hs.le hgap hT hH1 henc.contDiffOn
    (fun y _ => hnear y)
    (fun m => A.tensorEncode_bound hf hs (zero_le_one.trans (hH1 m)) (hbound m)) steps
    (mul_pos (zero_lt_one.trans_le hE) (pow_pos (zero_lt_one.trans_le hx) d)) (hvalue x hx)
  obtain ⟨ha,hb,hc,hd⟩ := hh.2 η hη hsmall j hj
  rw [trial_rescaledMean hη.ne'] at ha hb hc hd
  rw [rescaledMean_self hη.ne'] at hd
  have htrial : ContDiff ℝ ∞ (fixedTrial (A.tensorEncode f) (A.tensorMeanOperator T) j) :=
    contDiffOn_univ.mp ha
  have hη1 : η ≤ 1 := hsmall.trans (min_le_left _ _)
  have hmean : ContDiff ℝ ∞ (A.tensorMeanOperator T
      (fixedTrial (A.tensorEncode f) (A.tensorMeanOperator T) j)) := by
    have h := hT.smooth η hη hη1 _ ha hb
    rw [rescaledMean_self hη.ne'] at h
    exact contDiffOn_univ.mp h
  have hres : ContDiff ℝ ∞ (A.tensorEncode
      (A.tensorMeanTrial f T j+T (A.tensorMeanTrial f T j)-f)) := by
    rw [A.tensorEncode_meanResidual]
    exact (htrial.add hmean).sub henc
  refine ⟨A.tensorDecode_smooth htrial,?_,?_,?_⟩
  · rw [A.tensorEncode_meanTrial]
    exact hb
  · intro m
    apply A.tensorBound_of_encode (by rw [A.tensorEncode_meanTrial]; exact htrial) hs.le
      (zero_le_one.trans (sizeBound_ge_one hH1 hT.B_pos j m))
    rw [A.tensorEncode_meanTrial]
    exact hc m
  · intro m
    apply A.tensorBound_of_encode hres hs.le
      (mul_nonneg (differenceBound_nonneg hH1 hT.B_pos hT.K_pos j m) (pow_nonneg hη.le _))
    rw [A.tensorEncode_meanResidual]
    exact hd m

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
