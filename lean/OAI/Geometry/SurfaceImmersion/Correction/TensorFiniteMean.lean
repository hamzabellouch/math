import OAI.Geometry.SurfaceImmersion.Correction.TensorMeanIteration

namespace OAI

/-! Finite derivative-losing mean substitution on global surface tensors.
The actual section iterates are recovered exactly from their atlas encoding. -/
noncomputable section
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold Bundle WeightedEstimates FiniteMean
open JetPolynomial (Base)

local instance finiteMeanModelNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance finiteMeanModelSpace : NormedSpace ℝ TensorFiber := inferInstance

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

local instance finiteMeanDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance finiteMeanDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))

local instance finiteMeanSectionTensorNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance finiteMeanSectionTensorSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem tensor_finite_mean_substitution_uniform {r₀ r : ℝ} (hgap : r₀ < r)
    {L : ℕ} {B K : ℕ → ℝ → ℝ} {C : ℕ → ℝ} (hC : ∀ m, 1 ≤ C m)
    (steps : ℕ) :
    ∃ η₀ : ℝ, 0 < η₀ ∧ η₀ ≤ 1 ∧ ∀ s : ℝ, 0 < s →
      ∀ reference H : ∀ x : M, CovariantTwoTensor x,
      ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
        (fun x => TotalSpace.mk' TensorFiber x (H x)) →
      (∀ x, ‖A.tensorEncode H x - A.tensorEncode reference x‖ ≤ r₀) →
      (∀ m, A.TensorWeightedBound s m (C m) H) →
      ∀ η : ℝ, 0 < η → η ≤ η₀ →
      ∀ T : (∀ x : M, CovariantTwoTensor x) → ∀ x : M, CovariantTwoTensor x,
      MeanBounds univ s (A.tensorEncode reference) r L
        (rescaledMean η (A.tensorMeanOperator T)) B K →
      ∀ j ≤ steps,
        ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
          (fun x => TotalSpace.mk' TensorFiber x (A.tensorMeanTrial H T j x)) ∧
        InTrialBall univ (A.tensorEncode reference) r (A.tensorEncode (A.tensorMeanTrial H T j)) ∧
        (∀ m, A.TensorWeightedBound s m (sizeBound L C B j m) (A.tensorMeanTrial H T j)) ∧
        (∀ m, A.TensorWeightedBound s m (differenceBound L C B K j m * η ^ (j + 1))
          (A.tensorMeanTrial H T j + T (A.tensorMeanTrial H T j) - H)) := by
  obtain ⟨η₀,hη₀,hη₁,ht⟩ := finite_substitution_uniform_inputs
    (E := Base) (F := A.centers → TensorFiber) (B := B) (K := K) hgap hC steps
  refine ⟨η₀,hη₀,hη₁,?_⟩
  intro s hs reference H hH hH0 hbH η hη hsmall T hm j hj
  have henc := A.tensorEncode_smooth hH
  obtain ⟨ha,hb,hc,hd⟩ := ht univ uniqueDiffOn_univ s hs.le
    (A.tensorEncode reference) (A.tensorEncode H) henc.contDiffOn (fun x _ => hH0 x)
    (fun m => A.tensorEncode_bound hH hs (zero_le_one.trans (hC m)) (hbH m))
    _ hm η hη hsmall j hj
  rw [trial_rescaledMean hη.ne'] at ha hb hc hd
  rw [rescaledMean_self hη.ne'] at hd
  have htrial : ContDiff ℝ ∞ (fixedTrial (A.tensorEncode H) (A.tensorMeanOperator T) j) :=
    contDiffOn_univ.mp ha
  have hmean : ContDiff ℝ ∞ (A.tensorMeanOperator T
      (fixedTrial (A.tensorEncode H) (A.tensorMeanOperator T) j)) := by
    have hh := hm.smooth η hη (hsmall.trans hη₁) _ ha hb
    rw [rescaledMean_self hη.ne'] at hh
    exact contDiffOn_univ.mp hh
  have hres : ContDiff ℝ ∞ (A.tensorEncode
      (A.tensorMeanTrial H T j + T (A.tensorMeanTrial H T j) - H)) := by
    rw [A.tensorEncode_meanResidual]
    exact (htrial.add hmean).sub henc
  refine ⟨A.tensorDecode_smooth htrial,?_,?_,?_⟩
  · rw [A.tensorEncode_meanTrial]
    exact hb
  · intro m
    apply A.tensorBound_of_encode (by rw [A.tensorEncode_meanTrial]; exact htrial) hs.le
      (zero_le_one.trans (sizeBound_ge_one hC hm.B_pos j m))
    rw [A.tensorEncode_meanTrial]
    exact hc m
  · intro m
    apply A.tensorBound_of_encode hres hs.le
      (mul_nonneg (differenceBound_nonneg hC hm.B_pos hm.K_pos j m) (pow_nonneg hη.le _))
    rw [A.tensorEncode_meanResidual]
    exact hd m

theorem tensor_finite_mean_substitution {s : ℝ} (hs : 0 < s)
    {reference H : ∀ x : M, CovariantTwoTensor x} {r₀ r : ℝ} (hgap : r₀ < r)
    {L : ℕ} {B K : ℕ → ℝ → ℝ} {C : ℕ → ℝ} (hC : ∀ m, 1 ≤ C m)
    (hH : ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
      (fun x => TotalSpace.mk' TensorFiber x (H x)))
    (hH0 : ∀ x, ‖A.tensorEncode H x - A.tensorEncode reference x‖ ≤ r₀)
    (hbH : ∀ m, A.TensorWeightedBound s m (C m) H) (steps : ℕ) :
    ∃ η₀ : ℝ, 0 < η₀ ∧ η₀ ≤ 1 ∧ ∀ η : ℝ, 0 < η → η ≤ η₀ →
      ∀ T : (∀ x : M, CovariantTwoTensor x) → ∀ x : M, CovariantTwoTensor x,
      MeanBounds univ s (A.tensorEncode reference) r L
        (rescaledMean η (A.tensorMeanOperator T)) B K →
      ∀ j ≤ steps,
        ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
          (fun x => TotalSpace.mk' TensorFiber x (A.tensorMeanTrial H T j x)) ∧
        InTrialBall univ (A.tensorEncode reference) r (A.tensorEncode (A.tensorMeanTrial H T j)) ∧
        (∀ m, A.TensorWeightedBound s m (sizeBound L C B j m) (A.tensorMeanTrial H T j)) ∧
        (∀ m, A.TensorWeightedBound s m (differenceBound L C B K j m * η ^ (j + 1))
          (A.tensorMeanTrial H T j + T (A.tensorMeanTrial H T j) - H)) := by
  obtain ⟨η₀,hη₀,hη₁,ht⟩ := A.tensor_finite_mean_substitution_uniform
    (B := B) (K := K) hgap hC steps
  exact ⟨η₀,hη₀,hη₁,ht s hs reference H hH hH0 hbH⟩

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
