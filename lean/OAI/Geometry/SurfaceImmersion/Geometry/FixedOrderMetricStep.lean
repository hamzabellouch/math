import OAI.Geometry.SurfaceImmersion.Correction.ActualSmoothedStep
import OAI.Geometry.SurfaceImmersion.Geometry.NormalizedStepEnvelope
import OAI.Geometry.SurfaceImmersion.Geometry.FixedOrderThreshold
import OAI.Geometry.SurfaceImmersion.Geometry.ExactScaleOrdering

namespace OAI

/-! A genuine correction at the paper's fixed-order scales. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean PhaseGeometry WeightedEstimates FiniteMean
local instance fixedStepFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance fixedStepFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance fixedStepDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance fixedStepDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance fixedStepSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance fixedStepSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
namespace MetricGoodPhaseData
variable {g : SmoothMetric M} {F : M → Space}

/-- At each fixed order one threshold permits either holding or increasing
the order. The actual correction has small low derivatives and an affine
bound for the new normalized metric error in every higher input norm. -/
theorem fixed_order_metric_step (d : MetricGoodPhaseData g F)
    (hF : ContMDiff planeModel spaceModel ∞ F) (k : ℕ) (hk : 10 ≤ k)
    {B₀ : ℝ} (hB₀ : 0 ≤ B₀) :
    ∃ a ρ ε : ℝ, 0 < a ∧ 0 < ρ ∧ 0 < ε ∧ ε ≤ 1 ∧
    ∃ B L : ℕ → ℝ, (∀ m, 0 ≤ B m) ∧ (∀ m, 0 ≤ L m) ∧
    ∀ (G : M → Space), ContMDiff planeModel spaceModel ∞ G →
    ∀ t : ℝ, 0 < t → t < ε → ∀ j : ℕ, k ≤ j → j ≤ k+1 →
      d.A.InputBound t (40*(k+1)) B₀ G
        (normalizedTensorDefect g.inner (t^(k : ℝ)) G) →
      d.A.WeightedBound 1 2 (ρ/4) (G-F) →
      (∀ x, ‖d.A.tensorEncode (normalizedTensorDefect g.inner (t^(k : ℝ)) G) x -
        d.A.tensorEncode g.inner x‖ ≤ a/8) →
      ∃ U : M → Space, ContMDiff planeModel spaceModel ∞ U ∧
        (∀ m, d.A.WeightedBound (t^(6/5 : ℝ)) m
          (B m*(t^(k : ℝ)*t^(6/5 : ℝ))) U) ∧
        (∀ m ≤ k/2, d.A.WeightedBound 1 m (ρ*t) U) ∧
        ∀ m C, 0 ≤ C → d.A.InputBound t m C G
          (normalizedTensorDefect g.inner (t^(k : ℝ)) G) →
          d.A.TensorWeightedBound (t^(6/5 : ℝ)) m
            (L m*(1+B₀+C)*t^(1/5 : ℝ))
            (normalizedTensorDefect g.inner (t^((6/5 : ℝ)*(j : ℝ))) (G+U)-g.inner) := by
  classical
  let r := 40*(k+1)
  obtain ⟨a,ρ,η,D,K,ha,hρ,hη,_,hD,hK,B,T,Dm,Em,hB,hT,hDm,hEm,hstep⟩ :=
    d.actual_smoothed_step hF r r hB₀
  obtain ⟨ε,hε,hε1,hthreshold⟩ :=
    ExactCorrection.fixed_order_threshold_hold_advance k hk ρ a η D B₀ K hρ ha hη hD hB₀ hK B
  let L := fun m => Dm m*tailConstant r + Em m*B (m+1)*(Dm m*tailConstant r) + 2*T m
  have hL (m : ℕ) : 0 ≤ L m := by
    dsimp [L]
    exact add_nonneg (add_nonneg
      (mul_nonneg (hDm m) (tailConstant_nonneg r))
      (mul_nonneg (mul_nonneg (hEm m) (hB (m+1)))
        (mul_nonneg (hDm m) (tailConstant_nonneg r))))
      (mul_nonneg (by norm_num) (hT m))
  refine ⟨a,ρ,ε,ha,hρ,hε,hε1,B,L,hB,hL,?_⟩
  intro G hG t ht htε j hkj hjk hinput hnear hmetric
  have ht1 : t ≤ 1 := htε.le.trans hε1
  obtain ⟨hτη,htail,hratio,hlow,hδ'δ,hmin⟩ := hthreshold t ht htε j hkj hjk
  obtain ⟨hminpos,hδ,hτ,hs⟩ := ExactCorrection.exact_scale_positive ht k
  have hδ' : 0 < t^((6/5 : ℝ)*(j : ℝ)) := Real.rpow_pos_of_pos ht _
  obtain ⟨_,hδτ,hτs,hst⟩ := ExactCorrection.exact_scale_order ht ht1 hk
  obtain ⟨U,hU,hUB,herror⟩ := hstep G hG (t^(k : ℝ))
    (t^((6/5 : ℝ)*(j : ℝ))) t (t^(11/10 : ℝ)) (t^(6/5 : ℝ))
    hδ hδ' hδ'δ ht ht1 hs hst hτ hτs hτη hδτ hinput hnear hmetric htail hratio
  refine ⟨U,hU,hUB,?_,?_⟩
  · intro m hm i j hj x hx
    have hb := (hUB j i).deriv_le hτ (le_refl j) hx
    have hh := hb.trans (hlow j (hj.trans hm))
    simpa only [one_pow,one_mul] using hh
  · intro m C hC hCm i
    apply (herror m C hC hCm i).mono_const
    have he : normalizedStepBound r r B₀ (Dm m) (Em m) (B (m+1)) (T m) C
        (t^(k : ℝ)) (t^((6/5 : ℝ)*(j : ℝ)))
        (t^(6/5 : ℝ)) (t^(11/10 : ℝ)) t =
      ((t^((6/5 : ℝ)*(j : ℝ)))^2)⁻¹ *
        (((t^(k : ℝ))^2 + Em m*B (m+1)*t^(k : ℝ)) * (Dm m*tailConstant r) *
          (B₀*(t^(11/10 : ℝ)/t)^r+C*(t^(6/5 : ℝ)/t)^r) +
          T m*(t^(k : ℝ)*(t^(6/5 : ℝ)/t^(11/10 : ℝ))^(r+1)+
            (t^(k : ℝ))^3/t^(6/5 : ℝ))) := by
      unfold normalizedStepBound
      field_simp [hτ.ne']
    rw [he]
    have hden : ((t^((6/5 : ℝ)*(j : ℝ)))^2)⁻¹ ≤
        ((t^((6/5 : ℝ)*((k : ℝ)+1)))^2)⁻¹ := by
      apply (inv_le_inv₀ (sq_pos_of_pos hδ') (sq_pos_of_pos hminpos)).mpr
      nlinarith
    have hdm := hDm m
    have hem := hEm m
    have hbm := hB (m+1)
    have htm := hT m
    have htc := tailConstant_nonneg r
    have hnum : 0 ≤
        (((t^(k : ℝ))^2 + Em m*B (m+1)*t^(k : ℝ)) * (Dm m*tailConstant r) *
          (B₀*(t^(11/10 : ℝ)/t)^r+C*(t^(6/5 : ℝ)/t)^r) +
          T m*(t^(k : ℝ)*(t^(6/5 : ℝ)/t^(11/10 : ℝ))^(r+1)+
            (t^(k : ℝ))^3/t^(6/5 : ℝ))) := by positivity
    exact (mul_le_mul_of_nonneg_right hden hnum).trans
      (ExactCorrection.normalized_step_envelope_nat_succ ht ht1 hk hB₀ hC
        (mul_nonneg (hDm m) (tailConstant_nonneg r)) (hEm m) (hB (m+1)) (hT m))

end MetricGoodPhaseData
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
