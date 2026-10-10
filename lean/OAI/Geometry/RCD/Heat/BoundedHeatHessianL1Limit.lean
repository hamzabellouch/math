import OAI.Geometry.RCD.Heat.BoundedHeatDiagonalHessianDifference
import OAI.Geometry.RCD.Sobolev.WeightedGradientPairDifference
import OAI.Geometry.RCD.Metric.L1SequentialLimit

namespace OAI

/-! # The local Hessian L1 limit along a strong gradient approximation -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology NNReal ENNReal
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
  (hn : 2 ≤ n) (p : X) [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]

include hn in
theorem bounded_heat_hessian_L1_limit (hK : K ≤ 0)
    (f : Lp ℝ 2 (hausdorff n X)) (A : ℝ≥0)
    (hf : ∀ᵐ x ∂hausdorff n X, |f x| ≤ A) {a r : ℝ} (ha : 0 < a) (hr : 0 < r)
    (u : ℕ → SobolevSpace (hausdorff n X) hX.quadratic)
    (d : ℕ → Lp ℝ 2 (hausdorff n X))
    (hd : ∀ k, IsWeakLaplacian (hausdorff n X) hX.quadratic (u k) (d k))
    (U : ℕ → X → ℝ) (L B : ℕ → ℝ≥0)
    (hU : ∀ k, LipschitzWith (L k) (U k))
    (hu : ∀ k, SobolevSpace.toLp (hausdorff n X) hX.quadratic (u k) =ᵐ[hausdorff n X] U k)
    (huB : ∀ k, ∀ᵐ x ∂hausdorff n X, |SobolevSpace.toLp (hausdorff n X) hX.quadratic (u k) x| ≤ B k)
    {P : ℝ} (hP : 0 ≤ P)
    (hgu : ∀ k, ∀ᵐ x ∂(hausdorff n X).restrict (closedBall p r),
      localGamma (hausdorff n X) hX.quadratic (u k) (u k) x ≤ P)
    (φ : X → ℝ) (hφ : AEStronglyMeasurable φ (hausdorff n X)) (D : ℝ≥0)
    (hD : ∀ᵐ x ∂hausdorff n X, |φ x| ≤ D)
    (hzero : ∀ x ∉ closedBall p r, φ x = 0)
    (v : SobolevSpace (hausdorff n X) hX.quadratic)
    (henergy : Tendsto (fun k => weightedGamma (hausdorff n X) hX.quadratic
      (fun x => (φ x)^2) (u k-v) (u k-v)) atTop (𝓝 0))
    (WU UU : ℕ → SobolevSpace (hausdorff n X) hX.quadratic)
    (hWU : ∀ k, SobolevSpace.toLp (hausdorff n X) hX.quadratic (WU k)
      =ᵐ[(hausdorff n X).restrict (closedBall p r)]
        localGamma (hausdorff n X) hX.quadratic (heatSobolev (hausdorff n X) hX.quadratic a ha f) (u k))
    (hUU : ∀ k, SobolevSpace.toLp (hausdorff n X) hX.quadratic (UU k)
      =ᵐ[(hausdorff n X).restrict (closedBall p r)] localGamma (hausdorff n X) hX.quadratic (u k) (u k)) :
    let m := hausdorff n X
    let q := hX.quadratic
    let w := heatSobolev m q a ha f
    ∃ H : Lp ℝ 1 (m.restrict (closedBall p r)),
      Tendsto (fun k => ∫ x in closedBall p r,
        |φ x*localHessianAction m q w (u k) (u k) (WU k) (WU k) (UU k) x-H x| ∂m)
        atTop (𝓝 0) := by
  intro m q w
  let F k x := φ x*localHessianAction m q w (u k) (u k) (WU k) (WU k) (UU k) x
  have hFi (k : ℕ) : Integrable (F k) (m.restrict (closedBall p r)) :=
    ((localHessianAction_integrable m q w (u k) (u k) (WU k) (WU k) (UU k)).bdd_mul hφ
      (hD.mono fun x hx => by simpa only [Real.norm_eq_abs] using hx)).integrableOn
  apply exists_L1_limit_of_pairwise (m.restrict (closedBall p r)) F hFi
  intro i j hi hj
  have hφ2 : AEStronglyMeasurable (fun x => (φ x)^2) m := hφ.pow 2
  have hD2 : ∀ᵐ x ∂m, ‖(φ x)^2‖ ≤ (D^2 : ℝ≥0) := by
    filter_upwards [hD] with x hx
    simpa only [norm_pow,Real.norm_eq_abs,NNReal.coe_pow] using
      pow_le_pow_left₀ (abs_nonneg _) hx 2
  have hp := weighted_gradient_pair_tendsto_zero m q hφ2 hD2
    (Eventually.of_forall fun x => sq_nonneg (φ x)) (u ∘ i) (u ∘ j) v
    (henergy.comp hi) (henergy.comp hj)
  have hh := hX.bounded_heat_diagonal_hessian_difference hn p hK f A hf ha hr
    (u ∘ i) (u ∘ j) (d ∘ i) (d ∘ j) (fun k => hd (i k)) (fun k => hd (j k))
    (U ∘ i) (U ∘ j) (L ∘ i) (L ∘ j) (B ∘ i) (B ∘ j)
    (fun k => hU (i k)) (fun k => hU (j k)) (fun k => hu (i k)) (fun k => hu (j k))
    (fun k => huB (i k)) (fun k => huB (j k)) hP (fun k => hgu (i k)) (fun k => hgu (j k))
    φ hφ D hD hzero hp (WU ∘ i) (WU ∘ j) (UU ∘ i) (UU ∘ j)
    (fun k => hWU (i k)) (fun k => hWU (j k)) (fun k => hUU (i k)) (fun k => hUU (j k))
  apply hh.congr'
  refine Eventually.of_forall fun k => integral_congr_ae (Eventually.of_forall fun x => ?_)
  dsimp only [F,Function.comp_apply]
  rw [mul_sub]

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
