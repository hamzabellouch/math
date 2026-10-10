import Mathlib
import OAI.Geometry.WeakHessian.LocalBounds.LipschitzMulDist
import OAI.Geometry.WeakHessian.HeatFlow.ResolventEVI
import OAI.Geometry.WeakHessian.LocalBounds.Confinement

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile65
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianTransport WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}
variable [SigmaFinite m]

lemma RCD.cheegerHeat_comparison_compact {K N : ℝ}
    (hN : 1 < N) (hrcd : RCD m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m) (o : X)
    (h : QuadraticCheegerEnergy m) (u : Lp ℝ 2 m)
    (hun : ∀ᵐ x ∂m,0 ≤ u x) (hmass : ∫ x,u x ∂m = 1)
    {B : ℝ} (hB : 0 ≤ B) (huB : ∀ᵐ x ∂m,|u x| ≤ B)
    {R : ℝ} (hs : ∀ᵐ x ∂m,dist x o > R → u x = 0)
    (μ : ℝ → ProbabilityMeasure X) (hμ : ∀ t,0 ≤ t → (μ t:Measure X) = densityMeasure m (cheegerHeat h t u))
    (ν : ProbabilityMeasure X) (T : ℝ≥0) (hT : 0 < T)
    (hsν : (ν:Measure X) (Metric.closedBall o T)ᶜ = 0)
    {C : ℝ≥0∞} (hCt : C ≠ ∞) (hdν : (ν:Measure X) ≤ C • m)
    {b : ℝ} (hb : 0 ≤ b) :
    (Real.exp (K*b)*quadraticWassersteinSq (μ b:Measure X) (ν:Measure X)-
      quadraticWassersteinSq (μ 0:Measure X) (ν:Measure X))/2 ≤
      ∫ t in 0..b,Real.exp (K*t)*(entropyReal m (ν:Measure X)-entropyReal m (μ t:Measure X)) := by
  obtain ⟨a,ha,hi,h2,hD,hh,hhi,hW⟩ := hrcd.1.exists_comparison_confinement hN hfull hfin o
  let L : ℝ≥0 := ‖a‖₊
  let ts : ℕ → ℝ := fun n => (1/((n:ℝ)+1))/(2*((L:ℝ)^2+1))
  have hpos (n : ℕ) : 0 < ts n := by dsimp only [ts]; positivity
  have hlim : Tendsto ts atTop (𝓝 0) := by
    have H := tendsto_one_div_add_atTop_nhds_zero_nat.div_const (2*((L:ℝ)^2+1))
    simpa only [zero_div] using H
  have hsmall (n : ℕ) : ts n*(L:ℝ)^2 ≤ 1/2 := by
    have hden : 0 < 2*((L:ℝ)^2+1) := by positivity
    have h1 : 1/((n:ℝ)+1) ≤ 1 := (div_le_one (by positivity)).mpr (by have := Nat.cast_nonneg (α := ℝ) n; linarith)
    dsimp only [ts]
    rw [div_mul_eq_mul_div,div_le_iff₀ hden]
    nlinarith [mul_le_mul_of_nonneg_right h1 (sq_nonneg (L:ℝ))]
  exact hrcd.cheegerHeat_comparison_resolvents hN hfull hfin o h u hun
    (integrable_of_integral_eq_one hmass) hmass hB huB
    (lipschitz_mul_dist o a) (memLp_exp_weight_of_supported u o ha.le hs)
    h2 hD hi hh hhi μ hμ ν T hT hsν hCt hdν (hW T).1 (hW T).2 hpos hsmall hlim hb
end WeakHessian

end
end InlinedFile65

end OAI
