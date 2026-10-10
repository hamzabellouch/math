import Mathlib
import OAI.Geometry.WeakHessian.HeatFlow.ResolventEVI

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile67
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianTransport WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}
variable [SigmaFinite m]

lemma RCD.cheegerHeat_comparison_weighted {K N : ℝ}
    (hN : 1 < N) (hrcd : RCD m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m) (o : X)
    (h : QuadraticCheegerEnergy m) (u : Lp ℝ 2 m)
    (hun : ∀ᵐ x ∂m,0 ≤ u x) (hmass : ∫ x,u x ∂m = 1)
    {B : ℝ} (hB : 0 ≤ B) (huB : ∀ᵐ x ∂m,|u x| ≤ B)
    {V : X → ℝ} {L : ℝ≥0} (hV : LipschitzWith L V)
    (hU : MemLp (fun x => u x*Real.exp (V x)) 2 m)
    (hdecay : MemLp (fun x => Real.exp (-V x)) 2 m)
    (hD : MemLp (fun x => V x*Real.exp (-V x)) 2 m)
    (hw : Integrable (fun x => Real.exp (-V x)) m)
    (hhalf : MemLp (fun x => Real.exp (-(V x/2))) 2 m)
    (hhalfi : Integrable (fun x => Real.exp (-(V x/2))) m)
    (μ : ℝ → ProbabilityMeasure X) (hμ : ∀ t,0 ≤ t → (μ t:Measure X) = densityMeasure m (cheegerHeat h t u))
    (ν : ProbabilityMeasure X) (T : ℝ≥0) (hT : 0 < T)
    (hsν : (ν:Measure X) (Metric.closedBall o T)ᶜ = 0)
    {C : ℝ≥0∞} (hCt : C ≠ ∞) (hdν : (ν:Measure X) ≤ C • m)
    (hW : MemLp (fun x => (dist x o+T)^2*Real.exp (-V x)) 2 m)
    (hW1 : MemLp (fun x => (dist x o+T)*Real.exp (-V x)) 2 m)
    {b : ℝ} (hb : 0 ≤ b) :
    (Real.exp (K*b)*quadraticWassersteinSq (μ b:Measure X) (ν:Measure X)-
      quadraticWassersteinSq (μ 0:Measure X) (ν:Measure X))/2 ≤
      ∫ t in 0..b,Real.exp (K*t)*(entropyReal m (ν:Measure X)-entropyReal m (μ t:Measure X)) := by
  let ts : ℕ → ℝ := fun n => (1/((n:ℝ)+1))/(2*((L:ℝ)^2+1))
  have hpos (n : ℕ) : 0 < ts n := by dsimp only [ts]; positivity
  have hlim : Tendsto ts atTop (𝓝 0) := by
    have H := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).div_const
      (2*((L:ℝ)^2+1))
    simpa only [zero_div] using H
  have hsmall (n : ℕ) : ts n*(L:ℝ)^2 ≤ 1/2 := by
    have hden : 0 < 2*((L:ℝ)^2+1) := by positivity
    have h1 : 1/((n:ℝ)+1) ≤ 1 :=
      (div_le_one (by positivity)).mpr (le_add_of_nonneg_left (Nat.cast_nonneg n))
    dsimp only [ts]
    rw [div_mul_eq_mul_div,div_le_iff₀ hden]
    nlinarith [mul_le_mul_of_nonneg_right h1 (sq_nonneg (L:ℝ))]
  exact hrcd.cheegerHeat_comparison_resolvents hN hfull hfin o h u hun
    (integrable_of_integral_eq_one hmass) hmass hB huB
    hV hU hdecay hD hw hhalf hhalfi μ hμ ν T hT hsν hCt hdν hW hW1 hpos hsmall hlim hb
end WeakHessian

end
end InlinedFile67

end OAI
