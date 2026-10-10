import Mathlib
import OAI.Geometry.WeakHessian.LocalBounds.LipschitzMulDist
import OAI.Geometry.WeakHessian.LocalBounds.Confinement
import OAI.Geometry.WeakHessian.HeatFlow.HeatContraction

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile74
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianTransport
open scoped Topology ENNReal NNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}
variable [SigmaFinite m]

lemma RCD.cheegerHeat_contraction_compact {K N : ℝ}
    (hN : 1 < N) (hrcd : RCD m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m) (o : X)
    (h : QuadraticCheegerEnergy m) (u v : Lp ℝ 2 m)
    (hun : ∀ᵐ x ∂m,0 ≤ u x) (hvn : ∀ᵐ x ∂m,0 ≤ v x)
    (hum : ∫ x,u x ∂m = 1) (hvm : ∫ x,v x ∂m = 1)
    {B C R S : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C)
    (huB : ∀ᵐ x ∂m,|u x| ≤ B) (hvC : ∀ᵐ x ∂m,|v x| ≤ C)
    (hsu : ∀ᵐ x ∂m,dist x o > R → u x = 0) (hsv : ∀ᵐ x ∂m,dist x o > S → v x = 0)
    (μ ν : ℝ → ProbabilityMeasure X)
    (hμ : ∀ t,0 ≤ t → (μ t:Measure X) = densityMeasure m (cheegerHeat h t u))
    (hν : ∀ t,0 ≤ t → (ν t:Measure X) = densityMeasure m (cheegerHeat h t v))
    {b : ℝ} (hb : 0 ≤ b) :
    Real.exp (2*K*b)*quadraticWassersteinSq (μ b:Measure X) (ν b:Measure X) ≤
      quadraticWassersteinSq (μ 0:Measure X) (ν 0:Measure X) := by
  obtain ⟨a,ha,hi,h2,hD,hh,hhi,hW⟩ := hrcd.1.exists_comparison_confinement hN hfull hfin o
  exact hrcd.cheegerHeat_contraction_weighted hN hfull hfin o h u v hun hvn hum hvm hB hC huB hvC
    (lipschitz_mul_dist o a) (memLp_exp_weight_of_supported u o ha.le hsu)
    (memLp_exp_weight_of_supported v o ha.le hsv) h2 hD hi hh hhi hW μ ν hμ hν hb
end WeakHessian

end
end InlinedFile74

end OAI
