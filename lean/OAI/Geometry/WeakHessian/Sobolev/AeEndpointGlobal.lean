import Mathlib
import OAI.Geometry.WeakHessian.LocalBounds.SpeedApprox

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped NNReal
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open scoped Topology
open Set Filter
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open Set Filter Topology Bornology
open scoped InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable

open Set Filter Topology Bornology
open scoped InnerProductSpace


namespace WeakHessian
open MeasureTheory Set Filter

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [Nonempty X] {m : Measure X}

lemma IsLocalWeakUpperGradient.ae_endpoint_le_global {f D : X → ℝ}
    (hD : IsLocalWeakUpperGradient m f D) (hf : AEMeasurable f m)
    {π : Measure (Curve X)} (hπ : IsTestPlan m π) :
    ∀ᵐ γ ∂π, ENNReal.ofReal |f (γ timeOne) - f (γ timeZero)| ≤
      ∫⁻ t in Set.Icc (0 : ℝ) 1, ENNReal.ofReal (D (evalReal γ t)) * metricSpeed γ t := by
  let : IsProbabilityMeasure π := hπ.1
  let o : X := Classical.arbitrary X
  let S (n : ℕ) : Set (Curve X) := Metric.closedBall (ContinuousMap.const Time o) n
  have hS (n : ℕ) : MeasurableSet (S n) := measurableSet_closedBall
  have H (n : ℕ) : ∀ᵐ γ ∂π, γ ∈ S n →
      ENNReal.ofReal |f (γ timeOne)-f (γ timeZero)| ≤
      ∫⁻ t in Icc (0:ℝ) 1, ENNReal.ofReal (D (evalReal γ t))*metricSpeed γ t := by
    apply (ae_restrict_iff' (hS n)).mp
    by_cases hz : π (S n) = 0
    · rw [Measure.restrict_eq_zero.mpr hz]
      simp
    let ρ := (π (S n))⁻¹ • π.restrict (S n)
    have hdom : ρ ≤ (π (S n))⁻¹ • π := by
      change (π (S n))⁻¹ • π.restrict (S n) ≤ (π (S n))⁻¹ • π
      gcongr
      exact Measure.restrict_le_self
    have hp : IsProbabilityMeasure ρ := by
      constructor
      simp only [ρ,Measure.smul_apply,smul_eq_mul,Measure.restrict_apply_univ,
        ENNReal.inv_mul_cancel hz (measure_ne_top _ _)]
    have ht := hπ.of_plan_le_smul hp (ENNReal.inv_lt_top.mpr (pos_iff_ne_zero.mpr hz)) hdom
    have hb : BoundedTracks ρ := by
      refine ⟨o,(n:ℝ)+1,by positivity,?_⟩
      have ha : ∀ᵐ γ ∂ρ, γ ∈ S n := by
        exact Measure.ae_smul_measure (ae_restrict_mem (hS n)) _
      filter_upwards [ha] with γ hγ
      intro t
      have hdist := ContinuousMap.dist_apply_le_dist (f := γ) (g := ContinuousMap.const Time o) t
      exact (hdist.trans hγ).trans (by linarith)
    have HH := hD.ae_endpoint_le hf ht hb
    exact (Measure.ae_ennreal_smul_measure_iff (ENNReal.inv_ne_zero.mpr (measure_ne_top _ _))).mp HH
  filter_upwards [ae_all_iff.mpr H] with γ hγ
  obtain ⟨n,hn⟩ := exists_nat_gt (dist γ (ContinuousMap.const Time o))
  exact hγ n hn.le

lemma IsLocalWeakUpperGradient.integrated_global {f D : X → ℝ}
    (hD : IsLocalWeakUpperGradient m f D) (hf : AEMeasurable f m)
    {π : Measure (Curve X)} (hπ : IsTestPlan m π) :
    (∫⁻ γ, ENNReal.ofReal |f (γ timeOne)-f (γ timeZero)| ∂π) ≤
      ∫⁻ γ, ∫⁻ t in Icc (0:ℝ) 1,
        ENNReal.ofReal (D (evalReal γ t))*metricSpeed γ t ∂volume ∂π :=
  lintegral_mono_ae (hD.ae_endpoint_le_global hf hπ)
end WeakHessian

end

end OAI
