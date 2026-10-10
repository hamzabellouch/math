import Mathlib
import OAI.Geometry.WeakHessian.LocalBounds.CostMetric

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile63
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianTransport
open scoped Topology ENNReal NNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X]

lemma quadraticWassersteinSq_tendsto_zero_of_tests {ι : Type*} {l : Filter ι}
    (μ : ProbabilityMeasure X) (μs : ι → ProbabilityMeasure X) (ξ : ℕ → ProbabilityMeasure X) (o : X)
    (hμ : Integrable (fun x => dist x o^2) (μ:Measure X))
    (hμs : ∀ i,Integrable (fun x => dist x o^2) (μs i:Measure X))
    (hξ : ∀ n,Integrable (fun x => dist x o^2) (ξ n:Measure X))
    (hT : Tendsto (fun n => quadraticWassersteinSq (μ:Measure X) (ξ n:Measure X)) atTop (𝓝 0))
    (hTs : ∀ n,Tendsto (fun i => quadraticWassersteinSq (μs i:Measure X) (ξ n:Measure X)) l
      (𝓝 (quadraticWassersteinSq (μ:Measure X) (ξ n:Measure X)))) :
    Tendsto (fun i => quadraticWassersteinSq (μ:Measure X) (μs i:Measure X)) l (𝓝 0) := by
  have hS : Tendsto (fun n => Real.sqrt (quadraticWassersteinSq (μ:Measure X) (ξ n:Measure X))) atTop (𝓝 0) := by
    simpa only [Real.sqrt_zero] using hT.sqrt
  have hS' : Tendsto (fun i => Real.sqrt (quadraticWassersteinSq (μ:Measure X) (μs i:Measure X))) l (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨n,hn⟩ := (hS.eventually_lt_const (by linarith : (0:ℝ)<ε/4)).exists
    have H := (hTs n).sqrt.eventually_lt_const (show Real.sqrt (quadraticWassersteinSq (μ:Measure X) (ξ n:Measure X)) < ε/2 by linarith)
    filter_upwards [H] with i hi
    have ht := quadraticWassersteinSq_triangle μ (ξ n) (μs i) o hμ (hξ n) (hμs i)
    rw [quadraticWassersteinSq_comm (ξ n:Measure X) (μs i:Measure X)] at ht
    simpa only [Real.dist_eq,sub_zero,abs_of_nonneg (Real.sqrt_nonneg _)] using (show Real.sqrt (quadraticWassersteinSq (μ:Measure X) (μs i:Measure X)) < ε by linarith)
  have H := hS'.pow 2
  have hn (p q : Measure X) : 0 ≤ quadraticWassersteinSq p q := ENNReal.toReal_nonneg
  simpa only [Real.sq_sqrt (hn _ _),zero_pow (by norm_num : (2:ℕ) ≠ 0)] using H

lemma quadraticWassersteinSq_tendsto_pair {ι : Type*} {l : Filter ι}
    (μ ν : ProbabilityMeasure X) (μs νs : ι → ProbabilityMeasure X) (o : X)
    (hμ : Integrable (fun x => dist x o^2) (μ:Measure X))
    (hν : Integrable (fun x => dist x o^2) (ν:Measure X))
    (hμs : ∀ i,Integrable (fun x => dist x o^2) (μs i:Measure X))
    (hνs : ∀ i,Integrable (fun x => dist x o^2) (νs i:Measure X))
    (hTμ : Tendsto (fun i => quadraticWassersteinSq (μ:Measure X) (μs i:Measure X)) l (𝓝 0))
    (hTν : Tendsto (fun i => quadraticWassersteinSq (ν:Measure X) (νs i:Measure X)) l (𝓝 0)) :
    Tendsto (fun i => quadraticWassersteinSq (μs i:Measure X) (νs i:Measure X)) l
      (𝓝 (quadraticWassersteinSq (μ:Measure X) (ν:Measure X))) := by
  have hS : Tendsto (fun i => Real.sqrt (quadraticWassersteinSq (μ:Measure X) (μs i:Measure X))+
      Real.sqrt (quadraticWassersteinSq (ν:Measure X) (νs i:Measure X))) l (𝓝 0) := by
    simpa only [Real.sqrt_zero,add_zero] using hTμ.sqrt.add hTν.sqrt
  have hpair : Tendsto (fun i => Real.sqrt (quadraticWassersteinSq (μs i:Measure X) (νs i:Measure X))) l
      (𝓝 (Real.sqrt (quadraticWassersteinSq (μ:Measure X) (ν:Measure X)))) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    filter_upwards [hS.eventually_lt_const hε] with i hi
    have h1 := quadraticWassersteinSq_triangle (μs i) μ (νs i) o (hμs i) hμ (hνs i)
    have h2 := quadraticWassersteinSq_triangle μ ν (νs i) o hμ hν (hνs i)
    have h3 := quadraticWassersteinSq_triangle μ (μs i) ν o hμ (hμs i) hν
    have h4 := quadraticWassersteinSq_triangle (μs i) (νs i) ν o (hμs i) (hνs i) hν
    rw [quadraticWassersteinSq_comm (μs i:Measure X) (μ:Measure X)] at h1
    rw [quadraticWassersteinSq_comm (νs i:Measure X) (ν:Measure X)] at h4
    rw [Real.dist_eq]
    apply lt_of_le_of_lt _ hi
    apply abs_le.mpr
    constructor <;> linarith
  have H := hpair.pow 2
  have hn (p q : Measure X) : 0 ≤ quadraticWassersteinSq p q := ENNReal.toReal_nonneg
  simpa only [Real.sq_sqrt (hn _ _)] using H
end WeakHessian

end
end InlinedFile63

end OAI
