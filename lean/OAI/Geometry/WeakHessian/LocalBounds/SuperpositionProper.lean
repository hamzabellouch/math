import Mathlib
import OAI.Geometry.WeakHessian.LocalBounds.ContinuousTimeMarginals
import OAI.Geometry.WeakHessian.Calculus.CompactAnchoredControl
import OAI.Geometry.WeakHessian.Transport.JoinPlanPolish

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped Topology ENNReal NNReal
open Set Filter
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open scoped Topology
open Set MeasureTheory Filter
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
open Set Filter Topology Bornology
open scoped InnerProductSpace
open scoped BoundedContinuousFunction
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal

namespace WeakHessian
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

lemma exists_superposition_proper [ProperSpace X] [TopologicalSpace.SeparableSpace X] [Nonempty X]
    (μ : Time → ProbabilityMeasure X) (hμ : Continuous μ) {C : ℝ} (hC : 0 ≤ C)
    (h : DynamicActionBound (fun t => (μ t : Measure X)) C) :
    ∃ π : ProbabilityMeasure (Curve X),
      (∀ t : Time, (π:Measure (Curve X)).map (fun γ => γ t) = (μ t : Measure X)) ∧
      (∫⁻ γ, kineticAction γ ∂(π:Measure (Curve X))) ≤ ENNReal.ofReal C ∧
      (∀ᵐ γ ∂(π:Measure (Curve X)), IsAC2 γ) ∧
      (∫⁻ γ, ∫⁻ t in Icc (0:ℝ) 1, (metricSpeed γ t)^2 ∂volume ∂(π:Measure (Curve X))) ≤ ENNReal.ofReal C := by
  have hex := fun n => exists_grid_plan_polish n (fun t => (μ t : Measure X)) hC h
  choose πs hπs hgrid haction using hex
  let qs : ℕ → ProbabilityMeasure (Curve X) := fun n => ⟨πs n,hπs n⟩
  have ht : IsTightMeasureSet {((qs n:Measure (Curve X)).map (fun γ => γ timeZero)) | n : ℕ} := by
    apply (isTightMeasureSet_singleton (μ := (μ timeZero : Measure X))).subset
    rintro ν ⟨n,rfl⟩
    exact hgrid n timeZero (zero_mem_dyadicTimes n)
  obtain ⟨π,φ,hφ,hlim,hA,hAC,hS⟩ := exists_action_limit_initial qs ENNReal.ofReal_lt_top haction ht
  have hdense : EqOn (fun t : Time => π.map (fun curve => curve t))
      μ (⋃ n, dyadicTimes n) := by
    intro t ht
    obtain ⟨n,hn⟩ := mem_iUnion.mp ht
    have hevent : ∀ᶠ j in atTop,
        (qs (φ j)).map (fun curve => curve t) = μ t := by
      filter_upwards [eventually_ge_atTop n] with j hj
      apply ProbabilityMeasure.toMeasure_injective
      exact hgrid (φ j) t (monotone_dyadicTimes (hj.trans (hφ.id_le j)) hn)
    have hlimt := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
      (qs ∘ φ) π hlim (continuous_eval_const t)
    exact tendsto_nhds_unique hlimt (tendsto_const_nhds.congr' (hevent.mono fun j hj => hj.symm))
  have heq := Continuous.ext_on dense_dyadicTimes (continuous_time_marginals π) hμ hdense
  refine ⟨π,?_,hA,hAC,hS⟩
  intro t
  exact congrArg ProbabilityMeasure.toMeasure (congrFun heq t)

end WeakHessian

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

end

end OAI
