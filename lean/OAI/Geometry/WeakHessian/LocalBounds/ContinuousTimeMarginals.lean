import Mathlib
import OAI.Geometry.WeakHessian.Transport.DynamicActionBound

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
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
open Set Filter Topology Bornology
open scoped InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory

namespace WeakHessian
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

lemma continuous_time_marginals (π : ProbabilityMeasure (Curve X)) :
    Continuous (fun t : Time => π.map (fun curve => curve t)) := by
  rw [ProbabilityMeasure.continuous_iff_forall_continuous_integral]
  intro f
  have H : Continuous (fun t : Time => ∫ γ : Curve X, f (γ t) ∂(π:Measure (Curve X))) := by
    apply continuous_of_dominated
      (bound := fun _ : Curve X => ‖f‖)
    · intro t
      exact (f.continuous.comp (continuous_eval_const t)).aestronglyMeasurable
    · intro t
      exact ae_of_all _ (fun γ => f.norm_coe_le_norm (γ t))
    · exact integrable_const _
    · exact ae_of_all _ (fun γ => f.continuous.comp γ.continuous)
  convert H using 1
  funext t
  exact integral_map (continuous_eval_const t).measurable.aemeasurable f.continuous.aestronglyMeasurable

lemma exists_superposition [CompactSpace X] [Nonempty X]
    (μ : Time → ProbabilityMeasure X) (hμ : Continuous μ) {C : ℝ} (hC : 0 ≤ C)
    (h : DynamicActionBound (fun t => (μ t : Measure X)) C) :
    ∃ π : ProbabilityMeasure (Curve X),
      (∀ t : Time, (π:Measure (Curve X)).map (fun γ => γ t) = (μ t : Measure X)) ∧
      (∫⁻ γ, kineticAction γ ∂(π:Measure (Curve X))) ≤ ENNReal.ofReal C ∧
      (∀ᵐ γ ∂(π:Measure (Curve X)), IsAC2 γ) ∧
      (∫⁻ γ, ∫⁻ t in Icc (0:ℝ) 1, (metricSpeed γ t)^2 ∂volume ∂(π:Measure (Curve X))) ≤ ENNReal.ofReal C := by
  have hex := fun n => exists_grid_plan n (fun t => (μ t : Measure X)) hC h
  choose πs hπs hgrid haction using hex
  let qs : ℕ → ProbabilityMeasure (Curve X) := fun n => ⟨πs n,hπs n⟩
  obtain ⟨π,φ,hφ,hlim,hA,hAC,hS⟩ := exists_action_limit qs ENNReal.ofReal_lt_top haction
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
omit [MeasurableSpace X] [BorelSpace X] in
lemma boundedTracks_of_compact [CompactSpace X] [Nonempty X] (π : Measure (Curve X)) :
    BoundedTracks π := by
  let o : X := Classical.arbitrary X
  obtain ⟨R,hR⟩ := (isCompact_univ : IsCompact (univ : Set X)).isBounded.subset_closedBall o
  refine ⟨o,max R 1,lt_of_lt_of_le zero_lt_one (le_max_right _ _),ae_of_all _ ?_⟩
  intro γ t
  exact (hR (mem_univ (γ t))).trans (le_max_left _ _)

lemma exists_testPlan_superposition [CompactSpace X] [Nonempty X]
    (m : Measure X) (μ : Time → ProbabilityMeasure X) (hμ : Continuous μ)
    {C : ℝ} (hC : 0 ≤ C) (h : DynamicActionBound (fun t => (μ t : Measure X)) C)
    (hcomp : ∃ L : ℝ≥0, ∀ t : Time, (μ t : Measure X) ≤ (L:ℝ≥0∞) • m) :
    ∃ π : Measure (Curve X), IsTestPlan m π ∧ BoundedTracks π ∧
      (∀ t : Time, π.map (fun γ => γ t) = (μ t : Measure X)) ∧
      (∫⁻ γ, ∫⁻ t in Icc (0:ℝ) 1, (metricSpeed γ t)^2 ∂volume ∂π) ≤ ENNReal.ofReal C := by
  obtain ⟨π,hmarg,hA,hAC,hS⟩ := exists_superposition μ hμ hC h
  refine ⟨π,⟨inferInstance,?_,hAC,hS.trans_lt ENNReal.ofReal_lt_top⟩,
    boundedTracks_of_compact _,hmarg,hS⟩
  obtain ⟨L,hL⟩ := hcomp
  exact ⟨L,fun t => by rw [hmarg t]; exact hL t⟩

end WeakHessian

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

end

end OAI
