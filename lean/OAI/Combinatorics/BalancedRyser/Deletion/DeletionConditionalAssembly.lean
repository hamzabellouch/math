import OAI.Combinatorics.BalancedRyser.Deletion.DeletionProbabilityBridge
import OAI.Combinatorics.BalancedRyser.Deletion.DeletionSequential
import OAI.Combinatorics.BalancedRyser.Probability.PatternMomentsLemmas

namespace OAI

open Filter MeasureTheory ProbabilityTheory
open scoped Topology

namespace Balanced
open scoped _root_.Balanced

universe u v

theorem joint_deletion_failure_tendsto_zero {ι : Type*} {l : Filter ι}
    (k : ℕ) (K : ℝ)
    (E : ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F],
      DeletionSet F k → Prop)
    (hvanish : UniformDeletionVanishing k K E)
    (F : ι → Type u) [∀ i, Field (F i)] [∀ i, Fintype (F i)]
    [∀ i, DecidableEq (F i)]
    [∀ i, MeasurableSpace (DeletionSet (F i) k)]
    [∀ i, MeasurableSingletonClass (DeletionSet (F i) k)]
    (Ω : ι → Type v) [∀ i, MeasurableSpace (Ω i)]
    (μ : ∀ i, Measure (Ω i)) [∀ i, IsProbabilityMeasure (μ i)]
    (success : ∀ i, Set (Ω i)) (hsuccess : ∀ i, MeasurableSet (success i))
    (data : ∀ i, Ω i → DeletionSet (F i) k) (hdata : ∀ i, Measurable (data i))
    (Q : ∀ i, PMF (DeletionSet (F i) k))
    (hlaw : ∀ᶠ i in l, (Q i).toMeasure = ((cond (μ i) (success i)).map (data i)))
    (hQ : ∀ᶠ i in l, DeletionDominated k K (Q i))
    (hsize : Tendsto (fun i => Fintype.card (F i)) l atTop) :
    Tendsto (fun i => (μ i).real
      (success i ∩ data i ⁻¹' {D | E (F i) D})) l (𝓝 0) := by
  have hprob := uniformDeletionVanishing_tendsto_filter k K E hvanish F Q
    (hsize.eventually_ge_atTop k) hQ hsize
  apply ConditionalFailure.tendsto_joint_preimage_zero_of_map_cond μ success hsuccess
    data hdata (fun i => {D | E (F i) D})
    (fun i => (Set.toFinite {D | E (F i) D}).measurableSet)
  apply hprob.congr'
  filter_upwards [hlaw] with i hi
  rw [← hi, deletionEventProbability_eq_toMeasure]

end Balanced

end OAI
