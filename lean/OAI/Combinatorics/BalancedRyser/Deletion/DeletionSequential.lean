import Mathlib
import OAI.Combinatorics.BalancedRyser.Deletion.Deletion
import OAI.Combinatorics.BalancedRyser.Probability.UniformThreshold

namespace OAI

noncomputable section

namespace Balanced
open scoped _root_.Balanced

open Filter Topology

universe u

structure DominatedDeletionPresentation (k : ℕ) (K : ℝ) where
  fieldData : FiniteFieldPresentation.{u}
  law : PMF (DeletionSet fieldData.carrier k)
  enoughLines : k ≤ Fintype.card fieldData.carrier
  dominated : DeletionDominated k K law

theorem uniformDeletionVanishing_iff_growing_presentations (k : ℕ) (K : ℝ)
    (E : ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F],
      DeletionSet F k → Prop) :
    UniformDeletionVanishing k K E ↔
    ∀ A : ℕ → DominatedDeletionPresentation.{u} k K,
      Tendsto (fun n => Fintype.card (A n).fieldData.carrier) atTop atTop →
      Tendsto (fun n => deletionEventProbability (A n).law (E (A n).fieldData.carrier))
        atTop (𝓝 0) := by
  constructor
  · intro h A hsize
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    obtain ⟨N, hN⟩ := h ε hε
    filter_upwards [hsize.eventually_ge_atTop N] with n hn
    have hp := hN (A n).fieldData.carrier hn (A n).enoughLines
      (A n).law (A n).dominated
    have hnonneg : 0 ≤ deletionEventProbability (A n).law (E (A n).fieldData.carrier) := by
      classical
      unfold deletionEventProbability
      positivity
    simpa only [Real.dist_eq, sub_zero, abs_of_nonneg hnonneg] using hp
  · intro h ε hε
    let size : DominatedDeletionPresentation.{u} k K → ℕ :=
      fun A => Fintype.card A.fieldData.carrier
    let error : DominatedDeletionPresentation.{u} k K → ℝ :=
      fun A => deletionEventProbability A.law (E A.fieldData.carrier)
    obtain ⟨N, hN⟩ := uniform_metric_threshold_of_growing_sequences size error 0 h ε hε
    refine ⟨N, ?_⟩
    intro F hF hFin hDec hn hk Q hQ
    let A : DominatedDeletionPresentation.{u} k K := ⟨⟨F, hF, hFin, hDec⟩, Q, hk, hQ⟩
    have hbound := hN A hn
    exact (le_abs_self (deletionEventProbability Q (E F))).trans_lt
      (by simpa only [Real.dist_eq, sub_zero, error, A] using hbound)

theorem uniformDeletionVanishing_tendsto (k : ℕ) (K : ℝ)
    (E : ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F],
      DeletionSet F k → Prop)
    (h : UniformDeletionVanishing k K E)
    (F : ℕ → Type u) [hF : ∀ n, Field (F n)] [hFin : ∀ n, Fintype (F n)]
    [hDec : ∀ n, DecidableEq (F n)]
    (Q : ∀ n, PMF (DeletionSet (F n) k))
    (hk : ∀ n, k ≤ Fintype.card (F n)) (hQ : ∀ n, DeletionDominated k K (Q n))
    (hsize : Tendsto (fun n => Fintype.card (F n)) atTop atTop) :
    Tendsto (fun n => deletionEventProbability (Q n) (E (F n))) atTop (𝓝 0) := by
  let A : ℕ → DominatedDeletionPresentation.{u} k K :=
    fun n => ⟨⟨F n, hF n, hFin n, hDec n⟩, Q n, hk n, hQ n⟩
  exact (uniformDeletionVanishing_iff_growing_presentations k K E).mp h A hsize

theorem uniformDeletionVanishing_tendsto_filter {ι : Type*} {l : Filter ι}
    (k : ℕ) (K : ℝ)
    (E : ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F],
      DeletionSet F k → Prop)
    (h : UniformDeletionVanishing k K E)
    (F : ι → Type u) [∀ i, Field (F i)] [∀ i, Fintype (F i)]
    [∀ i, DecidableEq (F i)]
    (Q : ∀ i, PMF (DeletionSet (F i) k))
    (hk : ∀ᶠ i in l, k ≤ Fintype.card (F i))
    (hQ : ∀ᶠ i in l, DeletionDominated k K (Q i))
    (hsize : Tendsto (fun i => Fintype.card (F i)) l atTop) :
    Tendsto (fun i => deletionEventProbability (Q i) (E (F i))) l (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨N, hN⟩ := h ε hε
  filter_upwards [hsize.eventually_ge_atTop N, hk, hQ] with i hi hki hQi
  have hp := hN (F i) hi hki (Q i) hQi
  have hnonneg : 0 ≤ deletionEventProbability (Q i) (E (F i)) := by
    classical
    unfold deletionEventProbability
    positivity
  simpa only [Real.dist_eq, sub_zero, abs_of_nonneg hnonneg] using hp

end Balanced

end

end OAI
