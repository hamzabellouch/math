import Mathlib
import OAI.Probability.CriticalPercolation.Criticality.ActualGrowth
import OAI.Probability.CriticalPercolation.Criticality.GrowthProcess
import OAI.Probability.CriticalPercolation.Gluing.StoredPrediction
import OAI.Probability.CriticalPercolation.GraphGeometry.MarkConnectivity

namespace OAI

section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

namespace CriticalPercolation.Corridor.Scheme
open BondGraph Boundary BernoulliProduct

variable {V E : Type*} [Countable V] [Countable E] (P : Scheme V E)

lemma local_failure_bound (hh : 0≤P.h) (hhj : P.h≤P.j) (hsep : 2*P.j+P.h<1)
    (hroot : (P.seed∩P.mark (0,0)).Nonempty) (hδ : 0<P.delta)
    (a : ℝ) (hε : 0≤P.delta+2*a/P.delta)
    (hpros : ∀ n S, S.Valid n → S.Covered → (incoming n S.good).isSome →
      ∀ ω b, (blockProbability P.parameter (P.block S)
        (P.incomingHit n S\P.nextHit n S b) ω).toReal ≤ a)
    (n : ℕ) (w : DecisionCode n) (ω : Set E)
    (hw : ω∈(P.rule.partition n).cell w) (hB : ω∈P.rootEvent) :
    (blockProbability P.parameter (P.rule.block (P.rule.state n w))
      {σ | P.rule.active n (P.rule.state n w) ∧ σ∉P.rule.accept n (P.rule.state n w)} ω).toReal
      ≤ P.delta+2*a/P.delta := by
  let S := P.rule.state n w
  have hs := P.stable_on_cell hh hhj hsep hroot n w ω hw hB
  by_cases ha : (incoming n S.good).isSome
  · obtain ⟨e,he⟩ := Option.isSome_iff_exists.mp ha
    have ht : target e=slotSite n := incoming_target he
    have hh := hs.2 e (incoming_source he) (by rw [ht,gridSlot_slotSite])
    have hin : 1-P.delta ≤ (blockProbability P.parameter (P.block S) (P.incomingHit n S) ω).toReal := by
      simpa only [incomingHit,P.enlarged_incoming n S he,ht] using hh
    have hloc := pinned_prediction_failure P.parameter (P.block S) (P.enlarged n S) ω
      (P.block_enlarged n S) (P.incomingHit n S) (P.nextHit n S true) (P.nextHit n S false)
      (P.graph.measurableSet_restrictedSeed _ _ _)
      (P.graph.restrictedSeed_measurable _ _ _) (P.graph.restrictedSeed_measurable _ _ _)
      P.delta a hδ hin (hpros n S (P.state_valid n w) (P.state_covered n w) ha ω true)
      (hpros n S (P.state_valid n w) (P.state_covered n w) ha ω false)
    have hevent : {σ | P.rule.active n S ∧ σ∉P.rule.accept n S}=
        predictionFailure P.parameter (P.enlarged n S) (P.incomingHit n S)
          (P.nextHit n S true) (P.nextHit n S false) P.delta := by
      ext σ
      change ((incoming n S.good).isSome ∧ ¬¬σ∈_) ↔ _
      simp only [ha,true_and,not_not]
    change (blockProbability P.parameter (P.block S) _ ω).toReal ≤ _
    rw [hevent]
    exact hloc
  · have hevent : {σ | P.rule.active n S ∧ σ∉P.rule.accept n S}=∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro σ hσ
      exact ha hσ.1
    change (blockProbability P.parameter (P.block S) _ ω).toReal ≤ _
    rw [hevent]
    simpa only [blockProbability,Set.preimage_empty,measure_empty,ENNReal.toReal_zero] using hε

theorem exploration_percolates (hh : 0≤P.h) (hhj : P.h≤P.j) (hsep : 2*P.j+P.h<1)
    (seed : Finset V) (hseed : P.seed=seed) (hroot : (P.seed∩P.mark (0,0)).Nonempty)
    (hmark : Pairwise (Disjoint on P.mark))
    (p : unitInterval) (hp : P.parameter=fun _ => p)
    (hB : 0<(law P.parameter).real P.rootEvent) (hδ : 0<P.delta)
    (a q : ℝ) (hq₀ : 0≤q) (hq : 8*q<1) (ha : 0≤a)
    (herr : P.delta+2*a/P.delta ≤ q^4)
    (hpros : ∀ n S, S.Valid n → S.Covered → (incoming n S.good).isSome →
      ∀ ω b, (blockProbability P.parameter (P.block S)
        (P.incomingHit n S\P.nextHit n S b) ω).toReal ≤ a) :
    0<P.graph.law p P.graph.percolates := by
  have hε : 0≤P.delta+2*a/P.delta := by positivity
  have hlocal := P.local_failure_bound hh hhj hsep hroot hδ a hε hpros
  have hcond := P.rule.conditional_failure_bound P.parameter P.rootEvent _ hε hlocal
  have hi := infinitely_many_good_from_tests (law P.parameter)
    (fun n => (P.rule.partition n).historySigma) P.rule.historySigma_mono P.rule.failure
    P.rule.failure_history_measurable P.rootEvent P.rootEvent_history hB P.allGood
    (fun ω _ => P.allGood_root ω) (fun ω _ v hv => P.allGood_quadrant ω hv)
    (fun ω _ => P.missing_child_fails ω) q hq₀ hq (by
      intro n A hm hAB
      exact (hcond n A hm hAB).trans (mul_le_mul_of_nonneg_right herr (measureReal_nonneg)))
  have hlaw : law P.parameter=P.graph.law p := by rw [hp]; exact BernoulliProduct.law_const p
  rw [hlaw] at hi
  apply P.graph.percolation_of_infinite_marks p P.rootEvent P.allGood seed P.mark hmark _ hi
  intro ω hω v hv
  have hr := P.allGood_reached hh hhj hsep hroot hω hv
  obtain ⟨a,ha,b,hr,hb⟩ := Set.mem_iUnion₂.mp hr
  exact ⟨b,hb,a,by simpa only [hseed,Finset.mem_coe] using ha,hr⟩

end CriticalPercolation.Corridor.Scheme
end
end
end

end OAI
