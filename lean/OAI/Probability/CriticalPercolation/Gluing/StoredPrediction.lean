import Mathlib
import OAI.Probability.CriticalPercolation.Criticality.GrowthProcess

namespace OAI

section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

namespace CriticalPercolation.Corridor.Scheme
open BondGraph Boundary BernoulliProduct

variable {V E : Type*} [Countable V] [Countable E] (P : Scheme V E)

def Stable (n : ℕ) (S : GrowthState) (ω : Set E) : Prop :=
  (∀ v∈S.good, ω∈P.hit v (P.block S)) ∧
  (∀ e : Edge, source e∈S.good → n ≤ gridSlot (target e) →
    1-P.delta ≤ (blockProbability P.parameter (P.block S)
      (P.hit (target e) (P.block S∪P.edgeDomain e)) ω).toReal)

omit [Countable V] [Countable E] in
lemma stable_initial (hroot : (P.seed∩P.mark (0,0)).Nonempty)
    {ω : Set E} (hω : ω∈P.rootEvent) : P.Stable 0 GrowthState.initial ω := by
  constructor
  · intro v hv
    have he : v=(0,0) := by simpa [GrowthState.initial] using hv
    subst v
    change ω∈P.graph.restrictedSeed P.seed (P.mark (0,0)) _
    rw [P.graph.restrictedSeed_self _ _ hroot]
    trivial
  · intro e he _hn
    obtain ⟨v,b⟩ := e
    have hv : v=(0,0) := by simpa [GrowthState.initial,source] using he
    subst v
    exact hω b

lemma stable_advance (hh : 0≤P.h) (hhj : P.h≤P.j) (hsep : 2*P.j+P.h<1)
    (n : ℕ) (S : GrowthState) (b : Bool) (ω : Set E)
    (hv : S.Valid n) (hc : S.Covered) (hs : P.Stable n S ω)
    (ha : b=true → ω∈P.accepted n S) : P.Stable (n+1) (S.advance n b) ω := by
  have hold_hit : ∀ v∈S.good, ω∈P.hit v (P.block (S.advance n b)) := by
    intro v hv
    exact P.graph.restrictedSeed_mono _ _ (P.block_enlarged n S) (hs.1 v hv)
  have hold_pred : ∀ e : Edge, source e∈S.good → n+1 ≤ gridSlot (target e) →
      1-P.delta ≤ (blockProbability P.parameter (P.block (S.advance n b))
        (P.hit (target e) (P.block (S.advance n b)∪P.edgeDomain e)) ω).toReal := by
    intro e hp ht
    have hI := later_revealed_intersection P.graph P.coordinate P.j P.h hh hhj hsep
      (n+1) S (S.advance n b) hc (S.advance_valid n b hv) hp ht
    have hprob := P.graph.seed_prediction_persists P.parameter P.seed (P.mark (target e))
      (P.block S) (P.block (S.advance n b)) (P.edgeDomain e) ω (P.block_enlarged n S) hI
    exact (hs.2 e hp (by omega)).trans
      (ENNReal.toReal_mono (ne_of_lt (lt_of_le_of_lt (blockProbability_le_one _ _ _ _) ENNReal.one_lt_top)) hprob)
  constructor
  · intro v hv
    change v∈(if (incoming n S.good).isSome ∧ b=true then insert (slotSite n) S.good else S.good) at hv
    split_ifs at hv with hb
    · rcases Finset.mem_insert.mp hv with rfl|hv
      · exact (P.accepted_iff n S ω).mp (ha hb.2) |>.1
      · exact hold_hit v hv
    · exact hold_hit v hv
  · intro e hp ht
    change source e∈(if (incoming n S.good).isSome ∧ b=true then insert (slotSite n) S.good else S.good) at hp
    split_ifs at hp with hb
    · rcases Finset.mem_insert.mp hp with he|hp
      · have he' : e=(slotSite n,e.2) := Prod.ext he rfl
        rw [he']
        exact (P.accepted_iff n S ω).mp (ha hb.2) |>.2 e.2
      · exact hold_pred e hp ht
    · exact hold_pred e hp ht

theorem stable_on_cell (hh : 0≤P.h) (hhj : P.h≤P.j) (hsep : 2*P.j+P.h<1)
    (hroot : (P.seed∩P.mark (0,0)).Nonempty) (n : ℕ) (w : DecisionCode n)
    (ω : Set E) (hc : ω∈(P.rule.partition n).cell w) (hB : ω∈P.rootEvent) :
    P.Stable n (P.rule.state n w) ω := by
  induction n with
  | zero => exact P.stable_initial hroot hB
  | succ n ih =>
    rcases w with ⟨w,b⟩
    rw [P.rule.partition_cell_succ] at hc
    apply P.stable_advance hh hhj hsep n (P.rule.state n w) b ω
      (P.state_valid n w) (P.state_covered n w) (ih w hc.1)
    intro hb
    have hdecision := hc.2
    rw [hb] at hdecision
    change (if ω∈P.accepted n (P.rule.state n w) then true else false)=true at hdecision
    by_contra hn
    simp only [ite_eq_right hn,Bool.false_eq_true] at hdecision

end CriticalPercolation.Corridor.Scheme
end
end
end

end OAI
