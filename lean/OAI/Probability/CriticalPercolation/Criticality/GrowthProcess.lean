import Mathlib
import OAI.Probability.CriticalPercolation.Criticality.RestrictedSeed
import OAI.Probability.CriticalPercolation.Exploration.DecisionHistory
import OAI.Probability.CriticalPercolation.Exploration.GrowthHistoryGeometry
import OAI.Probability.CriticalPercolation.Gluing.PinnedTest

namespace OAI

section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

namespace CriticalPercolation.Corridor
open BondGraph Boundary BernoulliProduct

structure Scheme (V E : Type*) where
  graph : BondGraph V E
  coordinate : V → Point
  j : ℝ
  h : ℝ
  seed : Set V
  mark : Site → Set V
  parameter : E → unitInterval
  delta : ℝ

namespace Scheme
variable {V E : Type*} [Countable V] [Countable E] (P : Scheme V E)

def block (S : GrowthState) : Set E := revealed P.graph P.coordinate P.j P.h S

def edgeDomain (e : Edge) : Set E := corridorEdges P.graph P.coordinate P.j P.h e

def enlarged (n : ℕ) (S : GrowthState) : Set E := P.block (S.advance n false)

def hit (v : Site) (R : Set E) : Set (Set E) := P.graph.restrictedSeed P.seed (P.mark v) R

def incomingHit (n : ℕ) (S : GrowthState) : Set (Set E) := P.hit (slotSite n) (P.enlarged n S)

def nextHit (n : ℕ) (S : GrowthState) (b : Bool) : Set (Set E) :=
  P.hit (target (slotSite n,b)) (P.enlarged n S∪P.edgeDomain (slotSite n,b))

def accepted (n : ℕ) (S : GrowthState) : Set (Set E) :=
  (predictionFailure P.parameter (P.enlarged n S) (P.incomingHit n S)
    (P.nextHit n S true) (P.nextHit n S false) P.delta)ᶜ

lemma accepted_measurable (n : ℕ) (S : GrowthState) :
    MeasurableSet[blockSigma (P.enlarged n S)] (P.accepted n S) :=
  (measurableSet_predictionFailure P.parameter (P.enlarged n S) _ _ _
    (P.graph.measurableSet_restrictedSeed _ _ _) (P.graph.restrictedSeed_measurable _ _ _)
    (P.graph.restrictedSeed_measurable _ _ _) P.delta).compl

omit [Countable V] [Countable E] in
lemma accepted_iff (n : ℕ) (S : GrowthState) (ω : Set E) :
    ω∈P.accepted n S ↔ ω∈P.incomingHit n S ∧
      ∀ b : Bool, 1-P.delta ≤ (blockProbability P.parameter (P.enlarged n S) (P.nextHit n S b) ω).toReal := by
  change (¬((ω∉P.incomingHit n S ∨ ω∈P.incomingHit n S ∧
    (blockProbability P.parameter (P.enlarged n S) (P.nextHit n S true) ω).toReal<1-P.delta) ∨
    ω∈P.incomingHit n S ∧
    (blockProbability P.parameter (P.enlarged n S) (P.nextHit n S false) ω).toReal<1-P.delta)) ↔ _
  constructor
  · intro h
    have ha : ω∈P.incomingHit n S := Classical.byContradiction (fun hn => h (Or.inl (Or.inl hn)))
    refine ⟨ha,fun b => ?_⟩
    cases b
    · exact not_lt.mp (fun hb => h (Or.inr ⟨ha,hb⟩))
    · exact not_lt.mp (fun hb => h (Or.inl (Or.inr ⟨ha,hb⟩)))
  · rintro ⟨ha,hb⟩ (h|h)
    · rcases h with h|h
      · exact h ha
      · exact not_lt_of_ge (hb true) h.2
    · exact not_lt_of_ge (hb false) h.2

def rule : DecisionRule E GrowthState where
  initial := GrowthState.initial
  block := P.block
  further := P.enlarged
  contained n S := revealed_mono P.graph P.coordinate P.j P.h (S.seen_mono n false)
  active n S := (incoming n S.good).isSome
  accept := P.accepted
  measurable := P.accepted_measurable
  update := GrowthState.advance
  block_update _ _ _ := rfl

lemma state_valid (n : ℕ) (w : DecisionCode n) : (P.rule.state n w).Valid n := by
  induction n with
  | zero => exact GrowthState.initial_valid
  | succ n ih => exact GrowthState.advance_valid n _ w.2 (ih w.1)

lemma state_covered (n : ℕ) (w : DecisionCode n) : (P.rule.state n w).Covered := by
  induction n with
  | zero => exact GrowthState.initial_covered
  | succ n ih => exact GrowthState.advance_covered n _ w.2 (ih w.1)

omit [Countable V] [Countable E] in
lemma block_enlarged (n : ℕ) (S : GrowthState) : P.block S⊆P.enlarged n S :=
  revealed_mono P.graph P.coordinate P.j P.h (S.seen_mono n false)

omit [Countable V] [Countable E] in
lemma block_advance (n : ℕ) (S : GrowthState) (b : Bool) : P.block (S.advance n b)=P.enlarged n S := rfl

omit [Countable V] [Countable E] in
lemma enlarged_incoming (n : ℕ) (S : GrowthState) {e : Edge} (he : incoming n S.good=some e) :
    P.enlarged n S=P.block S∪P.edgeDomain e :=
  revealed_incoming P.graph P.coordinate P.j P.h n S false he

def rootEvent : Set (Set E) := {ω | ∀ b : Bool,
  1-P.delta ≤ (blockProbability P.parameter (P.block GrowthState.initial)
    (P.hit (target ((0,0),b)) (P.block GrowthState.initial∪P.edgeDomain ((0,0),b))) ω).toReal}

lemma rootEvent_measurable : MeasurableSet[blockSigma (P.block GrowthState.initial)] P.rootEvent := by
  simp only [rootEvent,Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro b
  exact measurableSet_le measurable_const
    (measurable_blockProbability P.parameter _ _ (P.graph.restrictedSeed_measurable _ _ _)).ennreal_toReal

lemma rootEvent_history : MeasurableSet[(P.rule.partition 0).historySigma] P.rootEvent := by
  intro w
  change MeasurableSet[blockSigma (P.block GrowthState.initial)] (P.rootEvent∩Set.univ)
  simpa only [Set.inter_univ] using P.rootEvent_measurable

end Scheme
end CriticalPercolation.Corridor
end
end
end

end OAI
