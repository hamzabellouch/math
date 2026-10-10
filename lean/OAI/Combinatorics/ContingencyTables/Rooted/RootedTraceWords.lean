import OAI.Combinatorics.ContingencyTables.Rooted.RootedArithmeticStep
import OAI.Combinatorics.ContingencyTables.Counting.CompanionTraceWords

namespace OAI

/-! # Actual bounded first-return words for the selected-root chain -/

namespace ContingencyTables.RootedTraceWords

open CommonBasesFPRAS CompanionFactorialApplication RootedBooleanPhase
open RootedPhaseTrajectory CompanionOracleDensity CompanionWeightOracle
open CompanionRationalUpdates TwoLiftStates GridBoundary FirstSuccess ResidualMixture
open CompanionBooleanPhase (State stepBits slowdown slowdown_bounds)
open CompanionPhaseTrajectory (historyPrefix)
open CompanionTraceWords (eventIndicator firstHit return_event_expectation return_failure_expectation)
open scoped BigOperators Classical

noncomputable section
variable {I J : Type} [Fintype I] [Fintype J]

def sourceKilled (A : Instance I J) (R : RootedCompletion.Selection A.T) (j : ℕ) (hp : 0<Fintype.card (Labels A))
    (w : Pair A → Pair A → ℚ) (hw : ∀ p q,0<w p q) :
    KilledKernel (FiniteChain.Outside (plainPredicate (pairs : List (Pair A)))) :=
  metropolisKilled pairs PairedLabels.fresh (CompanionConcentration.pairs_ne_nil A hp)
    PairedLabels.cover (fun p q => (w p q:ℝ)) (RootedAnnealing.weight A R j)
    (fun p q => by exact_mod_cast hw p q) (RootedAnnealing.weight_positive A R j)

def targetKilled (A : Instance I J) (R : RootedCompletion.Selection A.T) (j : ℕ) (hp : 0<Fintype.card (Labels A))
    (w : Pair A → Pair A → ℚ) (hw : ∀ p q,0<w p q) :
    KilledKernel (FiniteChain.Outside (plainPredicate (pairs : List (Pair A)))) :=
  FiniteChainSlowdown.slowKilled (sourceKilled A R j hp w hw) (slowdown A)
    (by linarith [(slowdown_bounds A hp).1]) (slowdown_bounds A hp).2

lemma targetKilled_matches (A : Instance I J) (R : RootedCompletion.Selection A.T) (j : ℕ) (hp : 0<Fintype.card (Labels A))
    (w : Pair A → Pair A → ℚ) (hw : ∀ p q,0<w p q) :
    ∀ x y,(targetKilled A R j hp w hw).Q x y=(targetChain A R j hp w hw).P x.val y.val := by
  exact FiniteChainSlowdown.slowKilled_matches (referenceChain A R j hp w hw) _
    (sourceKilled A R j hp w hw) (by intro x y; rfl) (slowdown A)
    (by linarith [(slowdown_bounds A hp).1]) (slowdown_bounds A hp).2

/-- The search consumes a fixed cap worth of disjoint words even when
the first return occurs before the last word. -/
def returnWord (A : Instance I J) (R : RootedCompletion.Selection A.T) (C K j k N : ℕ)
    (hK : 1≤K) (hW : 100*A.d*K≤A.W) (xi : ℚ)
    (v : Grid (I := Fin (dimension A)) K) (w : Pair A → Pair A → ℚ) (S : State A)
    (bits : Fin (N*stepBits A C K j k xi) → Bool) :
    Option (PlainIndex (pairs : List (Pair A))) :=
  firstHit (plainPredicate pairs)
    (historyPrefix (RootedArithmeticStep.recordedWalk A R C K j k N N hK hW xi v w S bits)).tail

private lemma arithmetic_event_eq (A : Instance I J) (R : RootedCompletion.Selection A.T) (C K j k N : ℕ)
    (hK : 1≤K) (hW : 100*A.d*K≤A.W) (xi : ℚ)
    (v : Grid (I := Fin (dimension A)) K) (w : Pair A → Pair A → ℚ) (S : State A)
    (E : List (State A) → Prop) :
    uniformAverage (fun bits : Fin (N*stepBits A C K j k xi) → Bool =>
      if E (historyPrefix (RootedArithmeticStep.recordedWalk A R C K j k N N hK hW xi v w S bits))
      then (1:ℝ) else 0)=
    uniformAverage (fun bits : Fin (N*stepBits A C K j k xi) → Bool =>
      if E (historyPrefix (RootedBooleanPhase.recordedWalk A R C K j k N N hK hW xi v w S bits))
      then (1:ℝ) else 0) := by
  have hnew := FiniteLawMoments.word_expectation
    (RootedArithmeticStep.recordedWalk A R C K j k N N hK hW xi v w S)
    (fun a => if E (historyPrefix a) then (1:ℝ) else 0)
  have hold := FiniteLawMoments.word_expectation
    (RootedBooleanPhase.recordedWalk A R C K j k N N hK hW xi v w S)
    (fun a => if E (historyPrefix a) then (1:ℝ) else 0)
  rw [RootedArithmeticStep.recordedWalk_law] at hnew
  rw [RootedBooleanPhase.recordedWalk_law] at hold
  exact hnew.trans hold.symm

theorem arithmetic_recorded_event_bound (A : Instance I J) (R : RootedCompletion.Selection A.T) (C : ℕ) (hC : 0<C) (K j k : ℕ)
    (hK : 1≤K) (hW : 100*A.d*K≤A.W) (hB : (K:ℝ)=binWidth A C)
    (hj : j≤rationalHeight A C) (xi : ℚ) (hx0 : 0<xi) (hx1 : xi≤1/4)
    (hPL : PublishedInputs.FiniteBoxPrekopaLeindler (dimension A))
    (hCheeger : PublishedInputs.FiniteCheeger (Grid (I := Fin (dimension A)) K))
    (v : Grid (I := Fin (dimension A)) K) (hp : 0<Fintype.card (Labels A))
    (w : Pair A → Pair A → ℚ) (hw : ∀ p q,0<w p q) (N : ℕ) (S : State A)
    (E : List (State A) → Prop) :
    uniformAverage (fun bits : Fin (N*stepBits A C K j k xi) → Bool =>
      eventIndicator (E (historyPrefix
        (RootedArithmeticStep.recordedWalk A R C K j k N N hK hW xi v w S bits))))≤
      (targetChain A R j hp w hw).pathExpectation N S (fun xs => eventIndicator (E xs))+
      N*((6*(xi:ℝ)+1/(2:ℝ)^k)/2) := by
  exact (arithmetic_event_eq A R C K j k N hK hW xi v w S E).trans_le
    (recorded_event_bound A R C hC K j k hK hW hB hj xi hx0 hx1 hPL hCheeger v hp w hw N S E)

/-- The concrete bounded return experiment has the capped trace event
bound plus one implementation error per used step. -/
theorem returnWord_event (A : Instance I J) (R : RootedCompletion.Selection A.T) (C : ℕ) (hC : 0<C) (K j k n : ℕ)
    (hK : 1≤K) (hW : 100*A.d*K≤A.W) (hB : (K:ℝ)=binWidth A C)
    (hj : j≤rationalHeight A C) (xi : ℚ) (hx0 : 0<xi) (hx1 : xi≤1/4)
    (hPL : PublishedInputs.FiniteBoxPrekopaLeindler (dimension A))
    (hCheeger : PublishedInputs.FiniteCheeger (Grid (I := Fin (dimension A)) K))
    (v : Grid (I := Fin (dimension A)) K) (hp : 0<Fintype.card (Labels A))
    (w : Pair A → Pair A → ℚ) (hw : ∀ p q,0<w p q)
    (S : PlainIndex (pairs : List (Pair A))) (E : PlainIndex (pairs : List (Pair A)) → Prop) :
    uniformAverage (fun bits : Fin ((n+1)*stepBits A C K j k xi) → Bool =>
      eventIndicator (∃ T,returnWord A R C K j k (n+1) hK hW xi v w S.val bits=some T ∧ E T))≤
      (∑ T,(targetChain A R j hp w hw).cappedTrace (plainPredicate pairs)
        (targetKilled A R j hp w hw) n S T*eventIndicator (E T))+
      ((n+1:ℕ):ℝ)*((6*(xi:ℝ)+1/(2:ℝ)^k)/2) := by
  have he := arithmetic_recorded_event_bound A R C hC K j k hK hW hB hj xi hx0 hx1
    hPL hCheeger v hp w hw (n+1) S.val
    (fun xs => ∃ T,firstHit (plainPredicate pairs) xs.tail=some T ∧ E T)
  have ht := return_event_expectation (targetChain A R j hp w hw) (plainPredicate pairs)
    (targetKilled A R j hp w hw) (targetKilled_matches A R j hp w hw) E n S
  have hfinal := he.trans_eq (congrArg (fun t : ℝ => t+
    ((n+1:ℕ):ℝ)*((6*(xi:ℝ)+1/(2:ℝ)^k)/2)) ht)
  exact hfinal

/-- Capping the concrete word experiment adds the exact reference
nonreturn probability and the accumulated step-implementation error. -/
theorem returnWord_failure (A : Instance I J) (R : RootedCompletion.Selection A.T) (C : ℕ) (hC : 0<C) (K j k n : ℕ)
    (hK : 1≤K) (hW : 100*A.d*K≤A.W) (hB : (K:ℝ)=binWidth A C)
    (hj : j≤rationalHeight A C) (xi : ℚ) (hx0 : 0<xi) (hx1 : xi≤1/4)
    (hPL : PublishedInputs.FiniteBoxPrekopaLeindler (dimension A))
    (hCheeger : PublishedInputs.FiniteCheeger (Grid (I := Fin (dimension A)) K))
    (v : Grid (I := Fin (dimension A)) K) (hp : 0<Fintype.card (Labels A))
    (w : Pair A → Pair A → ℚ) (hw : ∀ p q,0<w p q)
    (S : PlainIndex (pairs : List (Pair A))) :
    uniformAverage (fun bits : Fin ((n+1)*stepBits A C K j k xi) → Bool =>
      eventIndicator (returnWord A R C K j k (n+1) hK hW xi v w S.val bits=none))≤
      1-(∑ T,(targetChain A R j hp w hw).cappedTrace (plainPredicate pairs)
        (targetKilled A R j hp w hw) n S T)+
      ((n+1:ℕ):ℝ)*((6*(xi:ℝ)+1/(2:ℝ)^k)/2) := by
  have he := arithmetic_recorded_event_bound A R C hC K j k hK hW hB hj xi hx0 hx1
    hPL hCheeger v hp w hw (n+1) S.val (fun xs => firstHit (plainPredicate pairs) xs.tail=none)
  have ht := return_failure_expectation (targetChain A R j hp w hw) (plainPredicate pairs)
    (targetKilled A R j hp w hw) (targetKilled_matches A R j hp w hw) n S
  have hfinal := he.trans_eq (congrArg (fun t : ℝ => t+
    ((n+1:ℕ):ℝ)*((6*(xi:ℝ)+1/(2:ℝ)^k)/2)) ht)
  exact hfinal

end
end ContingencyTables.RootedTraceWords

end OAI
