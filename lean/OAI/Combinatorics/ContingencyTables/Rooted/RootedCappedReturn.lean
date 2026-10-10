import OAI.Combinatorics.ContingencyTables.Rooted.RootedTraceWords
import OAI.Combinatorics.ContingencyTables.Counting.CompanionCappedReturn

namespace OAI

/-! # Actual selected-root capped returns with their literal fallback -/

namespace ContingencyTables.RootedCappedReturn

open CommonBasesFPRAS RootedBooleanPhase RootedTraceWords
open CompanionFactorialApplication CompanionOracleDensity CompanionRationalUpdates
open CompanionBooleanPhase (State stepBits)
open CompanionCappedReturn (returnDefault returnDefault_event_upper)
open CompanionTraceWords (eventIndicator firstHit)
open CompanionPhaseTrajectory (historyPrefix)
open FirstSuccess RealKernelApproximation TwoLiftStates GridBoundary
open scoped BigOperators Classical

noncomputable section
variable {I J : Type} [Fintype I] [Fintype J]

def returnWordDefault (A : Instance I J) (R : RootedCompletion.Selection A.T) (C K j k n : ℕ)
    (hK : 1≤K) (hW : 100*A.d*K≤A.W) (xi : ℚ)
    (v : Grid (I := Fin (dimension A)) K) (w : Pair A → Pair A → ℚ)
    (S : PlainIndex (pairs : List (Pair A)))
    (bits : Fin ((n+1)*stepBits A C K j k xi) → Bool) : PlainIndex (pairs : List (Pair A)) :=
  (returnWord A R C K j k (n+1) hK hW xi v w S.val bits).getD S

private theorem returnWordDefault_to_path (A : Instance I J) (R : RootedCompletion.Selection A.T) (C : ℕ) (hC : 0<C) (K j k n : ℕ)
    (hK : 1≤K) (hW : 100*A.d*K≤A.W) (hB : (K:ℝ)=binWidth A C)
    (hj : j≤rationalHeight A C) (xi : ℚ) (hx0 : 0<xi) (hx1 : xi≤1/4)
    (hPL : PublishedInputs.FiniteBoxPrekopaLeindler (dimension A))
    (hCheeger : PublishedInputs.FiniteCheeger (Grid (I := Fin (dimension A)) K))
    (v : Grid (I := Fin (dimension A)) K) (hp : 0<Fintype.card (Labels A))
    (w : Pair A → Pair A → ℚ) (hw : ∀ p q,0<w p q)
    (S : PlainIndex (pairs : List (Pair A))) (E : PlainIndex (pairs : List (Pair A)) → Prop) :
    uniformAverage (fun bits : Fin ((n+1)*stepBits A C K j k xi) → Bool =>
      eventIndicator (E (returnWordDefault A R C K j k n hK hW xi v w S bits)))≤
      (targetChain A R j hp w hw).pathExpectation (n+1) S.val
        (fun xs => eventIndicator (E (returnDefault (plainPredicate pairs) S xs)))+
      ((n+1:ℕ):ℝ)*((6*(xi:ℝ)+1/(2:ℝ)^k)/2) := by
  exact arithmetic_recorded_event_bound A R C hC K j k hK hW hB hj xi hx0 hx1
    hPL hCheeger v hp w hw (n+1) S.val
    (fun xs => E (returnDefault (plainPredicate pairs) S xs))

private theorem target_returnDefault_bound (A : Instance I J) (R : RootedCompletion.Selection A.T) (j : ℕ)
    (hp : 0<Fintype.card (Labels A)) (w : Pair A → Pair A → ℚ)
    (hw : ∀ p q,0<w p q) (n : ℕ)
    (S : PlainIndex (pairs : List (Pair A))) (E : PlainIndex (pairs : List (Pair A)) → Prop) :
    (targetChain A R j hp w hw).pathExpectation (n+1) S.val
      (fun xs => eventIndicator (E (returnDefault (plainPredicate pairs) S xs)))≤
      (∑ T,(targetChain A R j hp w hw).traceMatrix (plainPredicate pairs)
        (targetKilled A R j hp w hw) S T*eventIndicator (E T))+
      (1-∑ T,(targetChain A R j hp w hw).cappedTrace (plainPredicate pairs)
        (targetKilled A R j hp w hw) n S T) := by
  exact returnDefault_event_upper (targetChain A R j hp w hw) (plainPredicate pairs)
    (targetKilled A R j hp w hw) (targetKilled_matches A R j hp w hw) E n S

/-- The implemented total return step is compared to the exact trace,
with its cap loss left explicit for subsequent warm-law averaging. -/
theorem returnWordDefault_event (A : Instance I J) (R : RootedCompletion.Selection A.T) (C : ℕ) (hC : 0<C) (K j k n : ℕ)
    (hK : 1≤K) (hW : 100*A.d*K≤A.W) (hB : (K:ℝ)=binWidth A C)
    (hj : j≤rationalHeight A C) (xi : ℚ) (hx0 : 0<xi) (hx1 : xi≤1/4)
    (hPL : PublishedInputs.FiniteBoxPrekopaLeindler (dimension A))
    (hCheeger : PublishedInputs.FiniteCheeger (Grid (I := Fin (dimension A)) K))
    (v : Grid (I := Fin (dimension A)) K) (hp : 0<Fintype.card (Labels A))
    (w : Pair A → Pair A → ℚ) (hw : ∀ p q,0<w p q)
    (S : PlainIndex (pairs : List (Pair A))) (E : PlainIndex (pairs : List (Pair A)) → Prop) :
    uniformAverage (fun bits : Fin ((n+1)*stepBits A C K j k xi) → Bool =>
      eventIndicator (E (returnWordDefault A R C K j k n hK hW xi v w S bits)))≤
      (∑ T,(targetChain A R j hp w hw).traceMatrix (plainPredicate pairs)
        (targetKilled A R j hp w hw) S T*eventIndicator (E T))+
      (1-∑ T,(targetChain A R j hp w hw).cappedTrace (plainPredicate pairs)
        (targetKilled A R j hp w hw) n S T)+
      ((n+1:ℕ):ℝ)*((6*(xi:ℝ)+1/(2:ℝ)^k)/2) := by
  have he := returnWordDefault_to_path A R C hC K j k n hK hW hB hj xi hx0 hx1
    hPL hCheeger v hp w hw S E
  have ht := target_returnDefault_bound A R j hp w hw n S E
  have hb := _root_.add_le_add ht
    (le_refl (((n+1:ℕ):ℝ)*((6*(xi:ℝ)+1/(2:ℝ)^k)/2)))
  exact he.trans hb

end
end ContingencyTables.RootedCappedReturn

end OAI
