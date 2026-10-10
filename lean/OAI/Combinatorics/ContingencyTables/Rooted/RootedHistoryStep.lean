import OAI.Combinatorics.ContingencyTables.Rooted.RootedPhaseHistory
import OAI.Combinatorics.ContingencyTables.Transport.FinitePaddedAverage

namespace OAI

/-! # Conditional accuracy of each actual adaptive outer phase -/

namespace ContingencyTables.RootedHistoryStep

open CommonBasesFPRAS FirstSuccess FairBits CompanionFactorialApplication
open CompanionRationalUpdates CompanionOracleDensity RootedPhaseHistory RootedStoredHistory
open CompanionPhaseWords (Stored)
open CompanionTraceWords (eventIndicator)
open CompanionTargetMixing (restartTime)
open TwoLiftStates GridBoundary
open scoped BigOperators Classical

noncomputable section

private lemma default_failure {X : Type*} (o : Option X) (d : X) (P : X → Prop) :
    eventIndicator (¬P (o.getD d)) ≤
      eventIndicator (¬∃ x,o=some x ∧ P x) := by
  cases o with
  | none => by_cases hd : P d <;> simp [eventIndicator,hd]
  | some x => by_cases hx : P x <;> simp [eventIndicator,hx]

variable {I J : Type} [Fintype I] [Fintype J]

def error (A : Instance I J) (s : Settings A) (eta : ℝ) (j : ℕ) : ℝ :=
  32000*(Fintype.card (Labels A):ℝ)^8*
    ObservableBounds.observableConstant (Fintype.card (Labels A)) ((A.W:ℝ)^2)/
      (((s.N+1:ℕ):ℝ)*eta^2)+
    (s.N:ℝ)*((6*(s.xi:ℝ)+1/(2:ℝ)^s.k)/2)+
      2*(1/(2:ℝ)^s.h+(j:ℝ)*((restartTime A s.H s.L:ℝ)*
        ((20*(Fintype.card (Labels A):ℝ)^2)/(s.n:ℝ)+
          ((s.n+1:ℕ):ℝ)*((6*(s.xi:ℝ)+1/(2:ℝ)^s.k)/2))))+
        2*((s.N+1:ℕ):ℝ)*(s.xi:ℝ)

lemma error_mono (A : Instance I J) (s : Settings A) (eta : ℝ) (j l : ℕ)
    (hj : j ≤ l) (hx : 0 ≤ s.xi) : error A s eta j ≤ error A s eta l := by
  have hxR : (0:ℝ) ≤ (s.xi:ℝ) := by exact_mod_cast hx
  have hcoef : 0 ≤ (restartTime A s.H s.L:ℝ)*
      ((20*(Fintype.card (Labels A):ℝ)^2)/(s.n:ℝ)+
        ((s.n+1:ℕ):ℝ)*((6*(s.xi:ℝ)+1/(2:ℝ)^s.k)/2)) := by positivity
  have hmul := mul_le_mul_of_nonneg_right (show (j:ℝ) ≤ l by exact_mod_cast hj) hcoef
  unfold error
  linarith

/-- On each good past history, the actual next stored value fails the
source update conditions with the proved common error bound. -/
theorem step_failure (A : Instance I J) (R : RootedCompletion.Selection A.T) (s : Settings A)
    (hC : 0 < s.C) (hB : (s.K:ℝ)=binWidth A s.C)
    (hH : s.H ≤ rationalHeight A s.C)
    (hbox : (∏ a : SmallCell A,((A.b a.val.1 a.val.2:ℝ)+1)) ≤ (2:ℝ)^s.L)
    (hx0 : 0 < s.xi) (hx1 : s.xi ≤ 1/4)
    (hPL : PublishedInputs.FiniteBoxPrekopaLeindler (dimension A))
    (hCheeger : PublishedInputs.FiniteCheeger (Grid (I := Fin (dimension A)) s.K))
    (hp : 0 < Fintype.card (Labels A)) (hn : 0 < s.n)
    (eta : ℝ) (he0 : 0 < eta) (he1 : eta ≤ 1/4)
    (history : List (Stored A)) (hg : Good A R s.xi eta history)
    (hj : history.length < s.H) :
    uniformAverage (fun bits : Word A s =>
      eventIndicator (¬RootedPhaseTrial.ValidOutput A R history.length
        (lookup A history history.length) s.xi eta (step A R s history bits))) ≤
      error A s eta history.length := by
  let j := history.length
  let old := lookup A history j
  let w : ℕ → Pair A → Pair A → ℚ := fun i => (lookup A history i).multiplier
  let P : Stored A → Prop := RootedPhaseTrial.ValidOutput A R j old s.xi eta
  let F : RootedRestartTrial.Words A s.C s.K s.H s.L j s.k s.n s.N s.h s.xi → ℝ :=
    fun bits => eventIndicator (¬∃ next,
      RootedRestartTrial.run A R s.C s.K s.H s.L j s.k s.n s.N s.h s.hK s.hW s.xi
        s.v w old.estimate bits=some next ∧ P next)
  have hs := RootedRestartTrial.failure A R s.C hC s.K s.H s.L j s.k s.n s.N s.h
    s.hK s.hW hB hH hj hbox s.xi hx0 hx1 hPL hCheeger s.v hp w
    (fun i => (good_positive A R s.xi eta history hg i).1)
    (fun i hi => good_multipliers A R s.xi eta history hg i hi) hn old.estimate
    (good_positive A R s.xi eta history hg j).2 eta he0 he1
  have hpw (bits : Word A s) :
      eventIndicator (¬P (step A R s history bits)) ≤
        F (split A s j (prefixWord (width_le A s j hj) bits)) := by
    simp only [step,hj,dite_true]
    exact default_failure _ old P
  have havg := uniformAverage_mono _ _ hpw
  have heq := padded_equiv_average (width_le A s j hj) (split A s j) F
  rw [heq] at havg
  have hbound : uniformAverage F ≤ error A s eta j := hs
  exact havg.trans hbound

end
end ContingencyTables.RootedHistoryStep

end OAI
