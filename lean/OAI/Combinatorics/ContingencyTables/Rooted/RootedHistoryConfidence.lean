import OAI.Combinatorics.ContingencyTables.Rooted.RootedHistoryStep
import OAI.Combinatorics.ContingencyTables.Transport.FiniteUniformHistory

namespace OAI

/-! # Success probability of the actual adaptive selected-root history -/

namespace ContingencyTables.RootedHistoryConfidence

open CommonBasesFPRAS CompanionFactorialApplication CompanionRationalUpdates
open CompanionOracleDensity RootedPhaseHistory RootedStoredHistory RootedHistoryStep
open CompanionTraceWords (eventIndicator)
open TwoLiftStates GridBoundary
open scoped BigOperators Classical

noncomputable section

private lemma success_of_failure {X : Type*} [Fintype X] [Nonempty X]
    (P : X → Prop) (e : ℝ)
    (hf : uniformAverage (fun x => eventIndicator (¬P x)) ≤ e) :
    1-e ≤ uniformAverage (fun x => if P x then (1:ℝ) else 0) := by
  have hpoint (x : X) : (if P x then (1:ℝ) else 0)+eventIndicator (¬P x)=1 := by
    by_cases hx : P x <;> simp [eventIndicator,hx]
  have hadd := uniformAverage_add (fun x => if P x then (1:ℝ) else 0)
    (fun x => eventIndicator (¬P x))
  simp_rw [hpoint] at hadd
  rw [uniformAverage_const] at hadd
  linarith

variable {I J : Type} [Fintype I] [Fintype J]

def GoodWords (A : Instance I J) (R : RootedCompletion.Selection A.T)
    (s : Settings A) (eta : ℝ) (words : List (Word A s)) : Prop :=
  Good A R s.xi eta (decoded A R s words)

lemma error_nonnegative (A : Instance I J) (s : Settings A) (eta : ℝ)
    (hx : 0 ≤ s.xi) (j : ℕ) : 0 ≤ error A s eta j := by
  have hxR : (0:ℝ) ≤ (s.xi:ℝ) := by exact_mod_cast hx
  unfold error ObservableBounds.observableConstant
  positivity

/-- Each conditional probability is proved from the actual finite-word
phase; independent word histories then accumulate these losses. -/
theorem history_success (A : Instance I J) (R : RootedCompletion.Selection A.T) (s : Settings A)
    (hC : 0 < s.C) (hB : (s.K:ℝ)=binWidth A s.C)
    (hH : s.H ≤ rationalHeight A s.C)
    (hbox : (∏ a : SmallCell A,((A.b a.val.1 a.val.2:ℝ)+1)) ≤ (2:ℝ)^s.L)
    (hx0 : 0 < s.xi) (hx1 : s.xi ≤ 1/4)
    (hPL : PublishedInputs.FiniteBoxPrekopaLeindler (dimension A))
    (hCheeger : PublishedInputs.FiniteCheeger (Grid (I := Fin (dimension A)) s.K))
    (hp : 0 < Fintype.card (Labels A)) (hn : 0 < s.n)
    (eta : ℝ) (he0 : 0 < eta) (he1 : eta ≤ 1/4) :
    1-(s.H:ℝ)*error A s eta s.H ≤
      uniformAverage (fun words : Fin s.H → Word A s =>
        if GoodWords A R s eta (List.ofFn words) then (1:ℝ) else 0) := by
  apply FiniteUniformHistory.good_probability (GoodWords A R s eta) s.H
    (error A s eta s.H) (error_nonnegative A s eta hx0.le s.H)
  · intro words hgood hlen
    have hgood' : Good A R s.xi eta (decoded A R s words) := hgood
    have hj : (decoded A R s words).length<s.H := by simpa only [decoded_length] using hlen
    have hf := step_failure A R s hC hB hH hbox hx0 hx1 hPL hCheeger hp hn eta he0 he1
      (decoded A R s words) hgood' hj
    have he := (error_mono A s eta (decoded A R s words).length s.H hj.le hx0.le)
    have hf' := hf.trans he
    have hg (bits : Word A s) :
        GoodWords A R s eta (words++[bits]) ↔
          RootedPhaseTrial.ValidOutput A R words.length
            (lookup A (decoded A R s words) words.length) s.xi eta
            (step A R s (decoded A R s words) bits) := by
      rw [GoodWords,good_snoc_iff]
      exact and_iff_right hgood'
    have hf'' : uniformAverage (fun bits : Word A s =>
        eventIndicator (¬GoodWords A R s eta (words++[bits]))) ≤ error A s eta s.H := by
      have heq : (fun bits : Word A s => eventIndicator (¬GoodWords A R s eta (words++[bits])))=
          (fun bits : Word A s => eventIndicator (¬RootedPhaseTrial.ValidOutput A R words.length
            (lookup A (decoded A R s words) words.length) s.xi eta
            (step A R s (decoded A R s words) bits))) := by
        funext bits
        rw [hg bits]
      rw [heq]
      simpa only [decoded_length] using hf'
    exact success_of_failure _ _ hf''
  · change Good A R s.xi eta (decoded A R s [])
    rw [decoded_nil]
    exact good_nil A R s.xi eta

end
end ContingencyTables.RootedHistoryConfidence

end OAI
