import OAI.Combinatorics.ContingencyTables.Rooted.RootedPlainTrial
import OAI.Combinatorics.ContingencyTables.Rooted.RootedRestartWords
import OAI.Combinatorics.ContingencyTables.Transport.FiniteLawMoments

namespace OAI

/-! # An actual initialized restart followed by the finite phase update -/

namespace ContingencyTables.RootedRestartTrial

open CommonBasesFPRAS FirstSuccess ResidualMixture RealKernelApproximation
open CompanionFactorialApplication CompanionRationalUpdates CompanionOracleDensity
open RootedAnnealing RootedWarmStart RootedPhaseTrial RootedRestartWords
open RootedRestartStages RootedRestartPrefix
open CompanionPhaseWords (Stored)
open CompanionTraceWords (eventIndicator)
open CompanionTargetMixing (restartTime)
open TwoLiftStates GridBoundary
open scoped BigOperators Classical

noncomputable section

private lemma replace_distance (r B d D e : ℝ) (hr : r ≤ B+2*d+e) (hd : d ≤ D) :
    r ≤ B+2*D+e := by linarith

variable {I J : Type} [Fintype I] [Fintype J]

abbrev Words (A : Instance I J) (C K H L j k n N h : ℕ) (xi : ℚ) :=
  (Fin (initialStageBits A C K H L k n h j xi) → Bool) × TrialWords A C K j k N xi

def run (A : Instance I J) (R : RootedCompletion.Selection A.T)
    (C K H L j k n N h : ℕ) (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (xi : ℚ)
    (v : Grid (I := Fin (dimension A)) K) (w : ℕ → Pair A → Pair A → ℚ)
    (estimate : ℚ) (bits : Words A C K H L j k n N h xi) : Option (Stored A) :=
  trial A R C K j k N hK hW xi v ⟨w j,estimate⟩
    (initializedStages A R C K H L k n h j hK hW xi v w bits.1).val bits.2

/-- All source conditions concern the learned prefix. The words
for initialization, successive restarts, observations and weight calls
are independent, and all are part of this single finite experiment. -/
theorem failure (A : Instance I J) (R : RootedCompletion.Selection A.T)
    (C : ℕ) (hC : 0 < C) (K H L j k n N h : ℕ)
    (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (hB : (K:ℝ)=binWidth A C)
    (hH : H ≤ rationalHeight A C) (hj : j < H)
    (hbox : (∏ s : SmallCell A,((A.b s.val.1 s.val.2:ℝ)+1)) ≤ (2:ℝ)^L)
    (xi : ℚ) (hx0 : 0 < xi) (hx1 : xi ≤ 1/4)
    (hPL : PublishedInputs.FiniteBoxPrekopaLeindler (dimension A))
    (hCheeger : PublishedInputs.FiniteCheeger (Grid (I := Fin (dimension A)) K))
    (v : Grid (I := Fin (dimension A)) K) (hp : 0 < Fintype.card (Labels A))
    (w : ℕ → Pair A → Pair A → ℚ) (hw : ∀ i p q,0 < w i p q)
    (hgood : ∀ i,i ≤ j → GoodMultipliers pairs (weight A R i)
      (fun p q => (w i p q:ℝ))) (hn : 0 < n)
    (estimate : ℚ) (hE : 0 < estimate) (eta : ℝ) (he0 : 0 < eta) (he1 : eta ≤ 1/4) :
    uniformAverage (fun bits : Words A C K H L j k n N h xi =>
      eventIndicator (¬∃ next,run A R C K H L j k n N h hK hW xi v w estimate bits=some next ∧
        ValidOutput A R j ⟨w j,estimate⟩ xi eta next)) ≤
      32000*(Fintype.card (Labels A):ℝ)^8*
        ObservableBounds.observableConstant (Fintype.card (Labels A)) ((A.W:ℝ)^2)/
          (((N+1:ℕ):ℝ)*eta^2)+
        (N:ℝ)*((6*(xi:ℝ)+1/(2:ℝ)^k)/2)+
          2*(1/(2:ℝ)^h+(j:ℝ)*((restartTime A H L:ℝ)*
            ((20*(Fintype.card (Labels A):ℝ)^2)/(n:ℝ)+
              ((n+1:ℕ):ℝ)*((6*(xi:ℝ)+1/(2:ℝ)^k)/2))))+
            2*((N+1:ℕ):ℝ)*(xi:ℝ) := by
  let draw := initializedStages A R C K H L k n h j hK hW xi v w
  let p := mapLaw (uniformLaw (α := Fin (initialStageBits A C K H L k n h j xi) → Bool)) draw
  let q := reference A R H L hp w hw j
  let g (S : PlainIndex (pairs : List (Pair A))) : ℝ :=
    uniformAverage (fun bits : TrialWords A C K j k N xi =>
      eventIndicator (¬∃ next,trial A R C K j k N hK hW xi v ⟨w j,estimate⟩ S.val bits=some next ∧
        ValidOutput A R j ⟨w j,estimate⟩ xi eta next))
  have he : uniformAverage (fun bits : Words A C K H L j k n N h xi =>
      eventIndicator (¬∃ next,run A R C K H L j k n N h hK hW xi v w estimate bits=some next ∧
        ValidOutput A R j ⟨w j,estimate⟩ xi eta next))=∑ S,(p.mass S:ℝ)*g S := by
    rw [uniformAverage_prod]
    exact FiniteLawMoments.word_expectation draw g
  have hpast := RootedPlainTrial.trial_failure A R C hC K j k N hK hW hB
    ((Nat.succ_le_of_lt hj).trans hH) xi hx0 hx1 hPL hCheeger v hp
    ⟨w j,estimate⟩ (hw j) hE (hgood j le_rfl) p q
    (reference_nonnegative A R H L hp w hw j)
    (reference_mass A R H L hp w hw j).le
    (reference_two_warm_at A R H L hbox hp w hw j hj.le (hgood j le_rfl)) eta he0 he1
  have hd := initializedStages_distance A R C hC K H L k n h j hK hW hB hH hbox
    xi hx0 hx1 hPL hCheeger v hp w hw hgood hn hj.le
  rw [he]
  exact replace_distance _ _ _ _ _ hpast hd

end
end ContingencyTables.RootedRestartTrial

end OAI
