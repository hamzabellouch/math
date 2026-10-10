import OAI.Combinatorics.ContingencyTables.Rooted.RootedPhaseAccuracy
import OAI.Combinatorics.ContingencyTables.Rooted.RootedSlowConcentration
import OAI.Combinatorics.ContingencyTables.Rooted.RootedTraceWords

namespace OAI

/-! # Accuracy of the selected-root executed finite-word phase history -/

namespace ContingencyTables.RootedPhaseExperiment

open CommonBasesFPRAS FirstSuccess RealKernelApproximation
open CompanionFactorialApplication RootedBooleanPhase CompanionOracleDensity
open CompanionRationalUpdates RootedAnnealing RootedMultiplierUpdate
open RootedPhaseTrajectory RootedTraceWords TwoLiftStates GridBoundary
open CompanionPhaseTrajectory (position_put historyPrefix)
open CompanionTraceWords (eventIndicator)
open CompanionBooleanPhase (State stepBits)
open scoped BigOperators Classical

noncomputable section

private lemma wordWalk_position {X : Type*} {k : ℕ}
    (step : X → (Fin k → Bool) → X) (N n : ℕ) (x : X) :
    n≤N → ∀ bits : Fin n → Fin k → Bool,
      (wordWalk (fun a b => pathPut a (step (pathRead a) b))
        (pathInitial N x) n bits).1.val=n := by
  induction n with
  | zero => intro _ bits; rfl
  | succ n ih =>
    intro hn bits
    let a := wordWalk (fun a b => pathPut a (step (pathRead a) b))
      (pathInitial N x) n (Fin.init bits)
    have ha : a.1.val=n := ih (by omega) (Fin.init bits)
    have hlt : a.1.val<N := by omega
    change (pathPut a (step (pathRead a) (bits (Fin.last n)))).1.val=n+1
    rw [position_put a _ hlt,ha]

private lemma full_prefix {X : Type*} {N : ℕ} (a : PathState X N)
    (ha : a.1.val=N) : historyPrefix a=List.ofFn a.2 := by
  unfold historyPrefix
  simp only [ha]
  congr 1

variable {I J : Type} [Fintype I] [Fintype J]

def observedStates (A : Instance I J) (R : RootedCompletion.Selection A.T) (C K j k N : ℕ)
    (hK : 1≤K) (hW : 100*A.d*K≤A.W) (xi : ℚ)
    (v : Grid (I := Fin (dimension A)) K) (w : Pair A → Pair A → ℚ)
    (S : State A) (bits : Fin (N*stepBits A C K j k xi) → Bool) :
    Fin (N+1) → Set (Labels A×Bool) := fun i =>
  ((RootedArithmeticStep.recordedWalk A R C K j k N N hK hW xi v w S bits).2 i).val

theorem observedStates_list (A : Instance I J) (R : RootedCompletion.Selection A.T) (C K j k N : ℕ)
    (hK : 1≤K) (hW : 100*A.d*K≤A.W) (xi : ℚ)
    (v : Grid (I := Fin (dimension A)) K) (w : Pair A → Pair A → ℚ)
    (S : State A) (bits : Fin (N*stepBits A C K j k xi) → Bool) :
    List.ofFn (observedStates A R C K j k N hK hW xi v w S bits)=
      (historyPrefix (RootedArithmeticStep.recordedWalk
        A R C K j k N N hK hW xi v w S bits)).map Subtype.val := by
  have hp := wordWalk_position (RootedArithmeticStep.step A R C K j k hK hW xi v w)
    N N S le_rfl (oracleWalkWordEquiv N (stepBits A C K j k xi) bits)
  change (RootedArithmeticStep.recordedWalk A R C K j k N N hK hW xi v w S bits).1.val=N at hp
  rw [full_prefix _ hp,List.map_ofFn]
  rfl

private lemma accuratePath_iff (A : Instance I J) (R : RootedCompletion.Selection A.T) (j N : ℕ)
    (hp : 0<Fintype.card (Labels A)) (w : Pair A → Pair A → ℚ)
    (hw : ∀ p q,0<w p q) (eta : ℝ) (l : List (State A)) (hlen : l.length=N+1) :
    (¬AccuratePhase pairs (fun p q => (w p q:ℝ)) (weight A R j) (ratio A R j)
      eta (l.map Subtype.val)) ↔
    ∃ o : PhaseObservables (pairs : List (Pair A)),
      eta*(targetChain A R j hp w hw).mean
        (fun S => phaseObservable pairs (ratio A R j) o S.val)<
      |FiniteChain.pathSum (fun S => phaseObservable pairs (ratio A R j) o S.val) l/(N+1:ℕ)-
        (targetChain A R j hp w hw).mean
          (fun S => phaseObservable pairs (ratio A R j) o S.val)| := by
  simp only [AccuratePhase,not_forall,not_le,empirical,List.map_map,List.length_map,
    hlen,FiniteChain.pathSum,RootedSlowConcentration.target_mean,Function.comp_def]

private theorem reference_failure (A : Instance I J) (R : RootedCompletion.Selection A.T) (j N : ℕ)
    (hp : 0<Fintype.card (Labels A)) (w : Pair A → Pair A → ℚ)
    (hw : ∀ p q,0<w p q)
    (hgood : GoodMultipliers pairs (weight A R j) (fun p q => (w p q:ℝ)))
    (nu : State A → ℝ) (hnu : ∀ S,0≤nu S)
    (hwarm : ∀ S,nu S≤(10*(Fintype.card (Labels A):ℝ)^2)*
      chainWeight pairs (fun p q => (w p q:ℝ)) (weight A R j) S.val/
        chainTotal pairs (fun p q => (w p q:ℝ)) (weight A R j))
    (eta : ℝ) (heta : 0<eta) :
    (targetChain A R j hp w hw).pathProbability nu N (fun l =>
      ¬AccuratePhase pairs (fun p q => (w p q:ℝ)) (weight A R j) (ratio A R j)
        eta (l.map Subtype.val))≤
      32000*(Fintype.card (Labels A):ℝ)^8*
        ObservableBounds.observableConstant (Fintype.card (Labels A)) ((A.W:ℝ)^2)/
          (((N+1:ℕ):ℝ)*eta^2) := by
  have he := (targetChain A R j hp w hw).pathProbability_congr_length nu N _ _
    (fun l hl => accuratePath_iff A R j N hp w hw eta l hl)
  rw [he]
  simpa only [Nat.add_sub_cancel] using
    RootedSlowConcentration.phase_failure A R j hp w hw hgood nu hnu hwarm
      (N+1) (by omega) eta heta

/-- The actual recorded finite-word trajectory satisfies the source
concentration bound plus the accumulated proved one-step error. -/
theorem observed_failure (A : Instance I J) (R : RootedCompletion.Selection A.T) (C : ℕ) (hC : 0<C) (K j k N : ℕ)
    (hK : 1≤K) (hW : 100*A.d*K≤A.W) (hB : (K:ℝ)=binWidth A C)
    (hj : j≤rationalHeight A C) (xi : ℚ) (hx0 : 0<xi) (hx1 : xi≤1/4)
    (hPL : PublishedInputs.FiniteBoxPrekopaLeindler (dimension A))
    (hCheeger : PublishedInputs.FiniteCheeger (Grid (I := Fin (dimension A)) K))
    (v : Grid (I := Fin (dimension A)) K) (hp : 0<Fintype.card (Labels A))
    (w : Pair A → Pair A → ℚ) (hw : ∀ p q,0<w p q)
    (hgood : GoodMultipliers pairs (weight A R j) (fun p q => (w p q:ℝ)))
    (nu : State A → ℝ) (hnu : ∀ S,0≤nu S) (hmass : ∑ S,nu S≤1)
    (hwarm : ∀ S,nu S≤(10*(Fintype.card (Labels A):ℝ)^2)*
      chainWeight pairs (fun p q => (w p q:ℝ)) (weight A R j) S.val/
        chainTotal pairs (fun p q => (w p q:ℝ)) (weight A R j))
    (eta : ℝ) (heta : 0<eta) :
    (∑ S,nu S*uniformAverage (fun bits : Fin (N*stepBits A C K j k xi) → Bool =>
      eventIndicator (¬AccuratePhase pairs (fun p q => (w p q:ℝ)) (weight A R j) (ratio A R j)
        eta (List.ofFn (observedStates A R C K j k N hK hW xi v w S bits)))))≤
      32000*(Fintype.card (Labels A):ℝ)^8*
        ObservableBounds.observableConstant (Fintype.card (Labels A)) ((A.W:ℝ)^2)/
          (((N+1:ℕ):ℝ)*eta^2)+
        (N:ℝ)*((6*(xi:ℝ)+1/(2:ℝ)^k)/2) := by
  let E : List (State A) → Prop := fun l =>
    ¬AccuratePhase pairs (fun p q => (w p q:ℝ)) (weight A R j) (ratio A R j)
      eta (l.map Subtype.val)
  let err : ℝ := (N:ℝ)*((6*(xi:ℝ)+1/(2:ℝ)^k)/2)
  have herr : 0≤err := by dsimp only [err]; positivity
  have hpoint (S : State A) :
      uniformAverage (fun bits : Fin (N*stepBits A C K j k xi) → Bool =>
        eventIndicator (¬AccuratePhase pairs (fun p q => (w p q:ℝ)) (weight A R j) (ratio A R j)
          eta (List.ofFn (observedStates A R C K j k N hK hW xi v w S bits))))≤
      (targetChain A R j hp w hw).pathExpectation N S (fun l => eventIndicator (E l))+err := by
    simpa only [observedStates_list] using
      arithmetic_recorded_event_bound A R C hC K j k hK hW hB hj xi hx0 hx1
        hPL hCheeger v hp w hw N S E
  have hs := Finset.sum_le_sum (fun S (_ : S∈Finset.univ) =>
    mul_le_mul_of_nonneg_left (hpoint S) (hnu S))
  have hm := mul_le_mul_of_nonneg_right hmass herr
  simp only [mul_add,Finset.sum_add_distrib,←Finset.sum_mul,one_mul] at hs hm
  dsimp only [err] at hs hm
  have href := reference_failure A R j N hp w hw hgood nu hnu hwarm eta heta
  change (∑ S,nu S*(targetChain A R j hp w hw).pathExpectation N S
    (fun l => eventIndicator (E l)))≤_ at href
  exact hs.trans (by linarith)

end
end ContingencyTables.RootedPhaseExperiment

end OAI
