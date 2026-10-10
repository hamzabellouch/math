import OAI.Combinatorics.ContingencyTables.Rooted.RootedObservationStart

namespace OAI

/-! # A complete finite-word selected-root phase trial

The trajectory and its weight queries use disjoint words. The output is
the actual guarded rational multiplier and count update.
-/

namespace ContingencyTables.RootedPhaseTrial

open CommonBasesFPRAS CompanionFactorialApplication CompanionRationalUpdates
open CompanionOracleDensity RootedAnnealing RootedMultiplierUpdate
open RootedPhaseExperiment RootedPhaseWords RootedPhaseAccuracy RootedObservationStart
open CompanionBooleanPhase (State stepBits)
open CompanionPhaseWords (Stored phaseBits)
open CompanionTraceWords (eventIndicator)
open TwoLiftStates GridBoundary
open scoped BigOperators Classical

noncomputable section
private lemma paired_average_bound {X Y : Type*} [Fintype X] [Fintype Y]
    [Nonempty X] [Nonempty Y] (f : X × Y → ℝ) (g : X → ℝ) (q : X → Y → ℝ)
    (e : ℝ) (hpoint : ∀ z,f z ≤ g z.1+q z.1 z.2)
    (hq : ∀ x,uniformAverage (q x) ≤ e) :
    uniformAverage f ≤ uniformAverage g+e := by
  have hmean := uniformAverage_mono (fun x => uniformAverage (q x)) (fun _ : X => e) hq
  rw [uniformAverage_const] at hmean
  calc
    uniformAverage f ≤ uniformAverage (fun z : X × Y => g z.1+q z.1 z.2) :=
      uniformAverage_mono _ _ hpoint
    _ = uniformAverage g+uniformAverage (fun x => uniformAverage (q x)) := by
      rw [uniformAverage_prod]
      simp only [uniformAverage_add,uniformAverage_const]
    _ ≤ uniformAverage g+e := _root_.add_le_add (le_refl (uniformAverage g)) hmean

variable {I J : Type} [Fintype I] [Fintype J]

abbrev TrialWords (A : Instance I J) (C K j k N : ℕ) (xi : ℚ) :=
  (Fin (N*stepBits A C K j k xi) → Bool) ×
    (Fin (phaseBits A C K j (N+1) xi) → Bool)

def trial (A : Instance I J) (R : RootedCompletion.Selection A.T) (C K j k N : ℕ)
    (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (xi : ℚ)
    (v : Grid (I := Fin (dimension A)) K) (old : Stored A) (S : State A)
    (bits : TrialWords A C K j k N xi) : Option (Stored A) :=
  update A R C K j (N+1) hK hW xi v old
    (observedStates A R C K j k N hK hW xi v old.multiplier S bits.1) bits.2

def ValidOutput (A : Instance I J) (R : RootedCompletion.Selection A.T)
    (j : ℕ) (old : Stored A) (xi : ℚ) (eta : ℝ) (next : Stored A) : Prop :=
  (∀ p q,0 < next.multiplier p q) ∧ 0 < next.estimate ∧
    GoodMultipliers pairs (weight A R (j+1)) (fun p q => (next.multiplier p q:ℝ)) ∧
    |Real.log ((next.estimate:ℝ)/((old.estimate:ℝ)*
      (slotTotal pairs (weight A R (j+1)) ∅/slotTotal pairs (weight A R j) ∅)))| ≤
      4*(xi:ℝ)+4*eta

theorem trial_success (A : Instance I J) (R : RootedCompletion.Selection A.T) (C K j k N : ℕ)
    (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (xi : ℚ) (hx0 : 0 ≤ xi) (hx1 : xi ≤ 1/4)
    (v : Grid (I := Fin (dimension A)) K) (old : Stored A)
    (hw : ∀ p q,0 < old.multiplier p q) (hE : 0 < old.estimate)
    (S : State A) (bits : TrialWords A C K j k N xi) (eta : ℝ)
    (he0 : 0 ≤ eta) (he1 : eta ≤ 1/4)
    (hacc : AccuratePhase pairs (fun p q => (old.multiplier p q:ℝ)) (weight A R j) (ratio A R j)
      eta (List.ofFn (observedStates A R C K j k N hK hW xi v old.multiplier S bits.1)))
    (hcalls : accurateCalls A R C K j (N+1) hK hW xi v
      (observedStates A R C K j k N hK hW xi v old.multiplier S bits.1) bits.2) :
    ∃ next,trial A R C K j k N hK hW xi v old S bits=some next ∧
      ValidOutput A R j old xi eta next := by
  exact update_success A R C K j (N+1) hK hW xi hx0 hx1 v old hw hE eta he0 he1
    (observedStates A R C K j k N hK hW xi v old.multiplier S bits.1) hacc bits.2 hcalls

private theorem calls_failure_indicator (A : Instance I J) (R : RootedCompletion.Selection A.T)
    (C : ℕ) (hC : 0 < C) (K j N : ℕ)
    (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (hB : (K:ℝ)=binWidth A C)
    (hj : j+1 ≤ rationalHeight A C) (xi : ℚ) (hx0 : 0 < xi) (hx1 : xi < 1)
    (hPL : PublishedInputs.FiniteBoxPrekopaLeindler (dimension A))
    (hCheeger : PublishedInputs.FiniteCheeger (Grid (I := Fin (dimension A)) K))
    (v : Grid (I := Fin (dimension A)) K) (states : Fin N → Set (Labels A×Bool)) :
    uniformAverage (fun bits : Fin (phaseBits A C K j N xi) → Bool =>
      eventIndicator (¬accurateCalls A R C K j N hK hW xi v states bits)) ≤
        2*(N:ℝ)*(xi:ℝ) := by
  have ht := accurateCalls_failure A R C hC K j N hK hW hB hj xi hx0 hx1 hPL hCheeger v states
  have he : uniformAverage (fun bits : Fin (phaseBits A C K j N xi) → Bool =>
      eventIndicator (¬accurateCalls A R C K j N hK hW xi v states bits))=
      uniformAverage (fun bits : Fin (phaseBits A C K j N xi) → Bool =>
        if ¬accurateCalls A R C K j N hK hW xi v states bits then (1:ℝ) else 0) := by
    apply CompanionPhaseWords.average_ext_instances
    intro bits
    exact CompanionTraceWords.eventIndicator_eq _
  exact he.trans_le ht

/-- Actual guarded output failure is bounded by trajectory concentration,
the proved weight-call error, and the distance of its incoming law from
the exact warm reference. -/
theorem trial_failure (A : Instance I J) (R : RootedCompletion.Selection A.T)
    (C : ℕ) (hC : 0 < C) (K j k N : ℕ)
    (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (hB : (K:ℝ)=binWidth A C)
    (hj : j+1 ≤ rationalHeight A C) (xi : ℚ) (hx0 : 0 < xi) (hx1 : xi ≤ 1/4)
    (hPL : PublishedInputs.FiniteBoxPrekopaLeindler (dimension A))
    (hCheeger : PublishedInputs.FiniteCheeger (Grid (I := Fin (dimension A)) K))
    (v : Grid (I := Fin (dimension A)) K) (hp : 0 < Fintype.card (Labels A))
    (old : Stored A) (hw : ∀ p q,0 < old.multiplier p q) (hE : 0 < old.estimate)
    (hgood : GoodMultipliers pairs (weight A R j) (fun p q => (old.multiplier p q:ℝ)))
    (p q : State A → ℝ) (hp0 : ∀ S,0 ≤ p S) (hp1 : ∑ S,p S=1)
    (hq : ∀ S,0 ≤ q S) (hq1 : ∑ S,q S ≤ 1)
    (hwarm : ∀ S,q S ≤ (10*(Fintype.card (Labels A):ℝ)^2)*
      chainWeight pairs (fun p q => (old.multiplier p q:ℝ)) (weight A R j) S.val/
        chainTotal pairs (fun p q => (old.multiplier p q:ℝ)) (weight A R j))
    (eta : ℝ) (he0 : 0 < eta) (he1 : eta ≤ 1/4) :
    (∑ S,p S*uniformAverage (fun bits : TrialWords A C K j k N xi =>
      eventIndicator (¬∃ next,trial A R C K j k N hK hW xi v old S bits=some next ∧
        ValidOutput A R j old xi eta next))) ≤
      32000*(Fintype.card (Labels A):ℝ)^8*
        ObservableBounds.observableConstant (Fintype.card (Labels A)) ((A.W:ℝ)^2)/
          (((N+1:ℕ):ℝ)*eta^2)+
        (N:ℝ)*((6*(xi:ℝ)+1/(2:ℝ)^k)/2)+2*RealKernelApproximation.distance p q+
          2*((N+1:ℕ):ℝ)*(xi:ℝ) := by
  let states (S : State A) (bits : Fin (N*stepBits A C K j k xi) → Bool) :=
    observedStates A R C K j k N hK hW xi v old.multiplier S bits
  let badObservation (S : State A) (bits : Fin (N*stepBits A C K j k xi) → Bool) :=
    ¬AccuratePhase pairs (fun p q => (old.multiplier p q:ℝ)) (weight A R j) (ratio A R j)
      eta (List.ofFn (states S bits))
  have hpoint (S : State A) (bits : TrialWords A C K j k N xi) :
      eventIndicator (¬∃ next,trial A R C K j k N hK hW xi v old S bits=some next ∧
        ValidOutput A R j old xi eta next) ≤
      eventIndicator (badObservation S bits.1)+
        eventIndicator (¬accurateCalls A R C K j (N+1) hK hW xi v (states S bits.1) bits.2) := by
    by_cases ha : badObservation S bits.1
    · unfold eventIndicator
      split_ifs <;> norm_num
    · have ha' : AccuratePhase pairs (fun p q => (old.multiplier p q:ℝ)) (weight A R j)
          (ratio A R j) eta (List.ofFn (states S bits.1)) := not_not.mp ha
      by_cases hc : accurateCalls A R C K j (N+1) hK hW xi v (states S bits.1) bits.2
      · have hs := trial_success A R C K j k N hK hW xi hx0.le hx1 v old hw hE S bits
          eta he0.le he1 ha' hc
        simp only [eventIndicator,ha,hc,hs,not_true_eq_false,ite_false,zero_add]
        exact le_rfl
      · unfold eventIndicator
        split_ifs <;> norm_num
  have hlocal (S : State A) :
      uniformAverage (fun bits : TrialWords A C K j k N xi =>
        eventIndicator (¬∃ next,trial A R C K j k N hK hW xi v old S bits=some next ∧
          ValidOutput A R j old xi eta next)) ≤
      uniformAverage (fun bits => eventIndicator (badObservation S bits))+
        2*((N+1:ℕ):ℝ)*(xi:ℝ) := by
    have hc (bits : Fin (N*stepBits A C K j k xi) → Bool) :
        uniformAverage (fun fresh : Fin (phaseBits A C K j (N+1) xi) → Bool =>
          eventIndicator (¬accurateCalls A R C K j (N+1) hK hW xi v (states S bits) fresh)) ≤
            2*((N+1:ℕ):ℝ)*(xi:ℝ) := by
      exact calls_failure_indicator A R C hC K j (N+1) hK hW hB hj xi hx0
        (lt_of_le_of_lt hx1 (by norm_num)) hPL hCheeger v (states S bits)
    exact paired_average_bound _ _ _ _ (hpoint S) hc
  have hsum := Finset.sum_le_sum (fun S (_ : S∈Finset.univ) =>
    mul_le_mul_of_nonneg_left (hlocal S) (hp0 S))
  simp only [mul_add,Finset.sum_add_distrib,←Finset.sum_mul,hp1,one_mul] at hsum
  have hobs := observed_failure_near A R C hC K j k N hK hW hB (by omega) xi hx0 hx1
    hPL hCheeger v hp old.multiplier hw hgood p q hq hq1 hwarm eta he0
  dsimp only [badObservation,states] at hsum
  have hb := _root_.add_le_add hobs (le_refl (2*((N+1:ℕ):ℝ)*(xi:ℝ)))
  exact hsum.trans hb

end
end ContingencyTables.RootedPhaseTrial

end OAI
