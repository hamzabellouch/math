import OAI.Combinatorics.ContingencyTables.Counting.CompanionArithmeticStep
import OAI.Combinatorics.ContingencyTables.Machines.FiniteTraceSlowdown

namespace OAI

/-! # Capped trace returns from the actual companion Boolean walk

The return search scans the recorded path after its initial state. Its
reference expectation is the finite Green sum defining the capped trace;
the Boolean walk contributes its path error.
-/

namespace ContingencyTables.CompanionTraceWords

open CommonBasesFPRAS CompanionFactorialApplication CompanionBooleanPhase
open CompanionPhaseTrajectory CompanionOracleDensity CompanionWeightOracle
open CompanionRationalUpdates TwoLiftStates GridBoundary FirstSuccess ResidualMixture
open scoped BigOperators Classical

noncomputable section

variable {X : Type*}

/-- A fixed indicator convention keeps equivalent event descriptions
independent of the decision procedures inferred for their propositions. -/
def eventIndicator (P : Prop) : ℝ := @ite ℝ P (Classical.propDecidable P) 1 0

lemma eventIndicator_eq (P : Prop) [Decidable P] :
    eventIndicator P=(if P then (1:ℝ) else 0) := by
  by_cases h : P <;> simp only [eventIndicator,h,ite_true,ite_false]

def firstHit (B : X → Prop) : List X → Option (FiniteChain.Inside B)
  | [] => none
  | x::xs => if hx : B x then some ⟨x,hx⟩ else firstHit B xs

def returnValue (B : X → Prop) (phi : FiniteChain.Inside B → ℝ) (xs : List X) : ℝ :=
  DrawTree.optionValue phi (firstHit B xs.tail)

variable [Fintype X]

private lemma expectation_congr_start (C : FiniteChain X) (n : ℕ) (x : X)
    (F G : List X → ℝ) (h : ∀ xs,F (x::xs)=G (x::xs)) :
    C.pathExpectation n x F=C.pathExpectation n x G := by
  cases n with
  | zero => exact h []
  | succ n =>
    apply Finset.sum_congr rfl
    intro y _
    congr 1
    exact C.pathExpectation_congr n y _ _ h

private lemma firstHit_expectation (C : FiniteChain X) (B : X → Prop)
    (phi : FiniteChain.Inside B → ℝ) (n : ℕ) (x : X) :
    C.pathExpectation n x (fun xs => DrawTree.optionValue phi (firstHit B xs))=
      if hx : B x then phi ⟨x,hx⟩ else C.pathExpectation n x (returnValue B phi) := by
  by_cases hx : B x
  · rw [dite_eq_left hx]
    calc
      _ = C.pathExpectation n x (fun _ => phi ⟨x,hx⟩) := by
        apply expectation_congr_start
        intro xs
        simp only [firstHit,dite_eq_left hx,DrawTree.optionValue]
      _ = _ := C.pathExpectation_const n x _
  · rw [dite_eq_right hx]
    apply expectation_congr_start
    intro xs
    simp only [firstHit,dite_eq_right hx,returnValue,List.tail_cons]

private lemma returnValue_succ (C : FiniteChain X) (B : X → Prop)
    (phi : FiniteChain.Inside B → ℝ) (n : ℕ) (x : X) :
    C.pathExpectation (n+1) x (returnValue B phi)=
      ∑ y,C.P x y*(if hy : B y then phi ⟨y,hy⟩
        else C.pathExpectation n y (returnValue B phi)) := by
  simp only [FiniteChain.pathExpectation,returnValue,List.tail_cons]
  apply Finset.sum_congr rfl
  intro y _
  rw [firstHit_expectation]

private lemma returnValue_split (C : FiniteChain X) (B : X → Prop)
    (phi : FiniteChain.Inside B → ℝ) (n : ℕ) (x : X) :
    C.pathExpectation (n+1) x (returnValue B phi)=
      (∑ y : FiniteChain.Inside B,C.P x y.val*phi y)+
      ∑ y : FiniteChain.Outside B,C.P x y.val*C.pathExpectation n y.val (returnValue B phi) := by
  rw [returnValue_succ,←Fintype.sum_subtype_add_sum_subtype B]
  congr 1
  · apply Finset.sum_congr rfl
    intro y _
    rw [dite_eq_left y.property]
  · apply Finset.sum_congr rfl
    intro y _
    rw [dite_eq_right y.property]

private lemma partialGreen_succ (Q : KilledKernel X) (n : ℕ) (f : X → ℝ) (x : X) :
    Q.partialGreen (n+1) f x=f x+Q.apply (Q.partialGreen n f) x := by
  unfold KilledKernel.partialGreen
  rw [Finset.sum_range_succ']
  simp only [KilledKernel.iterate_succ,KilledKernel.iterate_zero]
  rw [KilledKernel.apply_sum]
  exact add_comm _ _

/-- An outside starting state has exactly the truncated Green expectation. -/
theorem outside_return_expectation (C : FiniteChain X) (B : X → Prop)
    (Q : KilledKernel (FiniteChain.Outside B))
    (hQ : ∀ x y,Q.Q x y=C.P x.val y.val)
    (phi : FiniteChain.Inside B → ℝ) (n : ℕ) (x : FiniteChain.Outside B) :
    C.pathExpectation n x.val (returnValue B phi)=
      Q.partialGreen n (fun z => ∑ y : FiniteChain.Inside B,C.P z.val y.val*phi y) x := by
  induction n generalizing x with
  | zero => simp [FiniteChain.pathExpectation,returnValue,firstHit,DrawTree.optionValue,
      KilledKernel.partialGreen]
  | succ n ih =>
    rw [returnValue_split,partialGreen_succ]
    congr 1
    unfold KilledKernel.apply
    apply Finset.sum_congr rfl
    intro y _
    rw [ih,hQ]

/-- Starting inside and allowing n+1 transitions gives the manuscript's
capped trace, with n possible further outside transitions. -/
theorem inside_return_expectation (C : FiniteChain X) (B : X → Prop)
    (Q : KilledKernel (FiniteChain.Outside B))
    (hQ : ∀ x y,Q.Q x y=C.P x.val y.val)
    (phi : FiniteChain.Inside B → ℝ) (n : ℕ) (x : FiniteChain.Inside B) :
    C.pathExpectation (n+1) x.val (returnValue B phi)=
      ∑ y : FiniteChain.Inside B,C.cappedTrace B Q n x y*phi y := by
  rw [returnValue_split]
  simp_rw [outside_return_expectation C B Q hQ]
  simp only [FiniteChain.cappedTrace,add_mul,Finset.sum_add_distrib]
  congr 1
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z _
  simp only [mul_assoc]
  rw [←Finset.mul_sum,KilledKernel.partialGreen_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro y _
  unfold KilledKernel.partialGreen
  simp_rw [show (fun t : FiniteChain.Outside B => C.P t.val y.val*phi y)=
    (fun t => phi y*C.P t.val y.val) by funext t; ring]
  simp only [KilledKernel.iterate_mul,←Finset.mul_sum]
  ring

omit [Fintype X] in
private lemma option_event (B : X → Prop) (E : FiniteChain.Inside B → Prop)
    (o : Option (FiniteChain.Inside B)) :
    eventIndicator (∃ y,o=some y ∧ E y)=
      DrawTree.optionValue (fun y => if E y then 1 else 0) o := by
  cases o <;> simp [eventIndicator,DrawTree.optionValue]

theorem return_event_expectation (C : FiniteChain X) (B : X → Prop)
    (Q : KilledKernel (FiniteChain.Outside B))
    (hQ : ∀ x y,Q.Q x y=C.P x.val y.val) (E : FiniteChain.Inside B → Prop)
    (n : ℕ) (x : FiniteChain.Inside B) :
    C.pathExpectation (n+1) x.val
      (fun xs => eventIndicator (∃ y,firstHit B xs.tail=some y ∧ E y))=
      ∑ y : FiniteChain.Inside B,C.cappedTrace B Q n x y*(if E y then 1 else 0) := by
  calc
    _ = C.pathExpectation (n+1) x.val (returnValue B (fun y => if E y then 1 else 0)) := by
      apply C.pathExpectation_congr
      intro xs
      exact option_event B E (firstHit B xs.tail)
    _ = _ := inside_return_expectation C B Q hQ _ n x

theorem return_failure_expectation (C : FiniteChain X) (B : X → Prop)
    (Q : KilledKernel (FiniteChain.Outside B))
    (hQ : ∀ x y,Q.Q x y=C.P x.val y.val) (n : ℕ) (x : FiniteChain.Inside B) :
    C.pathExpectation (n+1) x.val
      (fun xs => eventIndicator (firstHit B xs.tail=none))=
      1-∑ y : FiniteChain.Inside B,C.cappedTrace B Q n x y := by
  have hfun : (fun xs : List X =>
      eventIndicator (firstHit B xs.tail=none)+returnValue B (fun _ => 1) xs)=
      fun _ => (1:ℝ) := by
    funext xs
    unfold returnValue
    cases firstHit B xs.tail <;> simp [eventIndicator,DrawTree.optionValue]
  have he := C.pathExpectation_add (n+1) x.val
    (fun xs => eventIndicator (firstHit B xs.tail=none))
    (returnValue B (fun _ => 1))
  rw [hfun,C.pathExpectation_const,inside_return_expectation C B Q hQ] at he
  simp only [mul_one] at he
  linarith

variable {I J : Type} [Fintype I] [Fintype J]

def sourceKilled (A : Instance I J) (j : ℕ) (hp : 0<Fintype.card (Labels A))
    (w : Pair A → Pair A → ℚ) (hw : ∀ p q,0<w p q) :
    KilledKernel (FiniteChain.Outside (plainPredicate (pairs : List (Pair A)))) :=
  metropolisKilled pairs PairedLabels.fresh (CompanionConcentration.pairs_ne_nil A hp)
    PairedLabels.cover (fun p q => (w p q:ℝ)) (CompanionAnnealing.weight A j)
    (fun p q => by exact_mod_cast hw p q) (CompanionAnnealing.weight_positive A j)

def targetKilled (A : Instance I J) (j : ℕ) (hp : 0<Fintype.card (Labels A))
    (w : Pair A → Pair A → ℚ) (hw : ∀ p q,0<w p q) :
    KilledKernel (FiniteChain.Outside (plainPredicate (pairs : List (Pair A)))) :=
  FiniteChainSlowdown.slowKilled (sourceKilled A j hp w hw) (slowdown A)
    (by linarith [(slowdown_bounds A hp).1]) (slowdown_bounds A hp).2

lemma targetKilled_matches (A : Instance I J) (j : ℕ) (hp : 0<Fintype.card (Labels A))
    (w : Pair A → Pair A → ℚ) (hw : ∀ p q,0<w p q) :
    ∀ x y,(targetKilled A j hp w hw).Q x y=(targetChain A j hp w hw).P x.val y.val := by
  exact FiniteChainSlowdown.slowKilled_matches (referenceChain A j hp w hw) _
    (sourceKilled A j hp w hw) (by intro x y; rfl) (slowdown A)
    (by linarith [(slowdown_bounds A hp).1]) (slowdown_bounds A hp).2

/-- The search consumes a fixed cap worth of disjoint words even when
the first return occurs before the last word. -/
def returnWord (A : Instance I J) (C K j k N : ℕ)
    (hK : 1≤K) (hW : 100*A.d*K≤A.W) (xi : ℚ)
    (v : Grid (I := Fin (dimension A)) K) (w : Pair A → Pair A → ℚ) (S : State A)
    (bits : Fin (N*stepBits A C K j k xi) → Bool) :
    Option (PlainIndex (pairs : List (Pair A))) :=
  firstHit (plainPredicate pairs)
    (historyPrefix (CompanionArithmeticStep.recordedWalk A C K j k N N hK hW xi v w S bits)).tail

private lemma arithmetic_event_eq (A : Instance I J) (C K j k N : ℕ)
    (hK : 1≤K) (hW : 100*A.d*K≤A.W) (xi : ℚ)
    (v : Grid (I := Fin (dimension A)) K) (w : Pair A → Pair A → ℚ) (S : State A)
    (E : List (State A) → Prop) :
    uniformAverage (fun bits : Fin (N*stepBits A C K j k xi) → Bool =>
      if E (historyPrefix (CompanionArithmeticStep.recordedWalk A C K j k N N hK hW xi v w S bits))
      then (1:ℝ) else 0)=
    uniformAverage (fun bits : Fin (N*stepBits A C K j k xi) → Bool =>
      if E (historyPrefix (CompanionBooleanPhase.recordedWalk A C K j k N N hK hW xi v w S bits))
      then (1:ℝ) else 0) := by
  have hnew := FiniteLawMoments.word_expectation
    (CompanionArithmeticStep.recordedWalk A C K j k N N hK hW xi v w S)
    (fun a => if E (historyPrefix a) then (1:ℝ) else 0)
  have hold := FiniteLawMoments.word_expectation
    (CompanionBooleanPhase.recordedWalk A C K j k N N hK hW xi v w S)
    (fun a => if E (historyPrefix a) then (1:ℝ) else 0)
  rw [CompanionArithmeticStep.recordedWalk_law] at hnew
  rw [CompanionBooleanPhase.recordedWalk_law] at hold
  exact hnew.trans hold.symm

theorem arithmetic_recorded_event_bound (A : Instance I J) (C : ℕ) (hC : 0<C) (K j k : ℕ)
    (hK : 1≤K) (hW : 100*A.d*K≤A.W) (hB : (K:ℝ)=binWidth A C)
    (hj : j≤rationalHeight A C) (xi : ℚ) (hx0 : 0<xi) (hx1 : xi≤1/4)
    (hPL : PublishedInputs.FiniteBoxPrekopaLeindler (dimension A))
    (hCheeger : PublishedInputs.FiniteCheeger (Grid (I := Fin (dimension A)) K))
    (v : Grid (I := Fin (dimension A)) K) (hp : 0<Fintype.card (Labels A))
    (w : Pair A → Pair A → ℚ) (hw : ∀ p q,0<w p q) (N : ℕ) (S : State A)
    (E : List (State A) → Prop) :
    uniformAverage (fun bits : Fin (N*stepBits A C K j k xi) → Bool =>
      eventIndicator (E (historyPrefix
        (CompanionArithmeticStep.recordedWalk A C K j k N N hK hW xi v w S bits))))≤
      (targetChain A j hp w hw).pathExpectation N S (fun xs => eventIndicator (E xs))+
      N*((6*(xi:ℝ)+1/(2:ℝ)^k)/2) := by
  exact (arithmetic_event_eq A C K j k N hK hW xi v w S E).trans_le
    (recorded_event_bound A C hC K j k hK hW hB hj xi hx0 hx1 hPL hCheeger v hp w hw N S E)

/-- The concrete bounded return experiment has the capped trace event
bound plus one implementation error per used step. -/
theorem returnWord_event (A : Instance I J) (C : ℕ) (hC : 0<C) (K j k n : ℕ)
    (hK : 1≤K) (hW : 100*A.d*K≤A.W) (hB : (K:ℝ)=binWidth A C)
    (hj : j≤rationalHeight A C) (xi : ℚ) (hx0 : 0<xi) (hx1 : xi≤1/4)
    (hPL : PublishedInputs.FiniteBoxPrekopaLeindler (dimension A))
    (hCheeger : PublishedInputs.FiniteCheeger (Grid (I := Fin (dimension A)) K))
    (v : Grid (I := Fin (dimension A)) K) (hp : 0<Fintype.card (Labels A))
    (w : Pair A → Pair A → ℚ) (hw : ∀ p q,0<w p q)
    (S : PlainIndex (pairs : List (Pair A))) (E : PlainIndex (pairs : List (Pair A)) → Prop) :
    uniformAverage (fun bits : Fin ((n+1)*stepBits A C K j k xi) → Bool =>
      eventIndicator (∃ T,returnWord A C K j k (n+1) hK hW xi v w S.val bits=some T ∧ E T))≤
      (∑ T,(targetChain A j hp w hw).cappedTrace (plainPredicate pairs)
        (targetKilled A j hp w hw) n S T*eventIndicator (E T))+
      ((n+1:ℕ):ℝ)*((6*(xi:ℝ)+1/(2:ℝ)^k)/2) := by
  have he := arithmetic_recorded_event_bound A C hC K j k hK hW hB hj xi hx0 hx1
    hPL hCheeger v hp w hw (n+1) S.val
    (fun xs => ∃ T,firstHit (plainPredicate pairs) xs.tail=some T ∧ E T)
  have ht := return_event_expectation (targetChain A j hp w hw) (plainPredicate pairs)
    (targetKilled A j hp w hw) (targetKilled_matches A j hp w hw) E n S
  have hfinal := he.trans_eq (congrArg (fun t : ℝ => t+
    ((n+1:ℕ):ℝ)*((6*(xi:ℝ)+1/(2:ℝ)^k)/2)) ht)
  exact hfinal

/-- Capping the concrete word experiment adds the exact reference
nonreturn probability and the accumulated step-implementation error. -/
theorem returnWord_failure (A : Instance I J) (C : ℕ) (hC : 0<C) (K j k n : ℕ)
    (hK : 1≤K) (hW : 100*A.d*K≤A.W) (hB : (K:ℝ)=binWidth A C)
    (hj : j≤rationalHeight A C) (xi : ℚ) (hx0 : 0<xi) (hx1 : xi≤1/4)
    (hPL : PublishedInputs.FiniteBoxPrekopaLeindler (dimension A))
    (hCheeger : PublishedInputs.FiniteCheeger (Grid (I := Fin (dimension A)) K))
    (v : Grid (I := Fin (dimension A)) K) (hp : 0<Fintype.card (Labels A))
    (w : Pair A → Pair A → ℚ) (hw : ∀ p q,0<w p q)
    (S : PlainIndex (pairs : List (Pair A))) :
    uniformAverage (fun bits : Fin ((n+1)*stepBits A C K j k xi) → Bool =>
      eventIndicator (returnWord A C K j k (n+1) hK hW xi v w S.val bits=none))≤
      1-(∑ T,(targetChain A j hp w hw).cappedTrace (plainPredicate pairs)
        (targetKilled A j hp w hw) n S T)+
      ((n+1:ℕ):ℝ)*((6*(xi:ℝ)+1/(2:ℝ)^k)/2) := by
  have he := arithmetic_recorded_event_bound A C hC K j k hK hW hB hj xi hx0 hx1
    hPL hCheeger v hp w hw (n+1) S.val (fun xs => firstHit (plainPredicate pairs) xs.tail=none)
  have ht := return_failure_expectation (targetChain A j hp w hw) (plainPredicate pairs)
    (targetKilled A j hp w hw) (targetKilled_matches A j hp w hw) n S
  have hfinal := he.trans_eq (congrArg (fun t : ℝ => t+
    ((n+1:ℕ):ℝ)*((6*(xi:ℝ)+1/(2:ℝ)^k)/2)) ht)
  exact hfinal

end
end ContingencyTables.CompanionTraceWords

end OAI
