import OAI.Combinatorics.ContingencyTables.Counting.CompanionTraceWords

namespace OAI

/-! # Total bounded trace steps

If a capped return search misses its target, the finite-word experiment
keeps its starting plain state. Its error against the exact trace is the
cap loss plus the error of the recorded Boolean walk.
-/

namespace ContingencyTables.CompanionCappedReturn

open CommonBasesFPRAS CompanionTraceWords CompanionPhaseTrajectory
open CompanionFactorialApplication CompanionBooleanPhase CompanionOracleDensity
open CompanionWeightOracle CompanionRationalUpdates TwoLiftStates GridBoundary
open scoped BigOperators Classical

noncomputable section

variable {X : Type*}

def returnDefault (B : X → Prop) (x : FiniteChain.Inside B) (xs : List X) :
    FiniteChain.Inside B := (firstHit B xs.tail).getD x

private lemma returnDefault_value (B : X → Prop) (x : FiniteChain.Inside B)
    (phi : FiniteChain.Inside B → ℝ) (xs : List X) :
    phi (returnDefault B x xs)=returnValue B phi xs+
      phi x*eventIndicator (firstHit B xs.tail=none) := by
  unfold returnDefault returnValue
  cases firstHit B xs.tail <;> simp [DrawTree.optionValue,eventIndicator]

variable [Fintype X]

/-- The missing cap mass is assigned to the starting state, exactly. -/
theorem returnDefault_expectation (C : FiniteChain X) (B : X → Prop)
    (Q : KilledKernel (FiniteChain.Outside B))
    (hQ : ∀ x y,Q.Q x y=C.P x.val y.val)
    (phi : FiniteChain.Inside B → ℝ) (n : ℕ) (x : FiniteChain.Inside B) :
    C.pathExpectation (n+1) x.val (fun xs => phi (returnDefault B x xs))=
      (∑ y,C.cappedTrace B Q n x y*phi y)+
        phi x*(1-∑ y,C.cappedTrace B Q n x y) := by
  calc
    _ = C.pathExpectation (n+1) x.val (fun xs => returnValue B phi xs+
        phi x*eventIndicator (firstHit B xs.tail=none)) := by
      apply C.pathExpectation_congr
      exact returnDefault_value B x phi
    _ = _ := by
      rw [C.pathExpectation_add,C.pathExpectation_mul,
        inside_return_expectation C B Q hQ,
        return_failure_expectation C B Q hQ]

/-- Bounded observations lose at most the exact omitted return mass. -/
theorem returnDefault_error (C : FiniteChain X) (B : X → Prop)
    (Q : KilledKernel (FiniteChain.Outside B))
    (hQ : ∀ x y,Q.Q x y=C.P x.val y.val)
    (phi : FiniteChain.Inside B → ℝ) (hphi : ∀ y,0≤phi y ∧ phi y≤1)
    (n : ℕ) (x : FiniteChain.Inside B) :
    |C.pathExpectation (n+1) x.val (fun xs => phi (returnDefault B x xs))-
      (∑ y,C.traceMatrix B Q x y*phi y)|≤
        1-∑ y,C.cappedTrace B Q n x y := by
  let loss : ℝ := 1-∑ y,C.cappedTrace B Q n x y
  have hloss : 0≤loss := sub_nonneg.mpr (C.cappedTrace_substochastic B Q hQ n x)
  have hdiff (y : FiniteChain.Inside B) :
      0≤C.traceMatrix B Q x y-C.cappedTrace B Q n x y :=
    sub_nonneg.mpr (C.cappedTrace_le B Q n x y)
  have hmass : (∑ y,(C.traceMatrix B Q x y-C.cappedTrace B Q n x y))=loss := by
    rw [Finset.sum_sub_distrib,C.traceMatrix_stochastic B Q hQ]
  have he0 : 0≤∑ y,(C.traceMatrix B Q x y-C.cappedTrace B Q n x y)*phi y :=
    Finset.sum_nonneg (fun y _ => mul_nonneg (hdiff y) (hphi y).1)
  have he1 : (∑ y,(C.traceMatrix B Q x y-C.cappedTrace B Q n x y)*phi y)≤loss := by
    calc
      _ ≤ ∑ y,(C.traceMatrix B Q x y-C.cappedTrace B Q n x y)*1 :=
        Finset.sum_le_sum (fun y _ => mul_le_mul_of_nonneg_left (hphi y).2 (hdiff y))
      _ = loss := by simpa only [mul_one] using hmass
  have hkeep0 : 0≤phi x*loss := mul_nonneg (hphi x).1 hloss
  have hkeep1 : phi x*loss≤loss := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (hphi x).2 hloss
  have heq : C.pathExpectation (n+1) x.val (fun xs => phi (returnDefault B x xs))-
      (∑ y,C.traceMatrix B Q x y*phi y)=
      phi x*loss-∑ y,(C.traceMatrix B Q x y-C.cappedTrace B Q n x y)*phi y := by
    rw [returnDefault_expectation C B Q hQ]
    simp only [sub_mul,Finset.sum_sub_distrib]
    dsimp only [loss]
    ring
  rw [heq]
  exact abs_le.mpr ⟨by linarith,by linarith⟩

theorem returnDefault_event_upper (C : FiniteChain X) (B : X → Prop)
    (Q : KilledKernel (FiniteChain.Outside B))
    (hQ : ∀ x y,Q.Q x y=C.P x.val y.val)
    (E : FiniteChain.Inside B → Prop) (n : ℕ) (x : FiniteChain.Inside B) :
    C.pathExpectation (n+1) x.val (fun xs => eventIndicator (E (returnDefault B x xs)))≤
      (∑ y,C.traceMatrix B Q x y*eventIndicator (E y))+
        (1-∑ y,C.cappedTrace B Q n x y) := by
  have h := returnDefault_error C B Q hQ (fun y => eventIndicator (E y))
    (by intro y; by_cases he : E y <;> simp [eventIndicator,he]) n x
  have hu := (le_abs_self _).trans h
  linarith

/-- The cap error is small on a warm input law even when a pointwise
return-time bound would be too expensive. -/
theorem warm_returnDefault_error (C : FiniteChain X) (B : X → Prop)
    [Nonempty (FiniteChain.Inside B)]
    (Q : KilledKernel (FiniteChain.Outside B))
    (hQ : ∀ x y,Q.Q x y=C.P x.val y.val)
    (phi : FiniteChain.Inside B → ℝ) (hphi : ∀ y,0≤phi y ∧ phi y≤1)
    (n : ℕ) (hn : 0<n) (nu : FiniteChain.Inside B → ℝ) (hnu : ∀ x,0≤nu x)
    (U : ℝ) (hwarm : ∀ x,nu x≤U*(C.traceChain B Q hQ).π x) :
    (∑ x,nu x*|C.pathExpectation (n+1) x.val (fun xs => phi (returnDefault B x xs))-
      (∑ y,C.traceMatrix B Q x y*phi y)|)≤U/C.insideMass B/(n:ℝ) := by
  have hloss := C.cappedTrace_warm_loss B Q hQ n U nu hnu hwarm
  have hnR : (0:ℝ)<n := by exact_mod_cast hn
  have hb : (∑ x,nu x*(1-∑ y,C.cappedTrace B Q n x y))≤
      U/C.insideMass B/(n:ℝ) := by
    apply (le_div_iff₀ hnR).mpr
    simpa only [mul_comm] using hloss
  apply le_trans _ hb
  exact Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left
    (returnDefault_error C B Q hQ phi hphi n x) (hnu x))

variable {I J : Type} [Fintype I] [Fintype J]

/-- A concrete total draw: a missing capped return keeps the input. -/
def returnWordDefault (A : Instance I J) (C K j k n : ℕ)
    (hK : 1≤K) (hW : 100*A.d*K≤A.W) (xi : ℚ)
    (v : Grid (I := Fin (dimension A)) K) (w : Pair A → Pair A → ℚ)
    (S : PlainIndex (pairs : List (Pair A)))
    (bits : Fin ((n+1)*stepBits A C K j k xi) → Bool) : PlainIndex (pairs : List (Pair A)) :=
  (returnWord A C K j k (n+1) hK hW xi v w S.val bits).getD S

private theorem returnWordDefault_to_path (A : Instance I J) (C : ℕ) (hC : 0<C) (K j k n : ℕ)
    (hK : 1≤K) (hW : 100*A.d*K≤A.W) (hB : (K:ℝ)=binWidth A C)
    (hj : j≤rationalHeight A C) (xi : ℚ) (hx0 : 0<xi) (hx1 : xi≤1/4)
    (hPL : PublishedInputs.FiniteBoxPrekopaLeindler (dimension A))
    (hCheeger : PublishedInputs.FiniteCheeger (Grid (I := Fin (dimension A)) K))
    (v : Grid (I := Fin (dimension A)) K) (hp : 0<Fintype.card (Labels A))
    (w : Pair A → Pair A → ℚ) (hw : ∀ p q,0<w p q)
    (S : PlainIndex (pairs : List (Pair A))) (E : PlainIndex (pairs : List (Pair A)) → Prop) :
    uniformAverage (fun bits : Fin ((n+1)*stepBits A C K j k xi) → Bool =>
      eventIndicator (E (returnWordDefault A C K j k n hK hW xi v w S bits)))≤
      (targetChain A j hp w hw).pathExpectation (n+1) S.val
        (fun xs => eventIndicator (E (returnDefault (plainPredicate pairs) S xs)))+
      ((n+1:ℕ):ℝ)*((6*(xi:ℝ)+1/(2:ℝ)^k)/2) := by
  exact arithmetic_recorded_event_bound A C hC K j k hK hW hB hj xi hx0 hx1
    hPL hCheeger v hp w hw (n+1) S.val
    (fun xs => E (returnDefault (plainPredicate pairs) S xs))

private theorem target_returnDefault_bound (A : Instance I J) (j : ℕ)
    (hp : 0<Fintype.card (Labels A)) (w : Pair A → Pair A → ℚ)
    (hw : ∀ p q,0<w p q) (n : ℕ)
    (S : PlainIndex (pairs : List (Pair A))) (E : PlainIndex (pairs : List (Pair A)) → Prop) :
    (targetChain A j hp w hw).pathExpectation (n+1) S.val
      (fun xs => eventIndicator (E (returnDefault (plainPredicate pairs) S xs)))≤
      (∑ T,(targetChain A j hp w hw).traceMatrix (plainPredicate pairs)
        (targetKilled A j hp w hw) S T*eventIndicator (E T))+
      (1-∑ T,(targetChain A j hp w hw).cappedTrace (plainPredicate pairs)
        (targetKilled A j hp w hw) n S T) := by
  exact returnDefault_event_upper (targetChain A j hp w hw) (plainPredicate pairs)
    (targetKilled A j hp w hw) (targetKilled_matches A j hp w hw) E n S

/-- The implemented total return step is compared to the exact trace,
with its cap loss left explicit for subsequent warm-law averaging. -/
theorem returnWordDefault_event (A : Instance I J) (C : ℕ) (hC : 0<C) (K j k n : ℕ)
    (hK : 1≤K) (hW : 100*A.d*K≤A.W) (hB : (K:ℝ)=binWidth A C)
    (hj : j≤rationalHeight A C) (xi : ℚ) (hx0 : 0<xi) (hx1 : xi≤1/4)
    (hPL : PublishedInputs.FiniteBoxPrekopaLeindler (dimension A))
    (hCheeger : PublishedInputs.FiniteCheeger (Grid (I := Fin (dimension A)) K))
    (v : Grid (I := Fin (dimension A)) K) (hp : 0<Fintype.card (Labels A))
    (w : Pair A → Pair A → ℚ) (hw : ∀ p q,0<w p q)
    (S : PlainIndex (pairs : List (Pair A))) (E : PlainIndex (pairs : List (Pair A)) → Prop) :
    uniformAverage (fun bits : Fin ((n+1)*stepBits A C K j k xi) → Bool =>
      eventIndicator (E (returnWordDefault A C K j k n hK hW xi v w S bits)))≤
      (∑ T,(targetChain A j hp w hw).traceMatrix (plainPredicate pairs)
        (targetKilled A j hp w hw) S T*eventIndicator (E T))+
      (1-∑ T,(targetChain A j hp w hw).cappedTrace (plainPredicate pairs)
        (targetKilled A j hp w hw) n S T)+
      ((n+1:ℕ):ℝ)*((6*(xi:ℝ)+1/(2:ℝ)^k)/2) := by
  have he := returnWordDefault_to_path A C hC K j k n hK hW hB hj xi hx0 hx1
    hPL hCheeger v hp w hw S E
  have ht := target_returnDefault_bound A j hp w hw n S E
  have hb := _root_.add_le_add ht
    (le_refl (((n+1:ℕ):ℝ)*((6*(xi:ℝ)+1/(2:ℝ)^k)/2)))
  exact he.trans hb

end
end ContingencyTables.CompanionCappedReturn

end OAI
