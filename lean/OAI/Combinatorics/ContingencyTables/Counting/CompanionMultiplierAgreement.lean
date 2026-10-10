import OAI.Combinatorics.ContingencyTables.Rooted.RootedReturnWords

namespace OAI

/-! # Only canonical pair entries affect the executed chain

The finite matrix stores one entry per pair of labels. Values of the
mathematical multiplier on arbitrary noncanonical coordinate pairs
do not affect any weight call, acceptance decision, or capped return.
-/

namespace ContingencyTables.CompanionMultiplierAgreement

open CommonBasesFPRAS CompanionFactorialApplication CompanionRationalUpdates
open CompanionOracleDensity CompanionWeightOracle TwoLiftStates GridBoundary
open CompanionBooleanPhase (State stepBits)
open scoped Classical

noncomputable section

lemma rationalMultiplier_congr {Γ : Type*} [Fintype Γ] [DecidableEq Γ]
    (gs : List (Γ × Γ)) (w w' : (Γ × Γ) → (Γ × Γ) → ℚ)
    (hw : ∀ p ∈ gs, ∀ q ∈ gs, w p q=w' p q) (S : Set Γ) :
    rationalMultiplier gs w S=rationalMultiplier gs w' S := by
  unfold rationalMultiplier
  split_ifs with h
  · exact hw _ h.choose_spec.choose_spec.1 _ h.choose_spec.choose_spec.2.1
  · rfl

variable {I J : Type} [Fintype I] [Fintype J]

def Agree (A : Instance I J) (w w' : Pair A → Pair A → ℚ) : Prop :=
  ∀ a b : Labels A, w (pair a) (pair b)=w' (pair a) (pair b)

lemma agree_on_pairs (A : Instance I J) (w w' : Pair A → Pair A → ℚ)
    (hw : Agree A w w') :
    ∀ p ∈ (pairs : List (Pair A)), ∀ q ∈ (pairs : List (Pair A)), w p q=w' p q := by
  intro p hp q hq
  obtain ⟨a,_,rfl⟩ := List.mem_map.mp hp
  obtain ⟨b,_,rfl⟩ := List.mem_map.mp hq
  exact hw a b

lemma multiplier_eq (A : Instance I J) (w w' : Pair A → Pair A → ℚ)
    (hw : Agree A w w') (S : Set (Labels A × Bool)) :
    rationalMultiplier pairs w S=rationalMultiplier pairs w' S :=
  rationalMultiplier_congr pairs w w' (agree_on_pairs A w w' hw) S

lemma evaluatedWeight_eq (A : Instance I J) (R : RootedCompletion.Selection A.T)
    (C K j : ℕ) (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (xi : ℚ)
    (v : Grid (I := Fin (dimension A)) K) (w w' : Pair A → Pair A → ℚ)
    (hw : Agree A w w') (S : Set (Labels A × Bool)) (bits : WeightWord A C K j xi) :
    RootedOracleAcceptance.evaluatedWeight A R C K j hK hW xi v w S bits=
      RootedOracleAcceptance.evaluatedWeight A R C K j hK hW xi v w' S bits := by
  unfold RootedOracleAcceptance.evaluatedWeight
  rw [multiplier_eq A w w' hw]

lemma acceptance_eq (A : Instance I J) (R : RootedCompletion.Selection A.T)
    (C K j : ℕ) (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (xi : ℚ)
    (v : Grid (I := Fin (dimension A)) K) (w w' : Pair A → Pair A → ℚ)
    (hw : Agree A w w') :
    RootedOracleAcceptance.acceptance A R C K j hK hW xi v w=
      RootedOracleAcceptance.acceptance A R C K j hK hW xi v w' := by
  funext S T bits
  unfold RootedOracleAcceptance.acceptance
  rw [evaluatedWeight_eq A R C K j hK hW xi v w w' hw,
    evaluatedWeight_eq A R C K j hK hW xi v w w' hw]

lemma step_eq (A : Instance I J) (R : RootedCompletion.Selection A.T)
    (C K j k : ℕ) (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (xi : ℚ)
    (v : Grid (I := Fin (dimension A)) K) (w w' : Pair A → Pair A → ℚ)
    (hw : Agree A w w') :
    RootedBooleanPhase.step A R C K j k hK hW xi v w=
      RootedBooleanPhase.step A R C K j k hK hW xi v w' := by
  funext S bits
  unfold RootedBooleanPhase.step
  rw [acceptance_eq A R C K j hK hW xi v w w' hw]

lemma arithmeticFinish_eq (A : Instance I J) (R : RootedCompletion.Selection A.T)
    (C K j k : ℕ) (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (xi : ℚ)
    (v : Grid (I := Fin (dimension A)) K) (w w' : Pair A → Pair A → ℚ)
    (hw : Agree A w w') :
    RootedArithmeticStep.finish A R C K j k hK hW xi v w=
      RootedArithmeticStep.finish A R C K j k hK hW xi v w' := by
  funext S U bits
  unfold RootedArithmeticStep.finish
  rw [acceptance_eq A R C K j hK hW xi v w w' hw]

lemma arithmeticStep_eq (A : Instance I J) (R : RootedCompletion.Selection A.T)
    (C K j k : ℕ) (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (xi : ℚ)
    (v : Grid (I := Fin (dimension A)) K) (w w' : Pair A → Pair A → ℚ)
    (hw : Agree A w w') :
    RootedArithmeticStep.step A R C K j k hK hW xi v w=
      RootedArithmeticStep.step A R C K j k hK hW xi v w' := by
  funext S bits
  unfold RootedArithmeticStep.step
  rw [arithmeticFinish_eq A R C K j k hK hW xi v w w' hw]

lemma recordedWalk_eq (A : Instance I J) (R : RootedCompletion.Selection A.T)
    (C K j k N n : ℕ) (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (xi : ℚ)
    (v : Grid (I := Fin (dimension A)) K) (w w' : Pair A → Pair A → ℚ)
    (hw : Agree A w w') :
    RootedArithmeticStep.recordedWalk A R C K j k N n hK hW xi v w=
      RootedArithmeticStep.recordedWalk A R C K j k N n hK hW xi v w' := by
  funext S bits
  unfold RootedArithmeticStep.recordedWalk
  rw [arithmeticStep_eq A R C K j k hK hW xi v w w' hw]

lemma return_eq (A : Instance I J) (R : RootedCompletion.Selection A.T)
    (C K j k n : ℕ) (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (xi : ℚ)
    (v : Grid (I := Fin (dimension A)) K) (w w' : Pair A → Pair A → ℚ)
    (hw : Agree A w w') :
    RootedCappedReturn.returnWordDefault A R C K j k n hK hW xi v w=
      RootedCappedReturn.returnWordDefault A R C K j k n hK hW xi v w' := by
  funext S bits
  unfold RootedCappedReturn.returnWordDefault RootedTraceWords.returnWord
  rw [recordedWalk_eq A R C K j k (n+1) (n+1) hK hW xi v w w' hw]

lemma returns_eq (A : Instance I J) (R : RootedCompletion.Selection A.T)
    (C K j k n t : ℕ) (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (xi : ℚ)
    (v : Grid (I := Fin (dimension A)) K) (w w' : Pair A → Pair A → ℚ)
    (hw : Agree A w w') :
    RootedReturnWords.booleanReturns A R C K j k n t hK hW xi v w=
      RootedReturnWords.booleanReturns A R C K j k n t hK hW xi v w' := by
  funext S bits
  unfold RootedReturnWords.booleanReturns
  rw [return_eq A R C K j k n hK hW xi v w w' hw]

end
end ContingencyTables.CompanionMultiplierAgreement

end OAI
