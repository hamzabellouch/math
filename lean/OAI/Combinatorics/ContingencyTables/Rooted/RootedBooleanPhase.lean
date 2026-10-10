import OAI.Combinatorics.ContingencyTables.Rooted.RootedOracleAcceptance
import OAI.Combinatorics.ContingencyTables.Counting.CompanionBooleanPhase

namespace OAI

/-! # Actual finite-word Metropolis steps using the selected-root oracle -/

namespace ContingencyTables.RootedBooleanPhase

open CompanionFactorialApplication CompanionOracleDensity CompanionWeightOracle CompanionRationalUpdates
open CommonBasesFPRAS FirstSuccess FairBits TwoLiftStates GridBoundary ResidualMixture
open CompanionBooleanPhase (State proposal proposal_mass proposalBits proposal_codes stepBits stepWordEquiv)
open scoped BigOperators Classical

noncomputable section
variable {I J : Type*} [Fintype I] [Fintype J]

/-- The realized step evaluates the current and proposed weights from
separate words, then uses a third independent word for its rational coin. -/
def step (A : Instance I J) (R : RootedCompletion.Selection A.T) (C K j k : ℕ)
    (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (xi : ℚ)
    (v : Grid (I := Fin (dimension A)) K) (w : Pair A → Pair A → ℚ)
    (S : State A) (bits : Fin (stepBits A C K j k xi) → Bool) : State A :=
  let b := stepWordEquiv A C K j k xi bits
  if b.1 0 then S else
    match proposal A S b.2.1 with
    | none => S
    | some T =>
        if rationalThresholdAccept k
          (RootedOracleAcceptance.acceptance A R C K j hK hW xi v w S.val T.val b.2.2.1) b.2.2.2
        then T else S

/-- A nontrivial move uses exactly its proposal code and the fresh
acceptance experiment. Failed codes and the independent holding bit
contribute only to the diagonal. -/
theorem step_eq_iff (A : Instance I J) (R : RootedCompletion.Selection A.T) (C K j k : ℕ)
    (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (xi : ℚ)
    (v : Grid (I := Fin (dimension A)) K) (w : Pair A → Pair A → ℚ)
    (S T : State A) (hST : S ≠ T) (bits : Fin (stepBits A C K j k xi) → Bool) :
    step A R C K j k hK hW xi v w S bits=T ↔
      (stepWordEquiv A C K j k xi bits).1 0=false ∧
      proposal A S (stepWordEquiv A C K j k xi bits).2.1=some T ∧
      rationalThresholdAccept k
        (RootedOracleAcceptance.acceptance A R C K j hK hW xi v w S.val T.val
          (stepWordEquiv A C K j k xi bits).2.2.1)
        (stepWordEquiv A C K j k xi bits).2.2.2 := by
  dsimp only [step]
  generalize stepWordEquiv A C K j k xi bits = b
  cases b.1 0 with
  | true => simp [hST]
  | false =>
    cases proposal A S b.2.1 with
    | none => simp [hST]
    | some U =>
      by_cases hUT : U=T
      · subst U
        simp [hST]
      · by_cases ha : rationalThresholdAccept k
          (RootedOracleAcceptance.acceptance A R C K j hK hW xi v w S.val U.val b.2.2.1) b.2.2.2
        · simp [hUT,ha]
        · simp [hST,hUT,ha]

def transitionLaw (A : Instance I J) (R : RootedCompletion.Selection A.T) (C K j k : ℕ)
    (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (xi : ℚ)
    (v : Grid (I := Fin (dimension A)) K) (w : Pair A → Pair A → ℚ) (S : State A) :
    RationalLaw (State A) :=
  mapLaw (uniformLaw (α := Fin (stepBits A C K j k xi) → Bool))
    (step A R C K j k hK hW xi v w S)

def walk (A : Instance I J) (R : RootedCompletion.Selection A.T) (C K j k n : ℕ)
    (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (xi : ℚ)
    (v : Grid (I := Fin (dimension A)) K) (w : Pair A → Pair A → ℚ) (S : State A)
    (bits : Fin (n*stepBits A C K j k xi) → Bool) : State A :=
  wordWalk (step A R C K j k hK hW xi v w) S n
    (oracleWalkWordEquiv n (stepBits A C K j k xi) bits)

/-- The actual flattened word gives independent repeated transitions;
its law follows from the accepted finite-word walk construction. -/
theorem walk_law (A : Instance I J) (R : RootedCompletion.Selection A.T) (C K j k n : ℕ)
    (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (xi : ℚ)
    (v : Grid (I := Fin (dimension A)) K) (w : Pair A → Pair A → ℚ) (S : State A) :
    mapLaw (uniformLaw (α := Fin (n*stepBits A C K j k xi) → Bool))
      (walk A R C K j k n hK hW xi v w S)=
        walkLaw (transitionLaw A R C K j k hK hW xi v w) S n := by
  unfold walk
  rw [←map_equiv (oracleWalkWordEquiv n (stepBits A C K j k xi)),uniform_equiv]
  exact wordWalkLaw_eq _ _ _

end
end ContingencyTables.RootedBooleanPhase

end OAI
