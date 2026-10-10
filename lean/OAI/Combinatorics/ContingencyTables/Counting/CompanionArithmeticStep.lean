import OAI.Combinatorics.ContingencyTables.Counting.CompanionArithmeticProposal
import OAI.Combinatorics.ContingencyTables.Counting.CompanionPhaseTrajectory

namespace OAI

/-! # Coordinate arithmetic for the companion proposal

The arithmetic and abstract proposals consume equal fixed word lengths.
Oracle and acceptance words are disjoint, and their full one-step laws
agree, giving the same trajectory error bound.
-/

namespace ContingencyTables.CompanionArithmeticStep
open CommonBasesFPRAS FirstSuccess ResidualMixture FairBits GridBoundary
open CompanionFactorialApplication CompanionOracleDensity CompanionWeightOracle
open CompanionBooleanPhase RealKernelApproximation
open scoped BigOperators Classical

noncomputable section

private def regroup (L P Q : Type*) : (L×(P×Q)) ≃ P×(L×Q) where
  toFun b := (b.2.1,(b.1,b.2.2))
  invFun b := (b.2.1,(b.1,b.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

private lemma word_finish_law {B P Q X Z : Type*}
    [Fintype B] [Fintype P] [Fintype Q] [Fintype X] [Fintype Z]
    [Nonempty B] [Nonempty P] [Nonempty Q] [DecidableEq X] [DecidableEq Z]
    (E : B ≃ P×Q) (draw : P → X) (finish : X → Q → Z) :
    mapLaw (uniformLaw (α := B)) (fun b => finish (draw (E b).1) (E b).2)=
      bindLaw (mapLaw (uniformLaw (α := P)) draw)
        (fun x => mapLaw (uniformLaw (α := Q)) (finish x)) := by
  have he := map_equiv E (uniformLaw (α := B)) (fun b : P×Q => finish (draw b.1) b.2)
  rw [uniform_equiv,←uniform_product] at he
  exact he.symm.trans (mapLaw_product_finish _ _ draw finish)

variable {I J : Type} [Fintype I] [Fintype J]

abbrev RestWord (A : Instance I J) (C K j k : ℕ) (xi : ℚ) :=
  (Fin 1 → Bool)×((WeightWord A C K j xi×WeightWord A C K j xi)×(Fin k → Bool))

def wordSplit (A : Instance I J) (C K j k : ℕ) (xi : ℚ) :
    (Fin (stepBits A C K j k xi) → Bool) ≃
      ((Fin (proposalBits A) → Bool)×RestWord A C K j k xi) :=
  (stepWordEquiv A C K j k xi).trans (regroup _ _ _)

def finish (A : Instance I J) (C K j k : ℕ)
    (hK : 1≤K) (hW : 100*A.d*K≤A.W) (xi : ℚ)
    (v : Grid (I := Fin (dimension A)) K) (w : CompanionRationalUpdates.Pair A → CompanionRationalUpdates.Pair A → ℚ)
    (S : State A) (U : Option (State A)) (rest : RestWord A C K j k xi) : State A :=
  if rest.1 0 then S else
    match U with
    | none => S
    | some T =>
        if rationalThresholdAccept k
          (CompanionOracleAcceptance.acceptance A C K j hK hW xi v w S.val T.val rest.2.1)
          rest.2.2 then T else S

def step (A : Instance I J) (C K j k : ℕ)
    (hK : 1≤K) (hW : 100*A.d*K≤A.W) (xi : ℚ)
    (v : Grid (I := Fin (dimension A)) K) (w : CompanionRationalUpdates.Pair A → CompanionRationalUpdates.Pair A → ℚ)
    (S : State A) (bits : Fin (stepBits A C K j k xi) → Bool) : State A :=
  let b := wordSplit A C K j k xi bits
  finish A C K j k hK hW xi v w S (CompanionArithmeticProposal.proposal A S b.1) b.2

private lemma source_step_eq_finish (A : Instance I J) (C K j k : ℕ)
    (hK : 1≤K) (hW : 100*A.d*K≤A.W) (xi : ℚ)
    (v : Grid (I := Fin (dimension A)) K) (w : CompanionRationalUpdates.Pair A → CompanionRationalUpdates.Pair A → ℚ)
    (S : State A) :
    (fun bits => finish A C K j k hK hW xi v w S
      (CompanionBooleanPhase.proposal A S (wordSplit A C K j k xi bits).1)
      (wordSplit A C K j k xi bits).2)=
      CompanionBooleanPhase.step A C K j k hK hW xi v w S := by
  funext bits
  simp only [finish,wordSplit,regroup,CompanionBooleanPhase.step,Equiv.trans_apply,Equiv.coe_fn_mk]
  by_cases hlazy : (stepWordEquiv A C K j k xi bits).1 0 = true
  · simp only [hlazy,ite_true]
  · simp only [hlazy]
    cases CompanionBooleanPhase.proposal A S
      (stepWordEquiv A C K j k xi bits).2.1 with
    | none => simp only
    | some T =>
      simp only
      by_cases haccept : rationalThresholdAccept k
        (CompanionOracleAcceptance.acceptance A C K j hK hW xi v w S.val T.val
          (stepWordEquiv A C K j k xi bits).2.2.1)
        (stepWordEquiv A C K j k xi bits).2.2.2
      · simp only [haccept,ite_true]
      · simp only [haccept,ite_false]

/-- Exact equality of complete one-step laws, including all holding
probability. Weight calls and the acceptance coin have not been reused. -/
theorem step_law (A : Instance I J) (C K j k : ℕ)
    (hK : 1≤K) (hW : 100*A.d*K≤A.W) (xi : ℚ)
    (v : Grid (I := Fin (dimension A)) K) (w : CompanionRationalUpdates.Pair A → CompanionRationalUpdates.Pair A → ℚ)
    (S : State A) :
    mapLaw (uniformLaw (α := Fin (stepBits A C K j k xi) → Bool))
      (step A C K j k hK hW xi v w S)=
        transitionLaw A C K j k hK hW xi v w S := by
  have hnew := word_finish_law (wordSplit A C K j k xi)
    (CompanionArithmeticProposal.proposal A S) (finish A C K j k hK hW xi v w S)
  have hold := word_finish_law (wordSplit A C K j k xi)
    (CompanionBooleanPhase.proposal A S) (finish A C K j k hK hW xi v w S)
  change mapLaw _ (fun bits => finish A C K j k hK hW xi v w S
    (CompanionArithmeticProposal.proposal A S (wordSplit A C K j k xi bits).1)
    (wordSplit A C K j k xi bits).2)=_
  rw [hnew,CompanionArithmeticProposal.proposal_law]
  rw [source_step_eq_finish] at hold
  exact hold.symm

/-- The full recorded finite-word path therefore retains the proved
joint-history distribution, rather than merely its terminal marginal. -/
def recordedWalk (A : Instance I J) (C K j k N n : ℕ)
    (hK : 1≤K) (hW : 100*A.d*K≤A.W) (xi : ℚ)
    (v : Grid (I := Fin (dimension A)) K) (w : CompanionRationalUpdates.Pair A → CompanionRationalUpdates.Pair A → ℚ)
    (S : State A) (bits : Fin (n*stepBits A C K j k xi) → Bool) : PathState (State A) N :=
  wordWalk (fun a b => pathPut a (step A C K j k hK hW xi v w (pathRead a) b))
    (pathInitial N S) n (oracleWalkWordEquiv n (stepBits A C K j k xi) bits)

theorem recordedWalk_law (A : Instance I J) (C K j k N n : ℕ)
    (hK : 1≤K) (hW : 100*A.d*K≤A.W) (xi : ℚ)
    (v : Grid (I := Fin (dimension A)) K) (w : CompanionRationalUpdates.Pair A → CompanionRationalUpdates.Pair A → ℚ)
    (S : State A) :
    mapLaw (uniformLaw (α := Fin (n*stepBits A C K j k xi) → Bool))
      (recordedWalk A C K j k N n hK hW xi v w S)=
        pathLaw A C K j k N n hK hW xi v w S := by
  unfold recordedWalk pathLaw
  rw [←map_equiv (oracleWalkWordEquiv n (stepBits A C K j k xi)),uniform_equiv]
  rw [show mapLaw (uniformLaw (α := Fin n → Fin (stepBits A C K j k xi) → Bool))
      (wordWalk (fun a b => pathPut a (step A C K j k hK hW xi v w (pathRead a) b))
        (pathInitial N S) n)=
      wordWalkLaw (fun a b => pathPut a (step A C K j k hK hW xi v w (pathRead a) b))
        (pathInitial N S) n from rfl,wordWalkLaw_eq]
  congr 1
  funext a
  rw [←mapLaw_comp,step_law]
  rfl

end
end ContingencyTables.CompanionArithmeticStep

end OAI
