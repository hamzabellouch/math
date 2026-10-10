import OAI.Combinatorics.ContingencyTables.Counting.CompanionBoundedWalkProgram
import OAI.Combinatorics.ContingencyTables.Counting.CompanionMetropolisWordSemantics
import OAI.Combinatorics.ContingencyTables.Machines.FiniteEncodedHistory

namespace OAI

/-! # The bounded physical recorder preserves the complete phase history -/

namespace ContingencyTables.CompanionBoundedWalkProgram

open MatchingFPRAS CompanionFactorialApplication CompanionComputedInitial CompanionComputedProposal
open CompanionArithmeticProposal CompanionOracleDensity CompanionWeightOracle
open CompanionEvaluatedWeightProgram CompanionMultiplierMatrixProgram CommonBasesFPRAS
open CompanionBooleanPhase (State)
open FiniteObservableTransport TwoLiftStates GridBoundary
open scoped Classical

def codeStep (fixed : Fixed) (code : List ℕ) (bits : List Bool) : List ℕ :=
  next (bits,(fixed,code))

lemma recordFold_eq (fixed : Fixed) (words : List (List Bool)) (code : List ℕ)
    (past : List (List ℕ)) :
    words.foldl (fun state bits => recordAdvance (bits,state)) ((fixed,code),past)=
      let out := words.foldl (fun state bits =>
        let d := codeStep fixed state.1 bits; (d,d::state.2)) (code,past)
      ((fixed,out.1),out.2) := by
  induction words generalizing code past with
  | nil => rfl
  | cons word words ih =>
    simpa only [List.foldl_cons,recordAdvance,advance,codeStep] using
      ih (next (word,(fixed,code))) (next (word,(fixed,code))::past)

lemma history_eq_trace (fixed : Fixed) (code : List ℕ) (words : List (List Bool)) :
    history ((fixed,code),words)=traceStates (codeStep fixed) code words := by
  unfold history recordWalk initialRecord
  rw [recordFold_eq]
  exact traceStates_fold (codeStep fixed) words code

noncomputable section
variable {m n : ℕ}

lemma cap_encode (A : Instance (Fin m) (Fin n)) (S T : Set (Labels A × Bool)) :
    ProfilePrograms.capView (((encodeSet (coordinateOrder A) S).length,1),
      encodeSet (coordinateOrder A) T)=encodeSet (coordinateOrder A) T := by
  apply ProfilePrograms.capView_eq
  · simp only [encodeSet,List.length_ofFn]
  · intro a ha
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp ha
    unfold ProfilePrograms.setProfile
    split_ifs <;> omega

/-- The all-input clipping has no effect on a valid encoded transition;
in particular its full row law agrees with the reference phase step. -/
theorem codeStep_sameLaw (A : Instance (Fin m) (Fin n)) (C K j k : ℕ)
    (hC : 0 < C) (hj : j ≤ rationalHeight A C) (hK : 1 ≤ K)
    (hW : 100*A.d*K ≤ A.W) (hB : (K:ℝ)=CompanionOracleDensity.binWidth A C)
    (xi : ℚ) (hxi : 0 < xi) (z : View A → ℕ)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) (degree depth : List Bool)
    (hdegree : degree.length=PowerOfTwoApproximation.rootDegree (roundingTolerance (innerTolerance (xi/2) j)))
    (hdepth : depth.length=PowerOfTwoApproximation.depth (roundingTolerance (innerTolerance (xi/2) j)))
    (w : LabelIndex A → LabelIndex A → TreeFraction.Fraction) (S₀ S : CompanionBooleanPhase.State A) :
    let cfg := RootedLabelWeightProgram.config A C K j xi xi z v degree depth
    let fixed : Fixed := (((cfg,matrixCode w),k),encodeSet (coordinateOrder A) S₀.val)
    SameLaw (fun bits : Fin (CompanionBooleanPhase.stepBits A C K j k xi) → Bool =>
      codeStep fixed (encodeSet (coordinateOrder A) S.val) (List.ofFn bits))
      (fun bits => encodeSet (coordinateOrder A)
        (RootedBooleanPhase.step A (RootedCompletion.rowColumn A.T) C K j k hK hW xi
          (RootedCatalogGrid.gridEquiv A K v) (sourceWeights A w) S bits).val) := by
  dsimp only
  have h := CompanionMetropolisWordProgram.sameLaw_flat A C K j k hC hj hK hW hB
    xi hxi z v degree depth hdegree hdepth w S
  have hm := h.map (fun code => ProfilePrograms.capView
    (((encodeSet (coordinateOrder A) S₀.val).length,1),code))
  intro phi
  simpa only [codeStep,next,bound,candidate,transitionInput,CompanionMetropolisWordProgram.packed,
    cap_encode] using hm phi

/-- The physical list recorder and the full reference state history have
the same law, before any first-return scan or phase statistic is applied. -/
theorem history_sameLaw (A : Instance (Fin m) (Fin n)) (C K j k : ℕ)
    (hC : 0 < C) (hj : j ≤ rationalHeight A C) (hK : 1 ≤ K)
    (hW : 100*A.d*K ≤ A.W) (hB : (K:ℝ)=CompanionOracleDensity.binWidth A C)
    (xi : ℚ) (hxi : 0 < xi) (z : View A → ℕ)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) (degree depth : List Bool)
    (hdegree : degree.length=PowerOfTwoApproximation.rootDegree (roundingTolerance (innerTolerance (xi/2) j)))
    (hdepth : depth.length=PowerOfTwoApproximation.depth (roundingTolerance (innerTolerance (xi/2) j)))
    (w : LabelIndex A → LabelIndex A → TreeFraction.Fraction) (S : CompanionBooleanPhase.State A) (N : ℕ) :
    let cfg := RootedLabelWeightProgram.config A C K j xi xi z v degree depth
    let fixed : Fixed := (((cfg,matrixCode w),k),encodeSet (coordinateOrder A) S.val)
    SameLaw (fun words : Fin N → (Fin (CompanionBooleanPhase.stepBits A C K j k xi) → Bool) =>
      history ((fixed,encodeSet (coordinateOrder A) S.val),List.ofFn (fun i => List.ofFn (words i))))
      (fun words : Fin N → (Fin (CompanionBooleanPhase.stepBits A C K j k xi) → Bool) => (traceStates
        (RootedBooleanPhase.step A (RootedCompletion.rowColumn A.T) C K j k hK hW xi
          (RootedCatalogGrid.gridEquiv A K v) (sourceWeights A w)) S (List.ofFn words)).map
          (fun T => encodeSet (coordinateOrder A) T.val)) := by
  dsimp only
  let cfg := RootedLabelWeightProgram.config A C K j xi xi z v degree depth
  let fixed : Fixed := (((cfg,matrixCode w),k),encodeSet (coordinateOrder A) S.val)
  have ht := traceStates_sameLaw
    (fun code bits => codeStep fixed code (List.ofFn bits))
    (RootedBooleanPhase.step A (RootedCompletion.rowColumn A.T) C K j k hK hW xi
      (RootedCatalogGrid.gridEquiv A K v) (sourceWeights A w))
    (fun T : CompanionBooleanPhase.State A => encodeSet (coordinateOrder A) T.val)
    (codeStep_sameLaw A C K j k hC hj hK hW hB xi hxi z v degree depth hdegree hdepth w S) S N
  intro phi
  rw [show (fun words : Fin N → (Fin (CompanionBooleanPhase.stepBits A C K j k xi) → Bool) =>
      phi (history ((fixed,encodeSet (coordinateOrder A) S.val),List.ofFn (fun i => List.ofFn (words i)))))=
      (fun words => phi (traceStates (fun code bits => codeStep fixed code (List.ofFn bits))
        (encodeSet (coordinateOrder A) S.val) (List.ofFn words))) by
    funext words
    rw [history_eq_trace]
    have hm : List.ofFn (fun i => List.ofFn (words i))=(List.ofFn words).map List.ofFn := by
      rw [List.map_ofFn]
      rfl
    rw [hm,traceStates_map]]
  exact ht phi

end
end ContingencyTables.CompanionBoundedWalkProgram

end OAI
