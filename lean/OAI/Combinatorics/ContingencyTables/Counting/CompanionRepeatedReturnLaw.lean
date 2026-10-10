import OAI.Combinatorics.ContingencyTables.Counting.CompanionRepeatedReturnProgram
import OAI.Combinatorics.ContingencyTables.Rooted.RootedReturnHistoryLaw
import OAI.Combinatorics.ContingencyTables.Rooted.RootedReturnWords

namespace OAI

/-! # The physical return loop has the actual repeated-return law -/

namespace ContingencyTables.CompanionRepeatedReturnProgram

open MatchingFPRAS CommonBasesFPRAS FirstSuccess ResidualMixture
open CompanionFactorialApplication CompanionOracleDensity CompanionWeightOracle
open CompanionComputedInitial CompanionComputedProposal CompanionArithmeticProposal
open CompanionEvaluatedWeightProgram CompanionMultiplierMatrixProgram
open FiniteObservableTransport TwoLiftStates GridBoundary
open scoped Classical

noncomputable section
variable {m n : ℕ}

def fixedData (A : Instance (Fin m) (Fin n)) (C K j k cap : ℕ) (xi : ℚ)
    (z : View A → ℕ) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (degree depth : List Bool) (w : LabelIndex A → LabelIndex A → TreeFraction.Fraction)
    (S₀ : Set (Labels A × Bool)) : Fixed :=
  ((((RootedLabelWeightProgram.config A C K j xi xi z v degree depth,matrixCode w),k),
    encodeSet (coordinateOrder A) S₀),cap)

def data (A : Instance (Fin m) (Fin n)) (C K j k cap t : ℕ) (xi : ℚ)
    (z : View A → ℕ) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (degree depth : List Bool) (w : LabelIndex A → LabelIndex A → TreeFraction.Fraction)
    (S : Set (Labels A × Bool)) (bits : List Bool) : Input :=
  (((fixedData A C K j k cap xi z v degree depth w S,
    encodeSet (coordinateOrder A) S),t),bits)

def codeStep (fixed : Fixed) (code : List ℕ) (bits : List Bool) : List ℕ :=
  next (bits,(fixed,code))

lemma walk_eq (fixed : Fixed) (words : List (List Bool)) (code : List ℕ) :
    walk ((fixed,code),words)=(fixed,words.foldl (codeStep fixed) code) := by
  induction words generalizing code with
  | nil => rfl
  | cons word words ih =>
    simpa only [walk,List.foldl_cons,advance,codeStep] using ih (next (word,(fixed,code)))

lemma blockWidth_data (A : Instance (Fin m) (Fin n)) (C K j k cap : ℕ) (xi : ℚ)
    (z : View A → ℕ) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (degree depth : List Bool) (w : LabelIndex A → LabelIndex A → TreeFraction.Fraction)
    (S : Set (Labels A × Bool)) :
    blockWidth (fixedData A C K j k cap xi z v degree depth w S)=
      (cap+1)*CompanionBooleanPhase.stepBits A C K j k xi := by
  unfold blockWidth widthInput fixedData
  dsimp only
  exact congrArg (fun width : ℕ => (cap+1)*width)
    (CompanionTransitionWidth.width_config A C K j k xi z v degree depth (matrixCode w) S [])

lemma words_data (A : Instance (Fin m) (Fin n)) (C K j k cap t : ℕ) (xi : ℚ)
    (z : View A → ℕ) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (degree depth : List Bool) (w : LabelIndex A → LabelIndex A → TreeFraction.Fraction)
    (S : Set (Labels A × Bool))
    (bits : Fin (t*((cap+1)*CompanionBooleanPhase.stepBits A C K j k xi)) → Bool) :
    words (data A C K j k cap t xi z v degree depth w S (List.ofFn bits))=
      List.ofFn (fun i : Fin t => List.ofFn (gridWordEquiv t
        ((cap+1)*CompanionBooleanPhase.stepBits A C K j k xi) bits i)) := by
  unfold words data
  dsimp only
  rw [blockWidth_data]
  rw [DensePrograms.wordChunks_ofFn (by unfold CompanionBooleanPhase.stepBits; positivity)]
  exact List.take_of_length_le (by simp only [List.length_ofFn]; exact le_rfl)

theorem codeStep_sameLaw (A : Instance (Fin m) (Fin n)) (C K j k cap : ℕ)
    (hC : 0 < C) (hj : j ≤ rationalHeight A C) (hK : 1 ≤ K)
    (hW : 100*A.d*K ≤ A.W) (hB : (K:ℝ)=CompanionOracleDensity.binWidth A C)
    (xi : ℚ) (hxi : 0 < xi) (z : View A → ℕ)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) (degree depth : List Bool)
    (hdegree : degree.length=PowerOfTwoApproximation.rootDegree (roundingTolerance (innerTolerance (xi/2) j)))
    (hdepth : depth.length=PowerOfTwoApproximation.depth (roundingTolerance (innerTolerance (xi/2) j)))
    (w : LabelIndex A → LabelIndex A → TreeFraction.Fraction)
    (S₀ : Set (Labels A × Bool)) (S : PlainIndex (pairs : List (CompanionRationalUpdates.Pair A))) :
    SameLaw (fun bits : Fin ((cap+1)*CompanionBooleanPhase.stepBits A C K j k xi) → Bool =>
      codeStep (fixedData A C K j k cap xi z v degree depth w S₀)
        (encodeSet (coordinateOrder A) S.val.val) (List.ofFn bits))
      (fun bits => encodeSet (coordinateOrder A)
        (RootedCappedReturn.returnWordDefault A (RootedCompletion.rowColumn A.T) C K j k cap hK hW xi
          (RootedCatalogGrid.gridEquiv A K v) (sourceWeights A w) S bits).val.val) := by
  have h := RootedReturnHistoryLaw.flatReturn_sameLaw A C K j k cap hC hj hK hW hB xi hxi
    z v degree depth hdegree hdepth w S
  have hm := h.map (fun code => ProfilePrograms.capView
    (((encodeSet (coordinateOrder A) S₀).length,1),code))
  intro phi
  simpa only [codeStep,next,bound,candidate,returnInput,fixedData,
    CompanionFlatReturnProgram.data,CompanionFlatReturnProgram.stateData,
    CompanionBoundedWalkProgram.cap_encode] using hm phi

private lemma wordWalk_fold {X : Type*} {k : ℕ}
    (F : X → (Fin k → Bool) → X) (x : X) (t : ℕ) (bits : Fin t → Fin k → Bool) :
    wordWalk F x t bits=(List.ofFn bits).foldl F x := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [wordWalk,ih,List.ofFn_succ',List.concat_eq_append,List.foldl_append]
    rfl

/-- Independent physical return blocks preserve the entire repeated
return distribution, including fallback events in every block. -/
theorem output_sameLaw (A : Instance (Fin m) (Fin n)) (C K j k cap t : ℕ)
    (hC : 0 < C) (hj : j ≤ rationalHeight A C) (hK : 1 ≤ K)
    (hW : 100*A.d*K ≤ A.W) (hB : (K:ℝ)=CompanionOracleDensity.binWidth A C)
    (xi : ℚ) (hxi : 0 < xi) (z : View A → ℕ)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) (degree depth : List Bool)
    (hdegree : degree.length=PowerOfTwoApproximation.rootDegree (roundingTolerance (innerTolerance (xi/2) j)))
    (hdepth : depth.length=PowerOfTwoApproximation.depth (roundingTolerance (innerTolerance (xi/2) j)))
    (w : LabelIndex A → LabelIndex A → TreeFraction.Fraction)
    (S : PlainIndex (pairs : List (CompanionRationalUpdates.Pair A))) :
    SameLaw (fun bits : Fin (t*((cap+1)*CompanionBooleanPhase.stepBits A C K j k xi)) → Bool =>
      output (data A C K j k cap t xi z v degree depth w S.val.val (List.ofFn bits)))
      (fun bits => encodeSet (coordinateOrder A)
        (RootedReturnWords.booleanReturns A (RootedCompletion.rowColumn A.T) C K j k cap t hK hW xi
          (RootedCatalogGrid.gridEquiv A K v) (sourceWeights A w) S bits).val.val) := by
  let fixed := fixedData A C K j k cap xi z v degree depth w S.val.val
  let F := fun (code : List ℕ)
    (bits : Fin ((cap+1)*CompanionBooleanPhase.stepBits A C K j k xi) → Bool) =>
    codeStep fixed code (List.ofFn bits)
  let G := RootedCappedReturn.returnWordDefault A (RootedCompletion.rowColumn A.T) C K j k cap hK hW xi
    (RootedCatalogGrid.gridEquiv A K v) (sourceWeights A w)
  let encode := fun T : PlainIndex (pairs : List (CompanionRationalUpdates.Pair A)) =>
    encodeSet (coordinateOrder A) T.val.val
  have hh := foldl_sameLaw F G encode
    (codeStep_sameLaw A C K j k cap hC hj hK hW hB xi hxi z v degree depth hdegree hdepth w S.val.val) S t
  let E := gridWordEquiv t ((cap+1)*CompanionBooleanPhase.stepBits A C K j k xi)
  have hout (bits : Fin (t*((cap+1)*CompanionBooleanPhase.stepBits A C K j k xi)) → Bool) :
      output (data A C K j k cap t xi z v degree depth w S.val.val (List.ofFn bits))=
        (List.ofFn (E bits)).foldl F (encode S) := by
    unfold output
    rw [words_data]
    change (walk ((fixed,encode S),List.ofFn (fun i => List.ofFn (E bits i)))).2=_
    rw [walk_eq]
    have he : List.ofFn (fun i => List.ofFn (E bits i))=(List.ofFn (E bits)).map List.ofFn := by
      rw [List.map_ofFn]
      rfl
    rw [he,List.foldl_map]
  intro phi
  have hleft := uniformAverage_equiv E
    (fun bs => phi ((List.ofFn bs).foldl F (encode S)))
  have hright := uniformAverage_equiv E
    (fun bs => phi (encode ((List.ofFn bs).foldl G S)))
  calc
    _ = uniformAverage (fun bits => phi ((List.ofFn (E bits)).foldl F (encode S))) := by
      apply congrArg uniformAverage
      funext bits
      dsimp only
      rw [hout]
    _ = uniformAverage (fun bs => phi ((List.ofFn bs).foldl F (encode S))) := hleft
    _ = uniformAverage (fun bs => phi (encode ((List.ofFn bs).foldl G S))) := hh phi
    _ = uniformAverage (fun bits => phi (encode ((List.ofFn (E bits)).foldl G S))) := hright.symm
    _ = _ := by
      apply congrArg uniformAverage
      funext bits
      dsimp only
      change phi (encode ((List.ofFn (E bits)).foldl G S))=
        phi (encode (wordWalk G S t (E bits)))
      rw [wordWalk_fold]

end
end ContingencyTables.CompanionRepeatedReturnProgram

end OAI
