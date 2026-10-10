import OAI.Combinatorics.ContingencyTables.Counting.CompanionRestartSemantics
import OAI.Combinatorics.ContingencyTables.Counting.CompanionRestartStageLaw

namespace OAI

/-! # The concrete stored-matrix restart experiment -/
namespace ContingencyTables.CompanionRestartProgram
open MatchingFPRAS CommonBasesFPRAS FirstSuccess FiniteObservableTransport
open CompanionFactorialApplication CompanionComputedInitial CompanionComputedProposal
open CompanionArithmeticProposal CompanionEvaluatedWeightProgram CompanionMultiplierMatrixProgram
open CompanionOracleDensity CompanionWeightOracle TwoLiftStates GridBoundary
open scoped BigOperators Classical
noncomputable section
variable {m n : ℕ}

def stagesData (A : Instance (Fin m) (Fin n)) (C K j : ℕ)
    (parameters : CountingPhaseParametersProgram.Input) (z : View A → ℕ)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) (reserve : List Bool)
    (w : ℕ → LabelIndex A → LabelIndex A → TreeFraction.Fraction) : List Stage :=
  List.ofFn (fun i : Fin j =>
    (CompanionPhaseContextProgram.data A C K (i.val+1) parameters z v reserve,matrixCode (w (i.val+1))))

def baseData (A : Instance (Fin m) (Fin n)) (C K j : ℕ)
    (parameters : CountingPhaseParametersProgram.Input) (z : View A → ℕ)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) (reserve : List Bool)
    (w : ℕ → LabelIndex A → LabelIndex A → TreeFraction.Fraction) (S : Set (Labels A×Bool)) :
    List Stage×List ℕ :=
  (stagesData A C K j parameters z v reserve w,encodeSet (coordinateOrder A) S)

def sourceWidth (A : Instance (Fin m) (Fin n)) (C K : ℕ)
    (parameters : CountingPhaseParametersProgram.Input) (i : ℕ) : ℕ :=
  CountingPhaseParametersProgram.scalar (.input 3) parameters*
    ((CountingPhaseParametersProgram.scalar (.input 5) parameters+1)*
      CompanionBooleanPhase.stepBits A C K (i+1) (CountingPhaseParametersProgram.precision parameters)
        (TreeFraction.val (CountingPhaseParametersProgram.noise parameters)))

lemma request_data (A : Instance (Fin m) (Fin n)) (C K j : ℕ)
    (parameters : CountingPhaseParametersProgram.Input) (z : View A → ℕ)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) (reserve : List Bool)
    (w : ℕ → LabelIndex A → LabelIndex A → TreeFraction.Fraction) (S : Set (Labels A×Bool))
    (i : Fin j) :
    request ((baseData A C K j parameters z v reserve w S,[]),i.val)=
      CompanionRestartStageProgram.data A C K (i.val+1) parameters z v reserve (w (i.val+1)) S := by
  unfold request baseData stagesData
  simp only [List.getD_eq_getElem?_getD,List.getElem?_ofFn,i.isLt,dite_true,Option.getD_some]
  rfl

theorem widthAt_data (A : Instance (Fin m) (Fin n)) (C K j : ℕ)
    (parameters : CountingPhaseParametersProgram.Input) (z : View A → ℕ)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) (reserve : List Bool)
    (w : ℕ → LabelIndex A → LabelIndex A → TreeFraction.Fraction) (S : Set (Labels A×Bool))
    (i : Fin j) :
    widthAt (baseData A C K j parameters z v reserve w S) i.val=
      sourceWidth A C K parameters i.val := by
  unfold widthAt indexedWidth
  rw [request_data,CompanionRestartStageProgram.width_data]
  rfl

def sourceStep (A : Instance (Fin m) (Fin n)) (C K : ℕ)
    (parameters : CountingPhaseParametersProgram.Input) (hK : 1 ≤ K)
    (hW : 100*A.d*K ≤ A.W) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (w : ℕ → LabelIndex A → LabelIndex A → TreeFraction.Fraction) (i : ℕ)
    (S : PlainIndex (pairs : List (CompanionRationalUpdates.Pair A)))
    (bits : Fin (sourceWidth A C K parameters i) → Bool) :
    PlainIndex (pairs : List (CompanionRationalUpdates.Pair A)) :=
  RootedReturnWords.booleanReturns A (RootedCompletion.rowColumn A.T) C K (i+1)
    (CountingPhaseParametersProgram.precision parameters)
    (CountingPhaseParametersProgram.scalar (.input 5) parameters)
    (CountingPhaseParametersProgram.scalar (.input 3) parameters) hK hW
    (TreeFraction.val (CountingPhaseParametersProgram.noise parameters))
    (RootedCatalogGrid.gridEquiv A K v) (sourceWeights A (w (i+1))) S bits

theorem detached_data_sameLaw (A : Instance (Fin m) (Fin n)) (C K j : ℕ)
    (hC : 0 < C) (hH : j ≤ rationalHeight A C) (hK : 1 ≤ K)
    (hW : 100*A.d*K ≤ A.W) (hB : (K:ℝ)=CompanionOracleDensity.binWidth A C)
    (parameters : CountingPhaseParametersProgram.Input)
    (hxi : 0 < TreeFraction.val (CountingPhaseParametersProgram.noise parameters))
    (z : View A → ℕ) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (reserve : List Bool)
    (hdegree : ∀ i : Fin j,RootedOracleConfigProgram.rootDegree
      (CompanionRestartStageProgram.oracleData A C K (i.val+1) parameters z v reserve) ≤ reserve.length)
    (hdepth : ∀ i : Fin j,RootedOracleConfigProgram.depth
      (CompanionRestartStageProgram.oracleData A C K (i.val+1) parameters z v reserve) ≤ reserve.length)
    (w : ℕ → LabelIndex A → LabelIndex A → TreeFraction.Fraction)
    (S₀ : Set (Labels A×Bool)) (i : Fin j)
    (S : PlainIndex (pairs : List (CompanionRationalUpdates.Pair A))) :
    SameLaw (fun bits : Fin (widthAt (baseData A C K j parameters z v reserve w S₀) i.val) → Bool =>
      detachedStep (baseData A C K j parameters z v reserve w S₀) i.val
        (encodeSet (coordinateOrder A) S.val.val) (List.ofFn bits))
      (fun bits => encodeSet (coordinateOrder A)
        (sourceStep A C K parameters hK hW v w i.val S bits).val.val) := by
  have hstage := CompanionRestartStageProgram.output_sameLaw A C K (i.val+1)
    hC (by omega) hK hW hB parameters hxi z v reserve (hdegree i) (hdepth i) (w (i.val+1)) S
  dsimp only at hstage
  have hm := hstage.map (fun code => ProfilePrograms.capView
    (((encodeSet (coordinateOrder A) S₀).length,1),code))
  have hu := widthAt_data A C K j parameters z v reserve w S₀ i
  have ht := SameLaw.word_length hu.symm
    (fun bits => ProfilePrograms.capView (((encodeSet (coordinateOrder A) S₀).length,1),
      CompanionRestartStageProgram.output
        (CompanionRestartStageProgram.data A C K (i.val+1) parameters z v reserve
          (w (i.val+1)) S.val.val,bits)))
    (fun bits => ProfilePrograms.capView (((encodeSet (coordinateOrder A) S₀).length,1),
      encodeSet (coordinateOrder A) (sourceStep A C K parameters hK hW v w i.val S bits).val.val)) hm
  intro phi
  have he : (stagesData A C K j parameters z v reserve w).getD i.val default=
      (CompanionPhaseContextProgram.data A C K (i.val+1) parameters z v reserve,matrixCode (w (i.val+1))) := by
    simp only [stagesData,List.getD_eq_getElem?_getD,List.getElem?_ofFn,i.isLt,dite_true,Option.getD_some]
  simpa only [detachedStep,baseData,he,CompanionRestartStageProgram.data,
    CompanionBoundedWalkProgram.cap_encode] using ht phi

theorem output_data_sameLaw (A : Instance (Fin m) (Fin n)) (C K j : ℕ)
    (hC : 0 < C) (hH : j ≤ rationalHeight A C) (hK : 1 ≤ K)
    (hW : 100*A.d*K ≤ A.W) (hB : (K:ℝ)=CompanionOracleDensity.binWidth A C)
    (parameters : CountingPhaseParametersProgram.Input)
    (hxi : 0 < TreeFraction.val (CountingPhaseParametersProgram.noise parameters))
    (z : View A → ℕ) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (reserve : List Bool)
    (hdegree : ∀ i : Fin j,RootedOracleConfigProgram.rootDegree
      (CompanionRestartStageProgram.oracleData A C K (i.val+1) parameters z v reserve) ≤ reserve.length)
    (hdepth : ∀ i : Fin j,RootedOracleConfigProgram.depth
      (CompanionRestartStageProgram.oracleData A C K (i.val+1) parameters z v reserve) ≤ reserve.length)
    (w : ℕ → LabelIndex A → LabelIndex A → TreeFraction.Fraction)
    (S : PlainIndex (pairs : List (CompanionRationalUpdates.Pair A))) :
    SameLaw (fun bits : Fin (∑ i : Fin (baseData A C K j parameters z v reserve w S.val.val).1.length,
        widthAt (baseData A C K j parameters z v reserve w S.val.val) i.val) → Bool =>
      output (baseData A C K j parameters z v reserve w S.val.val,List.ofFn bits))
      (fun bits : Fin (∑ i : Fin (baseData A C K j parameters z v reserve w S.val.val).1.length,
          sourceWidth A C K parameters i.val) → Bool =>
        encodeSet (coordinateOrder A)
          (varyingWalk (sourceWidth A C K parameters) (sourceStep A C K parameters hK hW v w) S
            (baseData A C K j parameters z v reserve w S.val.val).1.length
            (varyingWordEquiv (sourceWidth A C K parameters)
              (baseData A C K j parameters z v reserve w S.val.val).1.length bits)).val.val) := by
  apply output_sameLaw _ _ _ (fun T => encodeSet (coordinateOrder A) T.val.val) S rfl
  intro i hi T
  have hij : i < j := by simpa only [baseData,stagesData,List.length_ofFn] using hi
  exact detached_data_sameLaw A C K j hC hH hK hW hB parameters hxi z v reserve hdegree hdepth
    w S.val.val ⟨i,hij⟩ T

end
end ContingencyTables.CompanionRestartProgram

end OAI
