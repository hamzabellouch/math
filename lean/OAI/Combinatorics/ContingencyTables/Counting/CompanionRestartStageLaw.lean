import OAI.Combinatorics.ContingencyTables.Counting.CompanionRestartStageProgram
import OAI.Combinatorics.ContingencyTables.Counting.CompanionRepeatedReturnLaw

namespace OAI

/-! # The computed restart stage is the literal finite-word return law -/
namespace ContingencyTables.CompanionRestartStageProgram
open MatchingFPRAS CommonBasesFPRAS CompanionFactorialApplication
open CompanionOracleDensity CompanionWeightOracle CompanionComputedInitial
open CompanionComputedProposal CompanionArithmeticProposal CompanionMultiplierMatrixProgram
open CompanionEvaluatedWeightProgram
open FiniteObservableTransport TwoLiftStates GridBoundary
open scoped Classical
noncomputable section
variable {m n : ℕ}

def oracleData (A : Instance (Fin m) (Fin n)) (C K j : ℕ)
    (parameters : CountingPhaseParametersProgram.Input) (z : View A → ℕ)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) (reserve : List Bool) :
    RootedOracleConfigProgram.Input :=
  RootedOracleConfigProgram.data A C K j (CountingPhaseParametersProgram.noise parameters)
    z v (List.replicate reserve.length false)

def degree (A : Instance (Fin m) (Fin n)) (C K j : ℕ)
    (parameters : CountingPhaseParametersProgram.Input) (z : View A → ℕ)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) (reserve : List Bool) : List Bool :=
  (List.replicate reserve.length false).take
    (RootedOracleConfigProgram.rootDegree (oracleData A C K j parameters z v reserve))

def depth (A : Instance (Fin m) (Fin n)) (C K j : ℕ)
    (parameters : CountingPhaseParametersProgram.Input) (z : View A → ℕ)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) (reserve : List Bool) : List Bool :=
  (List.replicate reserve.length false).take
    (RootedOracleConfigProgram.depth (oracleData A C K j parameters z v reserve))

def data (A : Instance (Fin m) (Fin n)) (C K j : ℕ)
    (parameters : CountingPhaseParametersProgram.Input) (z : View A → ℕ)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) (reserve : List Bool)
    (w : LabelIndex A → LabelIndex A → TreeFraction.Fraction) (S : Set (Labels A×Bool)) : Request :=
  ((CompanionPhaseContextProgram.data A C K j parameters z v reserve,matrixCode w),
    encodeSet (coordinateOrder A) S)

lemma config_data (A : Instance (Fin m) (Fin n)) (C K j : ℕ)
    (parameters : CountingPhaseParametersProgram.Input) (z : View A → ℕ)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) (reserve : List Bool)
    (w : LabelIndex A → LabelIndex A → TreeFraction.Fraction) (S : Set (Labels A×Bool)) :
    CompanionPhaseContextProgram.config (context (data A C K j parameters z v reserve w S))=
      RootedLabelWeightProgram.config A C K j
        (TreeFraction.val (CountingPhaseParametersProgram.noise parameters))
        (TreeFraction.val (CountingPhaseParametersProgram.noise parameters)) z v
        (degree A C K j parameters z v reserve) (depth A C K j parameters z v reserve) := by
  unfold context data
  rw [CompanionPhaseContextProgram.config_data,RootedOracleConfigProgram.output_data]
  rfl

lemma fixed_data (A : Instance (Fin m) (Fin n)) (C K j : ℕ)
    (parameters : CountingPhaseParametersProgram.Input) (z : View A → ℕ)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) (reserve : List Bool)
    (w : LabelIndex A → LabelIndex A → TreeFraction.Fraction) (S : Set (Labels A×Bool)) :
    fixed (data A C K j parameters z v reserve w S)=
      CompanionRepeatedReturnProgram.fixedData A C K j
        (CountingPhaseParametersProgram.precision parameters)
        (CountingPhaseParametersProgram.scalar (.input 5) parameters)
        (TreeFraction.val (CountingPhaseParametersProgram.noise parameters)) z v
        (degree A C K j parameters z v reserve) (depth A C K j parameters z v reserve) w S := by
  unfold fixed frame
  rw [config_data]
  rfl

lemma prepare_data (A : Instance (Fin m) (Fin n)) (C K j : ℕ)
    (parameters : CountingPhaseParametersProgram.Input) (z : View A → ℕ)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) (reserve : List Bool)
    (w : LabelIndex A → LabelIndex A → TreeFraction.Fraction) (S : Set (Labels A×Bool))
    (bits : List Bool) :
    prepare (data A C K j parameters z v reserve w S,bits)=
      CompanionRepeatedReturnProgram.data A C K j
        (CountingPhaseParametersProgram.precision parameters)
        (CountingPhaseParametersProgram.scalar (.input 5) parameters)
        (CountingPhaseParametersProgram.scalar (.input 3) parameters)
        (TreeFraction.val (CountingPhaseParametersProgram.noise parameters)) z v
        (degree A C K j parameters z v reserve) (depth A C K j parameters z v reserve) w S bits := by
  unfold prepare
  rw [fixed_data]
  rfl

theorem width_data (A : Instance (Fin m) (Fin n)) (C K j : ℕ)
    (parameters : CountingPhaseParametersProgram.Input) (z : View A → ℕ)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) (reserve : List Bool)
    (w : LabelIndex A → LabelIndex A → TreeFraction.Fraction) (S : Set (Labels A×Bool)) :
    width (data A C K j parameters z v reserve w S)=
      CountingPhaseParametersProgram.scalar (.input 3) parameters*
        ((CountingPhaseParametersProgram.scalar (.input 5) parameters+1)*
          CompanionBooleanPhase.stepBits A C K j (CountingPhaseParametersProgram.precision parameters)
            (TreeFraction.val (CountingPhaseParametersProgram.noise parameters))) := by
  unfold width
  rw [fixed_data,CompanionRepeatedReturnProgram.blockWidth_data]
  rfl

theorem output_sameLaw (A : Instance (Fin m) (Fin n)) (C K j : ℕ)
    (hC : 0 < C) (hj : j ≤ rationalHeight A C) (hK : 1 ≤ K)
    (hW : 100*A.d*K ≤ A.W) (hB : (K:ℝ)=CompanionOracleDensity.binWidth A C)
    (parameters : CountingPhaseParametersProgram.Input)
    (hxi : 0 < TreeFraction.val (CountingPhaseParametersProgram.noise parameters))
    (z : View A → ℕ) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (reserve : List Bool)
    (hdegree : RootedOracleConfigProgram.rootDegree (oracleData A C K j parameters z v reserve) ≤ reserve.length)
    (hdepth : RootedOracleConfigProgram.depth (oracleData A C K j parameters z v reserve) ≤ reserve.length)
    (w : LabelIndex A → LabelIndex A → TreeFraction.Fraction)
    (S : PlainIndex (pairs : List (CompanionRationalUpdates.Pair A))) :
    let k := CountingPhaseParametersProgram.precision parameters
    let cap := CountingPhaseParametersProgram.scalar (.input 5) parameters
    let t := CountingPhaseParametersProgram.scalar (.input 3) parameters
    let xi := TreeFraction.val (CountingPhaseParametersProgram.noise parameters)
    SameLaw (fun bits : Fin (t*((cap+1)*CompanionBooleanPhase.stepBits A C K j k xi)) → Bool =>
      output (data A C K j parameters z v reserve w S.val.val,List.ofFn bits))
      (fun bits => encodeSet (coordinateOrder A)
        (RootedReturnWords.booleanReturns A (RootedCompletion.rowColumn A.T) C K j k cap t hK hW xi
          (RootedCatalogGrid.gridEquiv A K v) (CompanionEvaluatedWeightProgram.sourceWeights A w) S bits).val.val) := by
  dsimp only
  have hd : (degree A C K j parameters z v reserve).length=
      PowerOfTwoApproximation.rootDegree (roundingTolerance (innerTolerance
        (TreeFraction.val (CountingPhaseParametersProgram.noise parameters)/2) j)) := by
    rw [degree,List.length_take,List.length_replicate,min_eq_left hdegree]
    exact RootedOracleConfigProgram.rootDegree_data A C K j _ z v _
  have ht : (depth A C K j parameters z v reserve).length=
      PowerOfTwoApproximation.depth (roundingTolerance (innerTolerance
        (TreeFraction.val (CountingPhaseParametersProgram.noise parameters)/2) j)) := by
    rw [depth,List.length_take,List.length_replicate,min_eq_left hdepth]
    exact RootedOracleConfigProgram.depth_data A C K j _ z v _
  have h := CompanionRepeatedReturnProgram.output_sameLaw A C K j
    (CountingPhaseParametersProgram.precision parameters)
    (CountingPhaseParametersProgram.scalar (.input 5) parameters)
    (CountingPhaseParametersProgram.scalar (.input 3) parameters)
    hC hj hK hW hB (TreeFraction.val (CountingPhaseParametersProgram.noise parameters)) hxi
    z v (degree A C K j parameters z v reserve) (depth A C K j parameters z v reserve) hd ht w S
  intro phi
  have he : (fun bits : Fin ((CountingPhaseParametersProgram.scalar (.input 3) parameters)*
      ((CountingPhaseParametersProgram.scalar (.input 5) parameters+1)*
        CompanionBooleanPhase.stepBits A C K j (CountingPhaseParametersProgram.precision parameters)
          (TreeFraction.val (CountingPhaseParametersProgram.noise parameters)))) → Bool => output (data A C K j parameters z v reserve w S.val.val,List.ofFn bits))=
      (fun bits => CompanionRepeatedReturnProgram.output (CompanionRepeatedReturnProgram.data A C K j
        (CountingPhaseParametersProgram.precision parameters)
        (CountingPhaseParametersProgram.scalar (.input 5) parameters)
        (CountingPhaseParametersProgram.scalar (.input 3) parameters)
        (TreeFraction.val (CountingPhaseParametersProgram.noise parameters)) z v
        (degree A C K j parameters z v reserve) (depth A C K j parameters z v reserve) w S.val.val
        (List.ofFn bits))) := by
    funext bits
    unfold output
    rw [prepare_data]
  rw [he]
  exact h phi

end
end ContingencyTables.CompanionRestartStageProgram

end OAI
