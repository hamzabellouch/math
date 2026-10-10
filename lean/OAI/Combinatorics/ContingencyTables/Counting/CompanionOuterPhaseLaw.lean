import OAI.Combinatorics.ContingencyTables.Counting.CompanionRestartContinuation

namespace OAI

/-! # Law of an executed outer phase, including its initialized restart -/
namespace ContingencyTables.CompanionOuterPhaseProgram
open MatchingFPRAS CommonBasesFPRAS FirstSuccess FairBits CompanionFactorialApplication
open CompanionComputedInitial CompanionComputedProposal CompanionArithmeticProposal
open CompanionEvaluatedWeightProgram CompanionMultiplierMatrixProgram CompanionOracleDensity
open GridBoundary FiniteObservableTransport TwoLiftStates
open scoped Classical
noncomputable section
variable {m n : ℕ}

def tailWidth (A : Instance (Fin m) (Fin n)) (C K H T N R L j : ℕ)
    (epsilon : TreeFraction.Fraction) (z : View A→ℕ)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) (reserve : List Bool) (padding : ℕ) : ℕ :=
  let p := CompanionInitializedRestartProgram.parameters A H T N R L epsilon
  let xi := TreeFraction.val (CountingPhaseParametersProgram.noise p)
  let k := CountingPhaseParametersProgram.precision p
  let obs := CountingPhaseParametersProgram.observations p
  obs*CompanionBooleanPhase.stepBits A C K j k xi+
    ((obs+1)*CompanionObservationQueriesProgram.blockWidth
      (configs A C K H T N R L j epsilon z v reserve)+padding)

def phaseWordWidth (A : Instance (Fin m) (Fin n)) (C K H T N R L j : ℕ)
    (epsilon : TreeFraction.Fraction) (z : View A→ℕ)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) (reserve : List Bool) (padding : ℕ) : ℕ :=
  wordLength A (CompanionInitialDraw.precision A (CountingPhaseSchedule.initialPrecision H))+
    (CompanionRestartProgram.sumBits A C K j
      (CompanionInitializedRestartProgram.parameters A H T N R L epsilon)+
      tailWidth A C K H T N R L j epsilon z v reserve padding)

attribute [local irreducible] CompanionInitializedRestartProgram.output
  CompanionInitializedRestartProgram.model CompanionInitializedRestartProgram.jointModel
  CompanionPhaseContinuation.run CompanionOuterPhaseProgram.output

theorem output_sameLaw (A : Instance (Fin m) (Fin n)) (C K H T N R L j padding : ℕ)
    (hC : 0<C) (hj : j+1 ≤ rationalHeight A C) (hK : 1≤K)
    (hW : 100*A.d*K ≤ A.W) (hB : (K:ℝ)=binWidth A C)
    (epsilon : TreeFraction.Fraction)
    (hxi : 0<TreeFraction.val (CountingPhaseParametersProgram.noise
      (CompanionInitializedRestartProgram.parameters A H T N R L epsilon)))
    (z : View A→ℕ) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (reserve : List Bool)
    (hlen : reserve.length=phaseWordWidth A C K H T N R L j epsilon z v reserve padding)
    (hdegree : ∀ i,i ≤ j+1 → PowerOfTwoApproximation.rootDegree
      (roundingTolerance (innerTolerance (TreeFraction.val (CountingPhaseParametersProgram.noise
        (CompanionInitializedRestartProgram.parameters A H T N R L epsilon))/2) i)) ≤ reserve.length)
    (hdepth : ∀ i,i ≤ j+1 → PowerOfTwoApproximation.depth
      (roundingTolerance (innerTolerance (TreeFraction.val (CountingPhaseParametersProgram.noise
        (CompanionInitializedRestartProgram.parameters A H T N R L epsilon))/2) i)) ≤ reserve.length)
    (old : CompanionPhaseWords.Stored A)
    (w : ℕ→LabelIndex A→LabelIndex A→TreeFraction.Fraction)
    (E : ℕ→TreeFraction.Fraction)
    (hw : ∀ a b,TreeFraction.val (w j a b)=old.multiplier (pair (pairLabels A a)) (pair (pairLabels A b)))
    (hE : TreeFraction.val (E j)=old.estimate) :
    let p := CompanionInitializedRestartProgram.parameters A H T N R L epsilon
    let xi := TreeFraction.val (CountingPhaseParametersProgram.noise p)
    let k := CountingPhaseParametersProgram.precision p
    let obs := CountingPhaseParametersProgram.observations p
    SameLaw (fun bits : Fin (phaseWordWidth A C K H T N R L j epsilon z v reserve padding)→Bool =>
      CompanionPhaseFinishProgram.view (p := (CanonicalInitialEncoding.copyOrder (capacities A)).length)
        (output (data A C K H T N R L j epsilon z v w E (List.ofFn bits))))
      (fun bits : (Fin (CompanionInitialDraw.initialBits A
          (CompanionInitialDraw.precision A (CountingPhaseSchedule.initialPrecision H))+
          CompanionRestartProgram.sumBits A C K j p)→Bool)×RootedPhaseTrial.TrialWords A C K j k obs xi =>
        CompanionPhaseFinishProgram.storedView A (pairLabels A)
          ((RootedPhaseTrial.trial A (RootedCompletion.rowColumn A.T) C K j k obs hK hW xi
            (RootedCatalogGrid.gridEquiv A K v) old
            (CompanionInitializedRestartProgram.model A C K H T N R L j epsilon hK hW v w bits.1).val
            bits.2).getD old)) := by
  dsimp only
  let p := CompanionInitializedRestartProgram.parameters A H T N R L epsilon
  let xi := TreeFraction.val (CountingPhaseParametersProgram.noise p)
  let k := CountingPhaseParametersProgram.precision p
  let obs := CountingPhaseParametersProgram.observations p
  let a := wordLength A (CompanionInitialDraw.precision A (CountingPhaseSchedule.initialPrecision H))
  let b := CompanionRestartProgram.sumBits A C K j p
  let tail := tailWidth A C K H T N R L j epsilon z v reserve padding
  let cs := configs A C K H T N R L j epsilon z v reserve
  let project := CompanionPhaseFinishProgram.view (p := (CanonicalInitialEncoding.copyOrder (capacities A)).length)
  have hd (i : ℕ) (hi : i ≤ j+1) :
      (CompanionRestartStageProgram.degree A C K i p z v reserve).length=
        PowerOfTwoApproximation.rootDegree (roundingTolerance (innerTolerance (xi/2) i)) := by
    unfold CompanionRestartStageProgram.degree CompanionRestartStageProgram.oracleData
    rw [List.length_take,List.length_replicate,RootedOracleConfigProgram.rootDegree_data,
      min_eq_left (hdegree i hi)]
  have ht (i : ℕ) (hi : i ≤ j+1) :
      (CompanionRestartStageProgram.depth A C K i p z v reserve).length=
        PowerOfTwoApproximation.depth (roundingTolerance (innerTolerance (xi/2) i)) := by
    unfold CompanionRestartStageProgram.depth CompanionRestartStageProgram.oracleData
    rw [List.length_take,List.length_replicate,RootedOracleConfigProgram.depth_data,
      min_eq_left (hdepth i hi)]
  have hi := CompanionInitializedRestartProgram.output_joint_sameLaw A C K H T N R L j tail
    hC (by omega) hK hW hB epsilon hxi z v w (fun i => E (i.val+1))
    (fun i => by
      unfold CompanionRestartStageProgram.oracleData
      rw [RootedOracleConfigProgram.rootDegree_data]
      exact (hdegree (i.val+1) (by omega)).trans_eq hlen)
    (fun i => by
      unfold CompanionRestartStageProgram.oracleData
      rw [RootedOracleConfigProgram.depth_data]
      exact (hdepth (i.val+1) (by omega)).trans_eq hlen)
  have hi' := fun phi => (hi phi).trans
    ((CompanionInitializedRestartProgram.jointModel_sameLaw A C K H T N R L j tail
      epsilon hK hW v w) phi)
  let F := fun code (bits : Fin tail→Bool) =>
    project (CompanionPhaseContinuation.run cs (matrixCode (w j),E j) k obs code (List.ofFn bits))
  let G := fun (S : PlainIndex (pairs : List (CompanionRationalUpdates.Pair A)))
      (bits : RootedPhaseTrial.TrialWords A C K j k obs xi) =>
    CompanionPhaseFinishProgram.storedView A (pairLabels A)
      ((RootedPhaseTrial.trial A (RootedCompletion.rowColumn A.T) C K j k obs hK hW xi
        (RootedCatalogGrid.gridEquiv A K v) old S.val bits).getD old)
  have hs (S : PlainIndex (pairs : List (CompanionRationalUpdates.Pair A))) :
      SameLaw (F (encodeSet (coordinateOrder A) S.val.val)) (G S) :=
    CompanionPhaseContinuation.run_sameLaw padding A C K j k obs hC hj hK hW hB xi hxi z v
      (CompanionRestartStageProgram.degree A C K j p z v reserve)
      (CompanionRestartStageProgram.depth A C K j p z v reserve)
      (CompanionRestartStageProgram.degree A C K (j+1) p z v reserve)
      (CompanionRestartStageProgram.depth A C K (j+1) p z v reserve)
      (hd j (by omega)) (ht j (by omega)) (hd (j+1) le_rfl) (ht (j+1) le_rfl)
      old (w j) (E j) hw hE S.val
  have hh := joint_encoded_bind _
    (CompanionInitializedRestartProgram.model A C K H T N R L j epsilon hK hW v w)
    (fun S => encodeSet (coordinateOrder A) S.val.val) F G hi' hs
  intro phi
  have he (bits : Fin (a+(b+tail))→Bool) :
      project (output (data A C K H T N R L j epsilon z v w E (List.ofFn bits)))=
      F (CompanionInitializedRestartProgram.output
        (CompanionInitializedRestartProgram.data A C K H T N R L j epsilon z v w
          (fun i => E (i.val+1)) (List.ofFn bits)))
        (splitWordEquiv b tail (splitWordEquiv a (b+tail) bits).2).2 := by
    dsimp only [F]
    rw [output_data_run A C K H T N R L j epsilon z v w E reserve (List.ofFn bits)
      (by rw [List.length_ofFn]; exact hlen.symm)]
    congr 2
    rw [←List.drop_drop,DensePrograms.ofFn_split_drop,DensePrograms.ofFn_split_drop]
  change uniformAverage (fun bits : Fin (a+(b+tail))→Bool =>
    phi (project (output (data A C K H T N R L j epsilon z v w E (List.ofFn bits)))))=_
  simp_rw [he]
  exact hh phi

end
end ContingencyTables.CompanionOuterPhaseProgram

end OAI
