import OAI.Combinatorics.ContingencyTables.Counting.CompanionObservedUpdateProgram
import OAI.Combinatorics.ContingencyTables.Counting.CompanionObservationQueriesLaw
import OAI.Combinatorics.ContingencyTables.Counting.CompanionPhaseFinishSemantics

namespace OAI

/-! # Observable law of the physically executed phase update -/
namespace ContingencyTables.CompanionObservedUpdateProgram
open MatchingFPRAS CompanionFactorialApplication CompanionComputedInitial
open CompanionArithmeticProposal CompanionOrderedProposal CompanionMultiplierMatrixProgram
open FiniteObservableTransport CompanionComputedProposal TwoLiftStates
open scoped Classical
noncomputable section
variable {m n N : ℕ} (A : Instance (Fin m) (Fin n))

abbrev LabelIndex := CompanionEvaluatedWeightProgram.LabelIndex A

def data (cs : Configs) (states : Fin N→Set (Labels A×Bool))
    (w : LabelIndex A→LabelIndex A→TreeFraction.Fraction) (E : TreeFraction.Fraction)
    (bits : List Bool) : Input :=
  ((cs,(((orderedCatalog A (pairLabels A) (coordinateOrder A),
    (List.ofFn states).map (encodeSet (coordinateOrder A))),matrixCode w),E)),bits)

attribute [local irreducible] CompanionObservationQueriesProgram.output
  CompanionPhaseFinishProgram.output CompanionPhaseFinishProgram.rationalResult

theorem output_values (cs : Configs) (states : Fin N→Set (Labels A×Bool))
    (old : CompanionPhaseWords.Stored A)
    (w : LabelIndex A→LabelIndex A→TreeFraction.Fraction) (E : TreeFraction.Fraction)
    (hw : ∀ i j,TreeFraction.val (w i j)=old.multiplier (pair (pairLabels A i)) (pair (pairLabels A j)))
    (hE : TreeFraction.val E=old.estimate)
    (bits : Fin (N*CompanionObservationQueriesProgram.blockWidth cs)→Bool) :
    (output (data A cs states w E (List.ofFn bits))).map CompanionPhaseFinishProgram.view=
      CompanionPhaseFinishProgram.rationalResult A (pairLabels A) states old
        (CompanionObservationQueriesProgram.values (CompanionObservationQueriesProgram.output
          (cs,(List.ofFn (fun i => encodeSet (coordinateOrder A) (states i)),List.ofFn bits)))) := by
  have hq := CompanionObservationQueriesProgram.output_ofFn cs
    (fun i => encodeSet (coordinateOrder A) (states i)) bits
  have ho : output (data A cs states w E (List.ofFn bits))=
      CompanionPhaseFinishProgram.output
        ((((orderedCatalog A (pairLabels A) (coordinateOrder A),
          (List.ofFn states).map (encodeSet (coordinateOrder A))),matrixCode w),E),
          CompanionObservationQueriesProgram.output
            (cs,(List.ofFn (fun i => encodeSet (coordinateOrder A) (states i)),List.ofFn bits))) := by
    simp only [output,finishInput,queryInput,data,List.map_ofFn,Function.comp_def]
  rw [ho,hq]
  simpa only [CompanionPhaseFinishProgram.data,CompanionObservationQueriesProgram.values,List.map_ofFn,Function.comp_def] using
    (CompanionPhaseFinishProgram.output_values A (pairLabels A) (coordinateOrder A)
      states old w E (fun i => CompanionObservationQueriesProgram.queryPair
        (cs,(encodeSet (coordinateOrder A) (states i),List.ofFn
          (GridBoundary.gridWordEquiv N (CompanionObservationQueriesProgram.blockWidth cs) bits i)))) hw hE)

theorem sameLaw {U V : Type*} [Fintype U] [Fintype V]
    (cs : Configs) (states : Fin N→Set (Labels A×Bool))
    (old : CompanionPhaseWords.Stored A)
    (w : LabelIndex A→LabelIndex A→TreeFraction.Fraction) (E : TreeFraction.Fraction)
    (hw : ∀ i j,TreeFraction.val (w i j)=old.multiplier (pair (pairLabels A i)) (pair (pairLabels A j)))
    (hE : TreeFraction.val E=old.estimate) (f : Fin N→U→ℚ) (g : Fin N→V→ℚ)
    (hf : ∀ i,SameLaw (fun bits : Fin (CompanionObservationQueriesProgram.queryWidth cs.1)→Bool =>
      TreeFraction.val (RootedLabelWeightProgram.output
        (cs.1,(encodeSet (coordinateOrder A) (states i),List.ofFn bits)))) (f i))
    (hg : ∀ i,SameLaw (fun bits : Fin (CompanionObservationQueriesProgram.queryWidth cs.2)→Bool =>
      TreeFraction.val (RootedLabelWeightProgram.output
        (cs.2,(encodeSet (coordinateOrder A) (states i),List.ofFn bits)))) (g i)) :
    SameLaw (fun bits : Fin (N*CompanionObservationQueriesProgram.blockWidth cs)→Bool =>
      (output (data A cs states w E (List.ofFn bits))).map CompanionPhaseFinishProgram.view)
      (fun bits : Fin N→U×V => CompanionPhaseFinishProgram.rationalResult A (pairLabels A) states old
        (List.ofFn (fun i => (f i (bits i).1,g i (bits i).2)))) := by
  have h := (CompanionObservationQueriesProgram.sameLaw cs
    (fun i => encodeSet (coordinateOrder A) (states i)) f g hf hg).map
      (CompanionPhaseFinishProgram.rationalResult A (pairLabels A) states old)
  intro phi
  simp_rw [output_values A cs states old w E hw hE]
  exact h phi

open GridBoundary CommonBasesFPRAS CompanionWeightOracle CompanionOracleDensity

/-- The complete executed observation-and-update has the actual phase law. -/
theorem sameLaw_phase (C K j : ℕ)
    (hC : 0 < C) (hj : j+1 ≤ rationalHeight A C) (hK : 1 ≤ K)
    (hW : 100*A.d*K ≤ A.W) (hB : (K:ℝ)=binWidth A C)
    (xi : ℚ) (hxi : 0 < xi) (z : View A→ℕ)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (degree depth nextDegree nextDepth : List Bool)
    (hdegree : degree.length=PowerOfTwoApproximation.rootDegree (roundingTolerance (innerTolerance (xi/2) j)))
    (hdepth : depth.length=PowerOfTwoApproximation.depth (roundingTolerance (innerTolerance (xi/2) j)))
    (hnextDegree : nextDegree.length=PowerOfTwoApproximation.rootDegree (roundingTolerance (innerTolerance (xi/2) (j+1))))
    (hnextDepth : nextDepth.length=PowerOfTwoApproximation.depth (roundingTolerance (innerTolerance (xi/2) (j+1))))
    (states : Fin N→Set (Labels A×Bool)) (old : CompanionPhaseWords.Stored A)
    (w : LabelIndex A→LabelIndex A→TreeFraction.Fraction) (E : TreeFraction.Fraction)
    (hw : ∀ i j,TreeFraction.val (w i j)=old.multiplier (pair (pairLabels A i)) (pair (pairLabels A j)))
    (hE : TreeFraction.val E=old.estimate) :
    let cs := CompanionObservationQueriesProgram.phaseConfigs A C K j xi z v degree depth nextDegree nextDepth
    SameLaw (fun bits : Fin (N*CompanionObservationQueriesProgram.blockWidth cs)→Bool =>
      (output (data A cs states w E (List.ofFn bits))).map CompanionPhaseFinishProgram.view)
      (fun bits : Fin (CompanionPhaseWords.phaseBits A C K j N xi)→Bool =>
        (RootedPhaseWords.update A (RootedCompletion.rowColumn A.T) C K j N hK hW xi
          (RootedCatalogGrid.gridEquiv A K v) old states bits).map
            (CompanionPhaseFinishProgram.storedView A (pairLabels A))) := by
  let cs := CompanionObservationQueriesProgram.phaseConfigs A C K j xi z v degree depth nextDegree nextDepth
  let f := fun i : Fin N => RootedWeightOracle.evaluate A (RootedCompletion.rowColumn A.T)
    C K hK hW j xi (RootedCatalogGrid.gridEquiv A K v) (states i)
  let g := fun i : Fin N => RootedWeightOracle.evaluate A (RootedCompletion.rowColumn A.T)
    C K hK hW (j+1) xi (RootedCatalogGrid.gridEquiv A K v) (states i)
  have h := sameLaw A cs states old w E hw hE f g
    (fun i => CompanionObservationQueriesProgram.sameLaw_query A C K j hC (by omega)
      hK hW hB xi hxi z v degree depth hdegree hdepth (states i))
    (fun i => CompanionObservationQueriesProgram.sameLaw_query A C K (j+1) hC hj
      hK hW hB xi hxi z v nextDegree nextDepth hnextDegree hnextDepth (states i))
  dsimp only
  intro phi
  have he := uniformAverage_equiv (CompanionPhaseWords.phaseWordEquiv A C K j N xi)
    (fun xs => phi (CompanionPhaseFinishProgram.rationalResult A (pairLabels A) states old
      (List.ofFn (fun i => (f i (xs i).1,g i (xs i).2)))))
  have hr : CommonBasesFPRAS.uniformAverage
      (fun bits : Fin (CompanionPhaseWords.phaseBits A C K j N xi)→Bool =>
        phi (CompanionPhaseFinishProgram.rationalResult A (pairLabels A) states old
          (List.ofFn (fun i =>
            (f i (CompanionPhaseWords.phaseWordEquiv A C K j N xi bits i).1,
             g i (CompanionPhaseWords.phaseWordEquiv A C K j N xi bits i).2)))))=
      CommonBasesFPRAS.uniformAverage (fun bits : Fin (CompanionPhaseWords.phaseBits A C K j N xi)→Bool =>
        phi ((RootedPhaseWords.update A (RootedCompletion.rowColumn A.T) C K j N hK hW xi
          (RootedCatalogGrid.gridEquiv A K v) old states bits).map
            (CompanionPhaseFinishProgram.storedView A (pairLabels A)))) := by
    apply congrArg CommonBasesFPRAS.uniformAverage
    funext bits
    exact congrArg phi (CompanionPhaseFinishProgram.rationalResult_phase A (pairLabels A)
      (RootedCompletion.rowColumn A.T) C K j hK hW xi (RootedCatalogGrid.gridEquiv A K v) old states bits)
  exact (h phi).trans (he.symm.trans hr)

end
end ContingencyTables.CompanionObservedUpdateProgram

end OAI
