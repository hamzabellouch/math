import OAI.Combinatorics.ContingencyTables.Counting.CompanionCanonicalPhaseLaw
import OAI.Combinatorics.ContingencyTables.Counting.CompanionRestartSupport

namespace OAI

/-! # Representation preservation for every executed counting phase

The restart support statement is obtained from its actual finite-word law.
The remaining trajectory and observation words may be unused padding for
that law; their presence still supplies the required precision markers.
-/
namespace ContingencyTables.CompanionCanonicalPhaseSupport
open MatchingFPRAS CommonBasesFPRAS FiniteObservableTransport
open CompanionFactorialApplication CompanionComputedInitial CompanionComputedProposal
open CompanionEvaluatedWeightProgram CompanionStoredRepresentation CompanionHistoryReadback
open CompanionCanonicalPhaseLaw CompanionOracleDensity GridBoundary
open scoped Classical
noncomputable section
variable {m n : ℕ}

lemma restart_prefix_le (A : Instance (Fin m) (Fin n)) (C K H N R L W j : ℕ)
    (epsilon : TreeFraction.Fraction) (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (hj : j < H)
    (hwidth : RootedPhaseHistory.totalWidth A (rawSettings A C K H N R L epsilon hK hW v) ≤ W) :
    CompanionComputedInitial.wordLength A
        (CompanionInitialDraw.precision A (CountingPhaseSchedule.initialPrecision H))+
      CompanionRestartProgram.sumBits A C K j
        (CompanionInitializedRestartProgram.parameters A H
          (CompanionTargetMixing.restartTime A H L) N R L epsilon) ≤ W := by
  let s := rawSettings A C K H N R L epsilon hK hW v
  calc
    _ = RootedRestartWords.initialStageBits A C K H L s.k R s.h j s.xi :=
      CompanionOuterWidths.initialWidth_eq A C K H N R L j epsilon
    _ ≤ RootedPhaseHistory.width A s j := Nat.le_add_right _ _
    _ ≤ RootedPhaseHistory.totalWidth A s := RootedPhaseHistory.width_le A s j hj
    _ ≤ W := hwidth

theorem output_rep (A : Instance (Fin m) (Fin n)) (C K H N R L W : ℕ)
    (epsilon : TreeFraction.Fraction) (hC : 0 < C) (hK : 1 ≤ K)
    (hW : 100*A.d*K ≤ A.W) (hB : (K:ℝ)=binWidth A C)
    (hxi : 0 < TreeFraction.val (CountingPhaseParametersProgram.noise
      (CompanionInitializedRestartProgram.parameters A H
        (CompanionTargetMixing.restartTime A H L) N R L epsilon)))
    (z : View A→ℕ) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (initial : CompanionPhaseFinishProgram.Stored) (history : List CompanionPhaseFinishProgram.Stored)
    (hj : history.length < H) (hphase : history.length+1 ≤ rationalHeight A C)
    (hwidth : RootedPhaseHistory.totalWidth A (rawSettings A C K H N R L epsilon hK hW v) ≤ W)
    (hdegree : ∀ i,i ≤ history.length+1 → PowerOfTwoApproximation.rootDegree
      (roundingTolerance (innerTolerance
        ((rawSettings A C K H N R L epsilon hK hW v).xi/2) i)) ≤ W)
    (hdepth : ∀ i,i ≤ history.length+1 → PowerOfTwoApproximation.depth
      (roundingTolerance (innerTolerance
        ((rawSettings A C K H N R L epsilon hK hW v).xi/2) i)) ≤ W)
    (hinit : StoredRep (CanonicalInitialEncoding.copyOrder (capacities A)).length initial)
    (hh : ∀ q∈history,StoredRep (CanonicalInitialEncoding.copyOrder (capacities A)).length q)
    (bits : Fin W→Bool) :
    StoredRep (CanonicalInitialEncoding.copyOrder (capacities A)).length
      (CompanionOuterPhaseProgram.output
        (((CompanionRestartInitializer.data A C K H
          (CompanionTargetMixing.restartTime A H L) N R L epsilon z v,initial),history),List.ofFn bits)) := by
  let t := CompanionTargetMixing.restartTime A H L
  let j := history.length
  let p := CompanionInitializedRestartProgram.parameters A H t N R L epsilon
  let a := wordLength A (CompanionInitialDraw.precision A (CountingPhaseSchedule.initialPrecision H))
  let b := CompanionRestartProgram.sumBits A C K j p
  let padding := W-(a+b)
  let w := matrixAt (CanonicalInitialEncoding.copyOrder (capacities A)).length initial history
  let E := estimateAt initial history
  have hprefix : a+b ≤ W := restart_prefix_le A C K H N R L W j epsilon hK hW v hj hwidth
  have hlen : a+(b+padding)=W := by
    rw [←Nat.add_assoc]
    exact Nat.add_sub_of_le hprefix
  have hl := CompanionInitializedRestartProgram.output_padded_sameLaw A C K H t N R L j padding
    hC (by omega) hK hW hB epsilon hxi z v w (fun i => E (i.val+1))
    (fun i => by
      unfold CompanionRestartStageProgram.oracleData
      rw [RootedOracleConfigProgram.rootDegree_data]
      exact (hdegree (i.val+1) (by omega)).trans_eq hlen.symm)
    (fun i => by
      unfold CompanionRestartStageProgram.oracleData
      rw [RootedOracleConfigProgram.depth_data]
      exact (hdepth (i.val+1) (by omega)).trans_eq hlen.symm)
  have hl' := SameLaw.word_length hlen
    (fun bs => CompanionInitializedRestartProgram.output
      (CompanionInitializedRestartProgram.data A C K H t N R L j epsilon z v w
        (fun i => E (i.val+1)) bs)) _ hl
  obtain ⟨sourceBits,hs⟩ := hl'.exists_preimage bits
  have hd := outer_data_readback A C K H t N R L epsilon z v initial history hinit hh (List.ofFn bits)
  apply CompanionInitializedRestartProgram.outer_output_rep_of_supported A _ hinit hh
  refine ⟨CompanionInitializedRestartProgram.model A C K H t N R L j epsilon hK hW v w sourceBits,?_⟩
  rw [←hd]
  change CompanionInitializedRestartProgram.output
    (CompanionOuterPhaseProgram.restartInput
      (CompanionOuterPhaseProgram.data A C K H t N R L j epsilon z v w E (List.ofFn bits)))=_
  rw [CompanionOuterPhaseProgram.restartInput_data]
  exact hs.symm

end
end ContingencyTables.CompanionCanonicalPhaseSupport

end OAI
