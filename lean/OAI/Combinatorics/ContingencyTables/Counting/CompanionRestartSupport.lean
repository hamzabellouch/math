import OAI.Combinatorics.ContingencyTables.Counting.CompanionInitializedRestartLaw
import OAI.Combinatorics.ContingencyTables.Transport.FiniteSameLawSupport
import OAI.Combinatorics.ContingencyTables.Counting.CompanionStoredRepresentation

namespace OAI

/-! # Every executed restart has the canonical paired catalog

Finite uniform words have positive mass individually. The proved padded
restart law therefore gives a valid encoded source state on every word,
including words on which one of the return attempts uses its fallback.
-/
namespace ContingencyTables.CompanionInitializedRestartProgram
open MatchingFPRAS CommonBasesFPRAS FiniteObservableTransport
open CompanionFactorialApplication CompanionComputedInitial CompanionComputedProposal
open CompanionArithmeticProposal CompanionEvaluatedWeightProgram
open CompanionOracleDensity TwoLiftStates GridBoundary
open scoped Classical
noncomputable section
variable {m n : ℕ}

lemma catalog_length_encode (A : Instance (Fin m) (Fin n)) (S : Set (Labels A×Bool)) :
    (PairedCatalogProgram.catalog (encodeSet (coordinateOrder A) S)).length=
      (CanonicalInitialEncoding.copyOrder (capacities A)).length := by
  rw [encodeSet_reindex,PairedCatalogProgram.catalog_encode]
  exact List.length_ofFn

lemma catalog_length_of_supported (A : Instance (Fin m) (Fin n)) (code : List ℕ)
    (h : ∃ S : PlainIndex (pairs : List (CompanionRationalUpdates.Pair A)),
      code=encodeSet (coordinateOrder A) S.val.val) :
    (PairedCatalogProgram.catalog code).length=
      (CanonicalInitialEncoding.copyOrder (capacities A)).length := by
  obtain ⟨S,rfl⟩ := h
  exact catalog_length_encode A S.val.val

lemma outer_trial_catalog (z : CompanionOuterPhaseProgram.Input) :
    CompanionPhaseTrialProgram.catalogue (CompanionOuterPhaseProgram.trialInput z)=
      PairedCatalogProgram.catalog (CompanionOuterPhaseProgram.startCode z) := rfl

theorem outer_output_rep_of_supported (A : Instance (Fin m) (Fin n))
    (z : CompanionOuterPhaseProgram.Input)
    (hinit : CompanionStoredRepresentation.StoredRep
      (CanonicalInitialEncoding.copyOrder (capacities A)).length z.1.1.2)
    (hh : ∀ s∈z.1.2,CompanionStoredRepresentation.StoredRep
      (CanonicalInitialEncoding.copyOrder (capacities A)).length s)
    (hs : ∃ S : PlainIndex (pairs : List (CompanionRationalUpdates.Pair A)),
      CompanionOuterPhaseProgram.startCode z=encodeSet (coordinateOrder A) S.val.val) :
    CompanionStoredRepresentation.StoredRep
      (CanonicalInitialEncoding.copyOrder (capacities A)).length
      (CompanionOuterPhaseProgram.output z) := by
  apply CompanionStoredRepresentation.outer_output_rep z hinit hh
  rw [outer_trial_catalog]
  exact catalog_length_of_supported A _ hs

theorem output_padded_supported (A : Instance (Fin m) (Fin n)) (C K H T N R L j padding : ℕ)
    (hC : 0 < C) (hj : j ≤ rationalHeight A C) (hK : 1 ≤ K)
    (hW : 100*A.d*K ≤ A.W) (hB : (K:ℝ)=CompanionOracleDensity.binWidth A C)
    (epsilon : TreeFraction.Fraction)
    (hxi : 0 < TreeFraction.val (CountingPhaseParametersProgram.noise (parameters A H T N R L epsilon)))
    (z : View A → ℕ) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (w : ℕ → LabelIndex A → LabelIndex A → TreeFraction.Fraction)
    (estimates : Fin j → TreeFraction.Fraction)
    (hdegree : ∀ i : Fin j,RootedOracleConfigProgram.rootDegree
      (CompanionRestartStageProgram.oracleData A C K (i.val+1) (parameters A H T N R L epsilon) z v
        (List.replicate (wordLength A (CompanionInitialDraw.precision A (CountingPhaseSchedule.initialPrecision H))+
          (CompanionRestartProgram.sumBits A C K j (parameters A H T N R L epsilon)+padding)) false)) ≤
      wordLength A (CompanionInitialDraw.precision A (CountingPhaseSchedule.initialPrecision H))+
        (CompanionRestartProgram.sumBits A C K j (parameters A H T N R L epsilon)+padding))
    (hdepth : ∀ i : Fin j,RootedOracleConfigProgram.depth
      (CompanionRestartStageProgram.oracleData A C K (i.val+1) (parameters A H T N R L epsilon) z v
        (List.replicate (wordLength A (CompanionInitialDraw.precision A (CountingPhaseSchedule.initialPrecision H))+
          (CompanionRestartProgram.sumBits A C K j (parameters A H T N R L epsilon)+padding)) false)) ≤
      wordLength A (CompanionInitialDraw.precision A (CountingPhaseSchedule.initialPrecision H))+
        (CompanionRestartProgram.sumBits A C K j (parameters A H T N R L epsilon)+padding))
    (bits : Fin (wordLength A
      (CompanionInitialDraw.precision A (CountingPhaseSchedule.initialPrecision H))+
      (CompanionRestartProgram.sumBits A C K j (parameters A H T N R L epsilon)+padding)) → Bool) :
    ∃ S : PlainIndex (pairs : List (CompanionRationalUpdates.Pair A)),
      output (data A C K H T N R L j epsilon z v w estimates (List.ofFn bits))=
        encodeSet (coordinateOrder A) S.val.val := by
  have hl := output_padded_sameLaw A C K H T N R L j padding
    hC hj hK hW hB epsilon hxi z v w estimates hdegree hdepth
  obtain ⟨sourceBits,he⟩ := hl.exists_preimage bits
  exact ⟨model A C K H T N R L j epsilon hK hW v w sourceBits,he.symm⟩

end
end ContingencyTables.CompanionInitializedRestartProgram

end OAI
