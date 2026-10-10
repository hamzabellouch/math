import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkReferenceTestsActualSupport
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkReferenceTestsFrequencySource

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkReferenceTestsActual
open Construction Conclusion Construction.CanonicalOccurrenceTransport
open HistoryPairBulkTransport HistoryBulkSupportConverse HistoryPairSmoothXi
open HistoryBulkReferenceTests HistoryBulkReferenceScalarCoordinates HistorySignedSpectatorCRT
open HistoryBulkReferenceTestsFrequency HistoryBulkResidueNormSum HistoryBulkSpectatorReferenceRaw
open HistoryFrequencyResidues

theorem inserted_pair_supported_of_actual_finite_tests
    {d : Decomposition} {Bs BD Bz L : ℝ} {k : ℕ} {E : Finset ℕ}
    (C : InitialSourceChoice d Bs BD Bz k L E) {spectator : PrimeSource}
    (V : ℕ→ℕ) (outside : List ℕ) (l K : ℕ)
    (σ : Equiv.Perm (Fin (2^l)×Fin (2*(bulkSize k L/2))))
    (x₀ x : SourceAssignment C.sources (Template.current (Template.initial (2*(bulkSize k L/2)) k) l)) (s t : ℤ)
    (gp gm gp' gm' : ℕ) (c e : HistoryChoices C.sources (Template.initial (2*(bulkSize k L/2)) k) V l)
    (hs : ((assignedHistory C.sources (Template.initial (2*(bulkSize k L/2)) k) V l s gp gm x₀ c)).Supported V outside) (ks : ((assignedHistory C.sources (Template.initial (2*(bulkSize k L/2)) k) V l t gp gm ((leafBulkAssignmentPermutation (bulkSize k L/2) k l C.bulk (C.cells.topSource E C.deleted_card) (C.cells.compSource E C.deleted_card) σ) x₀) e)).Supported V outside)
    (b sw : ℕ) (X tb td G : ℝ)
    (hsep : C.CrossRoleSeparation spectator) (hle : l≤K)
    (hfixed : ∀i : Fin ((Template.current (Template.initial (2*(bulkSize k L/2)) k) l)).length, (((Template.current (Template.initial (2*(bulkSize k L/2)) k) l)).get i).role≠.bulk → (x i).val=(x₀ i).val)
    (hx : (assignmentPrior C.sources (Template.current (Template.initial (2*(bulkSize k L/2)) k) l)).mass x≠0)
    (hc : choicesMass C.sources (Template.initial (2*(bulkSize k L/2)) k) V l c≠0) (he : choicesMass C.sources (Template.initial (2*(bulkSize k L/2)) k) V l e≠0)
    (hfreq : ∀j≤l,∀origin,(C.sources origin).AboveFrequency (V j))
    (hp : 0<gp') (hm : 0<gm')
    (hroot : (assignedRoot C.sources (Template.current (Template.initial (2*(bulkSize k L/2)) k) l) s gp' gm' x).Coprime outside)
    (hroot' : (assignedRoot C.sources (Template.current (Template.initial (2*(bulkSize k L/2)) k) l) t gp' gm' ((leafBulkAssignmentPermutation (bulkSize k L/2) k l C.bulk (C.cells.topSource E C.deleted_card) (C.cells.compSource E C.deleted_card) σ) x)).Coprime outside)
    (hB : orderedSourceIndicatorB C.sources (2*(bulkSize k L/2)) k (assignedHistory C.sources (Template.initial (2*(bulkSize k L/2)) k) V l s gp gm x₀ c) (assignedHistory C.sources (Template.initial (2*(bulkSize k L/2)) k) V l t gp gm ((leafBulkAssignmentPermutation (bulkSize k L/2) k l C.bulk (C.cells.topSource E C.deleted_card) (C.cells.compSource E C.deleted_card) σ) x₀) e) hs ks
      (root_matches (assignedLabels C.sources (Template.initial (2*(bulkSize k L/2)) k) V l s gp gm x₀ c)) x gp' gm'≠0)
    (hXi : pairedRealXi b sw X tb td G (assignedHistory C.sources (Template.initial (2*(bulkSize k L/2)) k) V l s gp gm x₀ c) (assignedHistory C.sources (Template.initial (2*(bulkSize k L/2)) k) V l t gp gm ((leafBulkAssignmentPermutation (bulkSize k L/2) k l C.bulk (C.cells.topSource E C.deleted_card) (C.cells.compSource E C.deleted_card) σ) x₀) e) hs ks
      (insertOrderedGiants (2*(bulkSize k L/2)) k (assignedHistory C.sources (Template.initial (2*(bulkSize k L/2)) k) V l s gp gm x₀ c) (assignedHistory C.sources (Template.initial (2*(bulkSize k L/2)) k) V l t gp gm ((leafBulkAssignmentPermutation (bulkSize k L/2) k l C.bulk (C.cells.topSource E C.deleted_card) (C.cells.compSource E C.deleted_card) σ) x₀) e) hs
        (root_matches (assignedLabels C.sources (Template.initial (2*(bulkSize k L/2)) k) V l s gp gm x₀ c))
        (orderedSourceValues C.sources (2*(bulkSize k L/2)) k l x)
        (fun a => if a then (gm':ℝ) else (gp':ℝ)))≠0)
    (hR : independentRTest K (assignedHistory C.sources (Template.initial (2*(bulkSize k L/2)) k) V l s gp gm x₀ c) (assignedHistory C.sources (Template.initial (2*(bulkSize k L/2)) k) V l t gp gm ((leafBulkAssignmentPermutation (bulkSize k L/2) k l C.bulk (C.cells.topSource E C.deleted_card) (C.cells.compSource E C.deleted_card) σ) x₀) e) σ (gp',gm')
      (sourceBulkUnits ((pairedFrequencyProduct (assignedHistory C.sources (Template.initial (2*(bulkSize k L/2)) k) V l s gp gm x₀ c) (assignedHistory C.sources (Template.initial (2*(bulkSize k L/2)) k) V l t gp gm ((leafBulkAssignmentPermutation (bulkSize k L/2) k l C.bulk (C.cells.topSource E C.deleted_card) (C.cells.compSource E C.deleted_card) σ) x₀) e))^(K+2)) C.sources (2*(bulkSize k L/2)) k l x)≠0)
    (g : (q:ℕ)→ZMod q→ℂ) (hprime : ∀q∈outside,q.Prime)
    (hg : ∀q∈outside,g q 0=0) (houtfreq : ∀q∈outside,∀j≤l,V j<q)
    (hD : residuePairSpectator g outside outside.prod (assignedHistory C.sources (Template.initial (2*(bulkSize k L/2)) k) V l s gp' gm' x c) (assignedHistory C.sources (Template.initial (2*(bulkSize k L/2)) k) V l t gp' gm' ((leafBulkAssignmentPermutation (bulkSize k L/2) k l C.bulk (C.cells.topSource E C.deleted_card) (C.cells.compSource E C.deleted_card) σ) x) e) (gp',gm')≠0) :
    ((assignedHistory C.sources (Template.initial (2*(bulkSize k L/2)) k) V l s gp' gm' x c)).Supported V outside ∧ ((assignedHistory C.sources (Template.initial (2*(bulkSize k L/2)) k) V l t gp' gm' ((leafBulkAssignmentPermutation (bulkSize k L/2) k l C.bulk (C.cells.topSource E C.deleted_card) (C.cells.compSource E C.deleted_card) σ) x) e)).Supported V outside := by
  have hreq := independentRTest_source_eq_reference_of_mass K (bulkSize k L/2) k l C.bulk
    (C.cells.topSource E C.deleted_card) (C.cells.compSource E C.deleted_card) V
    (assignedHistory C.sources (Template.initial (2*(bulkSize k L/2)) k) V l s gp gm x₀ c) (assignedHistory C.sources (Template.initial (2*(bulkSize k L/2)) k) V l t gp gm ((leafBulkAssignmentPermutation (bulkSize k L/2) k l C.bulk (C.cells.topSource E C.deleted_card) (C.cells.compSource E C.deleted_card) σ) x₀) e) (assignedRoot C.sources (Template.current (Template.initial (2*(bulkSize k L/2)) k) l) s gp' gm' x)
    (assignedRoot C.sources (Template.current (Template.initial (2*(bulkSize k L/2)) k) l) t gp' gm' ((leafBulkAssignmentPermutation (bulkSize k L/2) k l C.bulk (C.cells.topSource E C.deleted_card) (C.cells.compSource E C.deleted_card) σ) x)) c e σ x rfl rfl hs ks hx hfreq (gp',gm')
  have hreference := hreq ▸ hR
  exact inserted_pair_supported_of_actual_source_tests C V outside l K σ x₀ x s t gp gm gp' gm'
    c e hs ks b sw X tb td G hsep hle hfixed hx hc he hfreq hp hm hroot hroot'
    hB hXi hreference g hprime hg houtfreq hD

end Ostmann.Arithmetic.HistoryBulkReferenceTestsActual

end

end OAI
