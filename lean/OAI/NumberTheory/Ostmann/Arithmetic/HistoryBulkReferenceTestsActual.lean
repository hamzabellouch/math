import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkReferenceScalarLeft
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkReferenceScalarRight
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkReferenceTestsSourceRight
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkSupportConverseGeneralActual

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkReferenceTestsActual
open Construction Conclusion Construction.CanonicalOccurrenceTransport
open HistoryPairBulkTransport HistoryBulkSupportConverse HistoryPairSmoothXi
open HistoryBulkReferenceTests HistoryBulkReferenceScalar HistoryBulkReferenceScalarCoordinates

theorem paired_referenceTests_of_inserted_nonzero
    (sources : SourceFamily) (m k : ℕ) (V : ℕ→ℕ) (l : ℕ)
  (s t : ℤ) (gp gm gp' gm' : ℕ)
  (x₀ x : SourceAssignment sources (Template.current (Template.initial m k) l))
  (π : Equiv.Perm (Fin (Template.current (Template.initial m k) l).length))
  (hπ : ∀i, sources ((Template.current (Template.initial m k) l).get (π i)).origin =
    sources ((Template.current (Template.initial m k) l).get i).origin)
  (c e : HistoryChoices sources (Template.initial m k) V l) {outside : List ℕ}
    (hs : ((assignedHistory sources (Template.initial m k) V l s gp gm x₀ c)).Supported V outside) (ks : ((assignedHistory sources (Template.initial m k) V l t gp gm (sourceAssignmentPermutation sources (Template.current (Template.initial m k) l) π hπ x₀) e)).Supported V outside)
  (hfixed : ∀i : Fin ((Template.current (Template.initial m k) l)).length, (((Template.current (Template.initial m k) l)).get i).role≠.bulk → (x i).val=(x₀ i).val)
  (b sw : ℕ) (X tb td G : ℝ)
    (hB : orderedSourceIndicatorB sources m k (assignedHistory sources (Template.initial m k) V l s gp gm x₀ c) (assignedHistory sources (Template.initial m k) V l t gp gm (sourceAssignmentPermutation sources (Template.current (Template.initial m k) l) π hπ x₀) e) hs ks
      (root_matches (assignedLabels sources (Template.initial m k) V l s gp gm x₀ c)) x gp' gm'≠0)
    (hXi : pairedRealXi b sw X tb td G (assignedHistory sources (Template.initial m k) V l s gp gm x₀ c) (assignedHistory sources (Template.initial m k) V l t gp gm (sourceAssignmentPermutation sources (Template.current (Template.initial m k) l) π hπ x₀) e) hs ks
      (insertOrderedGiants m k (assignedHistory sources (Template.initial m k) V l s gp gm x₀ c) (assignedHistory sources (Template.initial m k) V l t gp gm (sourceAssignmentPermutation sources (Template.current (Template.initial m k) l) π hπ x₀) e) hs
        (root_matches (assignedLabels sources (Template.initial m k) V l s gp gm x₀ c))
        (orderedSourceValues sources m k l x)
        (fun a => if a then (gm':ℝ) else (gp':ℝ)))≠0) :
    ReferenceTests b sw X tb td G sources (Template.initial m k) V outside l
      (assignedRoot sources (Template.current (Template.initial m k) l) s gp gm x₀) (assignedRoot sources (Template.current (Template.initial m k) l) s gp' gm' x) c
      (assignedRoot_matches sources (Template.current (Template.initial m k) l) s gp gm x₀)
      (assignedRoot_matches sources (Template.current (Template.initial m k) l) s gp' gm' x) hs ∧
    ReferenceTests b sw X tb td G sources (Template.initial m k) V outside l
      (assignedRoot sources (Template.current (Template.initial m k) l) t gp gm (sourceAssignmentPermutation sources (Template.current (Template.initial m k) l) π hπ x₀)) (assignedRoot sources (Template.current (Template.initial m k) l) t gp' gm' (sourceAssignmentPermutation sources (Template.current (Template.initial m k) l) π hπ x)) e
      (assignedRoot_matches sources (Template.current (Template.initial m k) l) t gp gm (sourceAssignmentPermutation sources (Template.current (Template.initial m k) l) π hπ x₀))
      (assignedRoot_matches sources (Template.current (Template.initial m k) l) t gp' gm' (sourceAssignmentPermutation sources (Template.current (Template.initial m k) l) π hπ x)) ks := by
  have hL := source_left_lines_squares_of_B sources m k V l s gp gm gp' gm'
    x₀ x c (assignedHistory sources (Template.initial m k) V l t gp gm (sourceAssignmentPermutation sources (Template.current (Template.initial m k) l) π hπ x₀) e) hs hfixed gp' gm' ks hB
  have hR := source_right_lines_squares_of_B sources m k V l s t gp gm gp' gm'
    x₀ x π hπ c e hs hfixed gp' gm' ks hB
  refine ⟨⟨fun i => (hL i).1, fun i => (hL i).2, ?_⟩,
    ⟨fun i => (hR i).1, fun i => (hR i).2, ?_⟩⟩
  · apply inserted_pairedRealXi_left_scalar_ne_zero sources m k V l s gp gm gp' gm'
      x₀ x c (assignedHistory sources (Template.initial m k) V l t gp gm (sourceAssignmentPermutation sources (Template.current (Template.initial m k) l) π hπ x₀) e) hs ks hfixed gp' gm' b sw X tb td G
    simpa only [Int.cast_natCast] using hXi
  · apply inserted_pairedRealXi_right_scalar_ne_zero sources m k V l s t gp gm gp' gm'
      x₀ x π hπ c e hs ks hfixed gp' gm' b sw X tb td G
    simpa only [Int.cast_natCast] using hXi

end Ostmann.Arithmetic.HistoryBulkReferenceTestsActual

end

end OAI
