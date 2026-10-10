import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkIndependentReferenceTransportIntegerCoordinates
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkReferenceScalarLeft
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkReferenceTestsSourceRight
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkSupportConverseGeneralActual

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkIndependentReferenceTerm
open Construction Conclusion Construction.CanonicalOccurrenceTransport
open HistoryPairBulkTransport HistoryBulkSupportConverse HistoryPairSmoothXi
open HistoryBulkReferenceTests HistoryBulkReferenceScalar HistoryBulkReferenceScalarCoordinates

theorem paired_referenceTests_of_inserted_nonzero
    (sources : SourceFamily) (m k : ℕ) (V : ℕ→ℕ) (l : ℕ)
  (s t : ℤ) (gp gm gp' gm' : ℕ)
  (x₀ y₀ x y : SourceAssignment sources (Template.current (Template.initial m k) l))
  (π : Equiv.Perm (Fin (Template.current (Template.initial m k) l).length))
  (hold : ∀i, (y₀ i).val=(x₀ (π i)).val)
  (hnew : ∀i, (y i).val=(x (π i)).val)
  (c e : HistoryChoices sources (Template.initial m k) V l) {outside : List ℕ}
    (hs : ((assignedHistory sources (Template.initial m k) V l s gp gm x₀ c)).Supported V outside) (ks : ((assignedHistory sources (Template.initial m k) V l t gp gm y₀ e)).Supported V outside)
  (hfixed : ∀i : Fin ((Template.current (Template.initial m k) l)).length, (((Template.current (Template.initial m k) l)).get i).role≠.bulk → (x i).val=(x₀ i).val)
  (b sw : ℕ) (X tb td G : ℝ)
    (hB : orderedSourceIndicatorB sources m k (assignedHistory sources (Template.initial m k) V l s gp gm x₀ c) (assignedHistory sources (Template.initial m k) V l t gp gm y₀ e) hs ks
      (root_matches (assignedLabels sources (Template.initial m k) V l s gp gm x₀ c)) x gp' gm'≠0)
    (hXi : pairedRealXi b sw X tb td G (assignedHistory sources (Template.initial m k) V l s gp gm x₀ c) (assignedHistory sources (Template.initial m k) V l t gp gm y₀ e) hs ks
      (insertOrderedGiants m k (assignedHistory sources (Template.initial m k) V l s gp gm x₀ c) (assignedHistory sources (Template.initial m k) V l t gp gm y₀ e) hs
        (root_matches (assignedLabels sources (Template.initial m k) V l s gp gm x₀ c))
        (orderedSourceValues sources m k l x)
        (fun a => if a then (gm':ℝ) else (gp':ℝ)))≠0) :
    ReferenceTests b sw X tb td G sources (Template.initial m k) V outside l
      (assignedRoot sources (Template.current (Template.initial m k) l) s gp gm x₀) (assignedRoot sources (Template.current (Template.initial m k) l) s gp' gm' x) c
      (assignedRoot_matches sources (Template.current (Template.initial m k) l) s gp gm x₀)
      (assignedRoot_matches sources (Template.current (Template.initial m k) l) s gp' gm' x) hs ∧
    ReferenceTests b sw X tb td G sources (Template.initial m k) V outside l
      (assignedRoot sources (Template.current (Template.initial m k) l) t gp gm y₀) (assignedRoot sources (Template.current (Template.initial m k) l) t gp' gm' y) e
      (assignedRoot_matches sources (Template.current (Template.initial m k) l) t gp gm y₀)
      (assignedRoot_matches sources (Template.current (Template.initial m k) l) t gp' gm' y) ks := by
  have hL := source_left_lines_squares_of_B sources m k V l s gp gm gp' gm'
    x₀ x c (assignedHistory sources (Template.initial m k) V l t gp gm y₀ e) hs hfixed gp' gm' ks hB
  have hR := right_reference_lines_squares_of_B sources (Template.initial m k) V outside l
    (assignedRoot sources (Template.current (Template.initial m k) l) t gp gm y₀)
    (assignedRoot sources (Template.current (Template.initial m k) l) t gp' gm' y) e
    (assignedRoot_matches sources _ t gp gm y₀)
    (assignedRoot_matches sources _ t gp' gm' y) ks
    (assignedHistory sources (Template.initial m k) V l s gp gm x₀ c) hs _ gp' gm'
    (HistoryBulkIndependentReferenceTransport.integerInsertOrderedGiants_right_projection
      sources m k V l s t gp gm gp' gm' x₀ y₀ x y π hold hnew c e hs hfixed gp' gm') hB
  refine ⟨⟨fun i => (hL i).1, fun i => (hL i).2, ?_⟩,
    ⟨fun i => (hR i).1, fun i => (hR i).2, ?_⟩⟩
  · apply inserted_pairedRealXi_left_scalar_ne_zero sources m k V l s gp gm gp' gm'
      x₀ x c (assignedHistory sources (Template.initial m k) V l t gp gm y₀ e) hs ks hfixed gp' gm' b sw X tb td G
    simpa only [Int.cast_natCast] using hXi
  · have hh := (pairedRealXi_ne_zero_scalars b sw X tb td G _ _ hs ks _ hXi).2
    have hr := HistoryBulkIndependentReferenceTransport.insertOrderedGiants_right_projection
      sources m k V l s t gp gm gp' gm' x₀ y₀ x y π hold hnew c e hs hfixed gp' gm'
    simp only [Int.cast_natCast] at hr
    simp only [hr] at hh
    simpa only [assignedHistory,assignedRoot] using hh

end Ostmann.Arithmetic.HistoryBulkIndependentReferenceTerm

end

end OAI
