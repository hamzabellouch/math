import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkFixedReferenceTransportScalarBasic
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkIndependentReferenceTransportCoordinates

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkIndependentReferenceTransport
open Construction Construction.CanonicalOccurrenceTransport Conclusion
open HistoryOccurrenceVariables HistoryPairPattern HistorySymbolicEncoding HistoryPairSmoothXi
open HistoryPairBulkTransport HistoryBulkSupportConversePlan HistoryBulkReferenceScalarCoordinates

section Pair
variable (sources : SourceFamily) (m k₀ : ℕ) (V : ℕ→ℕ) (outside : List ℕ) (l : ℕ)
  (s t : ℤ) (gp gm gp' gm' : ℕ)
  (x₀ y₀ x y : SourceAssignment sources (Template.current (Template.initial m k₀) l))
  (π : Equiv.Perm (Fin (Template.current (Template.initial m k₀) l).length))
  (hold : ∀i, (y₀ i).val = (x₀ (π i)).val)
  (hnew : ∀i, (y i).val = (x (π i)).val)
  (c e : HistoryChoices sources (Template.initial m k₀) V l)
include hold hnew

theorem assigned_pairedRealXi_insertOrderedGiants
    (hs : ((assignedHistory sources (Template.initial m k₀) V l s gp gm x₀ c)).Supported V outside) (ks : ((assignedHistory sources (Template.initial m k₀) V l t gp gm y₀ e)).Supported V outside)
    (hs' : ((assignedHistory sources (Template.initial m k₀) V l s gp' gm' x c)).Supported V outside) (ks' : ((assignedHistory sources (Template.initial m k₀) V l t gp' gm' y e)).Supported V outside)
    (hfixed : ∀i : Fin ((Template.current (Template.initial m k₀) l)).length, (((Template.current (Template.initial m k₀) l)).get i).role≠.bulk → (x i).val=(x₀ i).val)
    (bc sc : ℕ) (X tb td G : ℝ) :
    pairedRealXi bc sc X tb td G (assignedHistory sources (Template.initial m k₀) V l s gp gm x₀ c) (assignedHistory sources (Template.initial m k₀) V l t gp gm y₀ e) hs ks
      (insertOrderedGiants m k₀ (assignedHistory sources (Template.initial m k₀) V l s gp gm x₀ c) (assignedHistory sources (Template.initial m k₀) V l t gp gm y₀ e) hs
        (root_matches (assignedLabels sources (Template.initial m k₀) V l s gp gm x₀ c))
        (orderedSourceValues sources m k₀ l x)
        (fun u => if u then (gm':ℝ) else (gp':ℝ))) =
    pairedRealXi bc sc X tb td G (assignedHistory sources (Template.initial m k₀) V l s gp' gm' x c) (assignedHistory sources (Template.initial m k₀) V l t gp' gm' y e) hs' ks'
      (fun i => (pairSample (assignedHistory sources (Template.initial m k₀) V l s gp' gm' x c) (assignedHistory sources (Template.initial m k₀) V l t gp' gm' y e) i:ℝ)) := by
  have hr : RootGiantsAgree (assignedHistory sources (Template.initial m k₀) V l s gp' gm' x c) (assignedHistory sources (Template.initial m k₀) V l t gp' gm' y e) := by
    simp [RootGiantsAgree,assignedHistory,decodeHistory_root,assignedRoot]
  simp only [pairedRealXi,actualRealXi,leftMap_sample,rightMap_sample (assignedHistory sources (Template.initial m k₀) V l s gp' gm' x c) (assignedHistory sources (Template.initial m k₀) V l t gp' gm' y e) hr]
  apply congrArg₂ (fun a b : ℂ => a * star b)
  · apply HistoryBulkFixedReferenceTransport.assigned_scalar_transport sources (Template.initial m k₀) V outside l s gp gm gp' gm'
      x₀ x c hs hs' bc sc X tb td G
    intro i
    simpa only [Int.cast_natCast] using
      insertOrderedGiants_left_coordinate sources m k₀ V l s gp gm gp' gm'
        x₀ x c (assignedHistory sources (Template.initial m k₀) V l t gp gm y₀ e) hs hfixed gp' gm' i
  · apply HistoryBulkFixedReferenceTransport.assigned_scalar_transport sources (Template.initial m k₀) V outside l t gp gm gp' gm'
      y₀
      y e ks ks' bc sc X tb td G
    intro i
    simpa only [Int.cast_natCast] using
      insertOrderedGiants_right_coordinate sources m k₀ V l s t gp gm gp' gm'
        x₀ y₀ x y π hold hnew c e hs hfixed gp' gm' i

end Pair
end Ostmann.Arithmetic.HistoryBulkIndependentReferenceTransport

end

end OAI
