import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkFixedReferenceTransportScalarBasic

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkFixedReferenceTransport
open Construction Construction.CanonicalOccurrenceTransport Conclusion
open HistoryOccurrenceVariables HistoryPairPattern HistorySymbolicEncoding HistoryPairSmoothXi
open HistoryPairBulkTransport HistoryBulkSupportConversePlan HistoryBulkReferenceScalarCoordinates

section Pair
variable (sources : SourceFamily) (m k₀ : ℕ) (V : ℕ→ℕ) (outside : List ℕ) (l : ℕ)
  (s t : ℤ) (gp gm gp' gm' : ℕ)
  (x₀ x : SourceAssignment sources (Template.current (Template.initial m k₀) l))
  (π : Equiv.Perm (Fin (Template.current (Template.initial m k₀) l).length))
  (hπ : ∀i, sources ((Template.current (Template.initial m k₀) l).get (π i)).origin =
    sources ((Template.current (Template.initial m k₀) l).get i).origin)
  (c e : HistoryChoices sources (Template.initial m k₀) V l)
local notation "T" => Template.current (Template.initial m k₀) l
local notation "H₀" => assignedHistory sources (Template.initial m k₀) V l s gp gm x₀ c
local notation "K₀" => assignedHistory sources (Template.initial m k₀) V l t gp gm
  (sourceAssignmentPermutation sources T π hπ x₀) e
local notation "H₁" => assignedHistory sources (Template.initial m k₀) V l s gp' gm' x c
local notation "K₁" => assignedHistory sources (Template.initial m k₀) V l t gp' gm'
  (sourceAssignmentPermutation sources T π hπ x) e

theorem assigned_pairedRealXi_insertOrderedGiants
    (hs : (H₀).Supported V outside) (ks : (K₀).Supported V outside)
    (hs' : (H₁).Supported V outside) (ks' : (K₁).Supported V outside)
    (hfixed : ∀i : Fin (T).length, ((T).get i).role≠.bulk → (x i).val=(x₀ i).val)
    (bc sc : ℕ) (X tb td G : ℝ) :
    pairedRealXi bc sc X tb td G H₀ K₀ hs ks
      (insertOrderedGiants m k₀ H₀ K₀ hs
        (root_matches (assignedLabels sources (Template.initial m k₀) V l s gp gm x₀ c))
        (orderedSourceValues sources m k₀ l x)
        (fun u => if u then (gm':ℝ) else (gp':ℝ))) =
    pairedRealXi bc sc X tb td G H₁ K₁ hs' ks'
      (fun i => (pairSample H₁ K₁ i:ℝ)) := by
  have hr : RootGiantsAgree H₁ K₁ := by
    simp [RootGiantsAgree,assignedHistory,decodeHistory_root,assignedRoot]
  simp only [pairedRealXi,actualRealXi,leftMap_sample,rightMap_sample H₁ K₁ hr]
  apply congrArg₂ (fun a b : ℂ => a * star b)
  · apply assigned_scalar_transport sources (Template.initial m k₀) V outside l s gp gm gp' gm'
      x₀ x c hs hs' bc sc X tb td G
    intro i
    simpa only [Int.cast_natCast] using
      insertOrderedGiants_left_coordinate sources m k₀ V l s gp gm gp' gm'
        x₀ x c K₀ hs hfixed gp' gm' i
  · apply assigned_scalar_transport sources (Template.initial m k₀) V outside l t gp gm gp' gm'
      (sourceAssignmentPermutation sources T π hπ x₀)
      (sourceAssignmentPermutation sources T π hπ x) e ks ks' bc sc X tb td G
    intro i
    simpa only [Int.cast_natCast] using
      insertOrderedGiants_right_coordinate sources m k₀ V l s t gp gm gp' gm'
        x₀ x π hπ c e hs hfixed gp' gm' i

end Pair
end Ostmann.Arithmetic.HistoryBulkFixedReferenceTransport

end

end OAI
