import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkReferenceScalarBasic
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkReferenceScalarCoordinatesRight

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkReferenceScalar
open Construction Conclusion Construction.CanonicalOccurrenceTransport HistoryOccurrenceVariables
open HistoryPairPattern HistoryPairSmoothXi HistorySymbolicEncoding HistoryPairBulkTransport
open HistoryBulkReferenceScalarCoordinates HistoryBulkSupportConversePlan

theorem inserted_pairedRealXi_right_scalar_ne_zero
    (sources : SourceFamily) (m k : ℕ) (V : ℕ → ℕ) (l : ℕ) (s t : ℤ)
    (gp gm gp' gm' : ℕ)
    (x₀ x : SourceAssignment sources (Template.current (Template.initial m k) l))
    (π : Equiv.Perm (Fin (Template.current (Template.initial m k) l).length))
    (hπ : ∀ i, sources ((Template.current (Template.initial m k) l).get (π i)).origin =
      sources ((Template.current (Template.initial m k) l).get i).origin)
    (c d : HistoryChoices sources (Template.initial m k) V l)
    {outside : List ℕ}
    (hs : (assignedHistory sources (Template.initial m k) V l s gp gm x₀ c).Supported V outside)
    (gs : (assignedHistory sources (Template.initial m k) V l t gp gm
      (sourceAssignmentPermutation sources (Template.current (Template.initial m k) l) π hπ x₀) d).Supported V outside)
    (hfixed : ∀ i : Fin (Template.current (Template.initial m k) l).length,
      ((Template.current (Template.initial m k) l).get i).role ≠ .bulk → (x i).val = (x₀ i).val)
    (Xp Xm : ℤ) (b sw : ℕ) (X tb td G : ℝ)
    (hx : pairedRealXi b sw X tb td G
      (assignedHistory sources (Template.initial m k) V l s gp gm x₀ c) (assignedHistory sources (Template.initial m k) V l t gp gm (sourceAssignmentPermutation sources (Template.current (Template.initial m k) l) π hπ x₀) d) hs gs
      (insertOrderedGiants m k (assignedHistory sources (Template.initial m k) V l s gp gm x₀ c) (assignedHistory sources (Template.initial m k) V l t gp gm (sourceAssignmentPermutation sources (Template.current (Template.initial m k) l) π hπ x₀) d) hs
        (root_matches (assignedLabels sources (Template.initial m k) V l s gp gm x₀ c))
        (orderedSourceValues sources m k l x) (fun t => if t then (Xm:ℝ) else (Xp:ℝ))) ≠ 0) :
    actualRealHistoryScalar b sw X tb td G outside
      (assignedHistory sources (Template.initial m k) V l t gp gm
        (sourceAssignmentPermutation sources (Template.current (Template.initial m k) l) π hπ x₀) d) gs
      (fun q => (newSourceSample sources (Template.initial m k) V l
        (assignedRoot sources (Template.current (Template.initial m k) l) t gp' gm' (sourceAssignmentPermutation sources (Template.current (Template.initial m k) l) π hπ x)) d
        (assignedRoot_matches sources (Template.current (Template.initial m k) l) t gp' gm' (sourceAssignmentPermutation sources (Template.current (Template.initial m k) l) π hπ x)) Xp Xm
        ((decodedCoordinateEquiv sources (Template.initial m k) V l
          (assignedRoot sources (Template.current (Template.initial m k) l) t gp gm (sourceAssignmentPermutation sources (Template.current (Template.initial m k) l) π hπ x₀)) d
          (assignedRoot_matches sources (Template.current (Template.initial m k) l) t gp gm (sourceAssignmentPermutation sources (Template.current (Template.initial m k) l) π hπ x₀))).symm q):ℝ)) ≠ 0 := by
  have hh := (pairedRealXi_ne_zero_scalars b sw X tb td G _ _ hs gs _ hx).2
  simpa only [insertOrderedGiants_right_projection sources m k V l s t gp gm gp' gm' x₀ x π hπ c d
    hs hfixed Xp Xm] using hh

end Ostmann.Arithmetic.HistoryBulkReferenceScalar

end

end OAI
