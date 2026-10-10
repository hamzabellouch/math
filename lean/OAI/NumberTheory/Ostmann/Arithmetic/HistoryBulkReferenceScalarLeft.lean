import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkReferenceScalarBasic
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkReferenceScalarCoordinatesLeft

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkReferenceScalar
open Construction Construction.CanonicalOccurrenceTransport HistoryOccurrenceVariables
open HistoryPairPattern HistoryPairSmoothXi HistorySymbolicEncoding HistoryPairBulkTransport
open HistoryBulkReferenceScalarCoordinates HistoryBulkSupportConversePlan

theorem inserted_pairedRealXi_left_scalar_ne_zero
    (sources : SourceFamily) (m k : ℕ) (V : ℕ → ℕ) (l : ℕ) (s : ℤ)
    (gp gm gp' gm' : ℕ)
    (x₀ x : SourceAssignment sources (Template.current (Template.initial m k) l))
    (c : HistoryChoices sources (Template.initial m k) V l) (g : History l)
    {outside : List ℕ}
    (hs : (assignedHistory sources (Template.initial m k) V l s gp gm x₀ c).Supported V outside)
    (gs : g.Supported V outside)
    (hfixed : ∀ i : Fin (Template.current (Template.initial m k) l).length,
      ((Template.current (Template.initial m k) l).get i).role ≠ .bulk → (x i).val = (x₀ i).val)
    (Xp Xm : ℤ) (b sw : ℕ) (X tb td G : ℝ)
    (hx : pairedRealXi b sw X tb td G
      (assignedHistory sources (Template.initial m k) V l s gp gm x₀ c) g hs gs
      (insertOrderedGiants m k _ g hs
        (root_matches (assignedLabels sources (Template.initial m k) V l s gp gm x₀ c))
        (orderedSourceValues sources m k l x) (fun t => if t then (Xm:ℝ) else (Xp:ℝ))) ≠ 0) :
    actualRealHistoryScalar b sw X tb td G outside
      (assignedHistory sources (Template.initial m k) V l s gp gm x₀ c) hs
      (fun q => (newSourceSample sources (Template.initial m k) V l
        (assignedRoot sources _ s gp' gm' x) c (assignedRoot_matches sources _ s gp' gm' x) Xp Xm
        ((decodedCoordinateEquiv sources (Template.initial m k) V l
          (assignedRoot sources _ s gp gm x₀) c (assignedRoot_matches sources _ s gp gm x₀)).symm q):ℝ)) ≠ 0 := by
  have hh := (pairedRealXi_ne_zero_scalars b sw X tb td G _ g hs gs _ hx).1
  simpa only [insertOrderedGiants_left_projection sources m k V l s gp gm gp' gm' x₀ x c g
    hs hfixed Xp Xm] using hh

end Ostmann.Arithmetic.HistoryBulkReferenceScalar

end

end OAI
