import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkIndependentReferenceTransportCoordinates
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkReferenceTestsInsertion

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkIndependentReferenceTransport
open Construction Construction.CanonicalOccurrenceTransport Conclusion
open HistoryOccurrenceVariables HistoryPairPattern HistoryPairGiantCoordinates
open HistoryPairBulkCoordinates HistoryPairBulkTransport HistoryBulkSupportConversePlan
open HistoryBulkReferenceScalarCoordinates HistoryBulkSupportConverse
open HistoryBulkReferenceTests

variable (sources : SourceFamily) (m k₀ : ℕ) (V : ℕ→ℕ) (l : ℕ)
  (s t : ℤ) (gp gm gp' gm' : ℕ)
  (x₀ y₀ x y : SourceAssignment sources (Template.current (Template.initial m k₀) l))
  (π : Equiv.Perm (Fin (Template.current (Template.initial m k₀) l).length))
  (hold : ∀i, (y₀ i).val = (x₀ (π i)).val)
  (hnew : ∀i, (y i).val = (x (π i)).val)
  (c e : HistoryChoices sources (Template.initial m k₀) V l) {outside : List ℕ}
  (hs : (assignedHistory sources (Template.initial m k₀) V l s gp gm x₀ c).Supported V outside)
  (hfixedLeft : ∀i : Fin (Template.current (Template.initial m k₀) l).length, ((Template.current (Template.initial m k₀) l).get i).role≠.bulk → (x i).val=(x₀ i).val)
  (Xp Xm : ℤ)
include hold hnew hfixedLeft

theorem integerInsertOrderedGiants_right_projection (q : Key (assignedHistory sources (Template.initial m k₀) V l t gp gm y₀ e)) :
    integerInsertOrderedGiants m k₀ (assignedHistory sources (Template.initial m k₀) V l s gp gm x₀ c) (assignedHistory sources (Template.initial m k₀) V l t gp gm y₀ e) hs (root_matches (assignedLabels sources (Template.initial m k₀) V l s gp gm x₀ c))
      (orderedIntegerSourceValues sources m k₀ l x) (fun u => if u then Xm else Xp)
      (rightMap (assignedHistory sources (Template.initial m k₀) V l s gp gm x₀ c) (assignedHistory sources (Template.initial m k₀) V l t gp gm y₀ e) q) =
      newIntegerSample sources (Template.initial m k₀) V l (assignedRoot sources (Template.current (Template.initial m k₀) l) t gp' gm' y) e (assignedRoot_matches sources (Template.current (Template.initial m k₀) l) t gp' gm' y) Xp Xm
        ((decodedCoordinateEquiv sources (Template.initial m k₀) V l (assignedRoot sources (Template.current (Template.initial m k₀) l) t gp gm y₀) e (assignedRoot_matches sources (Template.current (Template.initial m k₀) l) t gp gm y₀)).symm q) := by
  have he := insertOrderedGiants_right_projection sources m k₀ V l s t gp gm gp' gm'
    x₀ y₀ x y π hold hnew c e hs hfixedLeft Xp Xm q
  have hc := congrFun (integerInsertOrderedGiants_cast m k₀ (assignedHistory sources (Template.initial m k₀) V l s gp gm x₀ c) (assignedHistory sources (Template.initial m k₀) V l t gp gm y₀ e) hs (root_matches (assignedLabels sources (Template.initial m k₀) V l s gp gm x₀ c))
    (orderedIntegerSourceValues sources m k₀ l x) (fun u => if u then Xm else Xp))
    (rightMap (assignedHistory sources (Template.initial m k₀) V l s gp gm x₀ c) (assignedHistory sources (Template.initial m k₀) V l t gp gm y₀ e) q)
  simp only [orderedIntegerSourceValues_cast, Int.cast_ite] at hc
  have hz := congrArg (fun r : ℚ => (r : ℝ))
    (congrFun (newIntegerSample_cast sources (Template.initial m k₀) V l (assignedRoot sources (Template.current (Template.initial m k₀) l) t gp' gm' y) e (assignedRoot_matches sources (Template.current (Template.initial m k₀) l) t gp' gm' y) Xp Xm)
      ((decodedCoordinateEquiv sources (Template.initial m k₀) V l (assignedRoot sources (Template.current (Template.initial m k₀) l) t gp gm y₀) e (assignedRoot_matches sources (Template.current (Template.initial m k₀) l) t gp gm y₀)).symm q))
  simp only [Rat.cast_intCast] at hz
  exact_mod_cast hc.trans (he.trans hz.symm)

end Ostmann.Arithmetic.HistoryBulkIndependentReferenceTransport

end

end OAI
