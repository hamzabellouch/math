import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkReferenceScalarCoordinatesLeft
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkReferenceTestsInsertion

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkReferenceTests
open Construction Construction.CanonicalOccurrenceTransport Conclusion
open HistoryOccurrenceVariables HistoryPairPattern HistoryPairGiantCoordinates
open HistoryPairBulkCoordinates HistoryPairBulkTransport HistoryBulkSupportConversePlan
open HistoryBulkReferenceScalarCoordinates HistoryBulkSupportConverse

section Left
variable (sources : SourceFamily) (m k₀ : ℕ) (V : ℕ→ℕ) (l : ℕ)
  (s : ℤ) (gp gm gp' gm' : ℕ)
  (x₀ x : SourceAssignment sources (Template.current (Template.initial m k₀) l))
  (c : HistoryChoices sources (Template.initial m k₀) V l) (k : History l)
  {outside : List ℕ}
variable (hs : ((assignedHistory sources (Template.initial m k₀) V l s gp gm x₀ c)).Supported V outside)
  (hfixed : ∀i : Fin ((Template.current (Template.initial m k₀) l)).length, ((Template.current (Template.initial m k₀) l).get i).role≠.bulk → (x i).val=(x₀ i).val)
  (Xp Xm : ℤ)
include hfixed

theorem integerInsertOrderedGiants_left_projection (q : Key (assignedHistory sources (Template.initial m k₀) V l s gp gm x₀ c)) :
    integerInsertOrderedGiants m k₀ (assignedHistory sources (Template.initial m k₀) V l s gp gm x₀ c) k hs (root_matches (assignedLabels sources (Template.initial m k₀) V l s gp gm x₀ c))
      (orderedIntegerSourceValues sources m k₀ l x) (fun t => if t then Xm else Xp)
      (leftMap (assignedHistory sources (Template.initial m k₀) V l s gp gm x₀ c) k q) =
      newIntegerSample sources (Template.initial m k₀) V l (assignedRoot sources (Template.current (Template.initial m k₀) l) s gp' gm' x) c (assignedRoot_matches sources (Template.current (Template.initial m k₀) l) s gp' gm' x) Xp Xm
        ((decodedCoordinateEquiv sources (Template.initial m k₀) V l (assignedRoot sources (Template.current (Template.initial m k₀) l) s gp gm x₀) c (assignedRoot_matches sources (Template.current (Template.initial m k₀) l) s gp gm x₀)).symm q) := by
  have he := insertOrderedGiants_left_projection sources m k₀ V l s gp gm gp' gm'
    x₀ x c k hs hfixed Xp Xm q
  have hc := congrFun (integerInsertOrderedGiants_cast m k₀ (assignedHistory sources (Template.initial m k₀) V l s gp gm x₀ c) k hs (root_matches (assignedLabels sources (Template.initial m k₀) V l s gp gm x₀ c))
    (orderedIntegerSourceValues sources m k₀ l x) (fun t => if t then Xm else Xp))
    (leftMap (assignedHistory sources (Template.initial m k₀) V l s gp gm x₀ c) k q)
  simp only [orderedIntegerSourceValues_cast, Int.cast_ite] at hc
  have hz := congrArg (fun r : ℚ => (r : ℝ))
    (congrFun (newIntegerSample_cast sources (Template.initial m k₀) V l
      (assignedRoot sources (Template.current (Template.initial m k₀) l) s gp' gm' x) c (assignedRoot_matches sources (Template.current (Template.initial m k₀) l) s gp' gm' x) Xp Xm)
      ((decodedCoordinateEquiv sources (Template.initial m k₀) V l (assignedRoot sources (Template.current (Template.initial m k₀) l) s gp gm x₀) c (assignedRoot_matches sources (Template.current (Template.initial m k₀) l) s gp gm x₀)).symm q))
  simp only [Rat.cast_intCast] at hz
  exact_mod_cast hc.trans (he.trans hz.symm)

theorem source_left_lines_squares_of_B (ks : k.Supported V outside)
    (hB : orderedSourceIndicatorB sources m k₀ (assignedHistory sources (Template.initial m k₀) V l s gp gm x₀ c) k hs ks (root_matches (assignedLabels sources (Template.initial m k₀) V l s gp gm x₀ c)) x Xp Xm ≠ 0) :
    ∀ i : Internal (Template.initial m k₀) l,
      ((historyDraws sources (Template.initial m k₀) V l c i).val : ℤ) ∣
        referenceLine sources (Template.initial m k₀) V outside l
          (assignedRoot sources (Template.current (Template.initial m k₀) l) s gp gm x₀) (assignedRoot sources (Template.current (Template.initial m k₀) l) s gp' gm' x)
          c (assignedRoot_matches sources (Template.current (Template.initial m k₀) l) s gp gm x₀) (assignedRoot_matches sources (Template.current (Template.initial m k₀) l) s gp' gm' x) hs Xp Xm i ∧
      ¬((historyDraws sources (Template.initial m k₀) V l c i).val : ℤ)^2 ∣
        referenceLine sources (Template.initial m k₀) V outside l
          (assignedRoot sources (Template.current (Template.initial m k₀) l) s gp gm x₀) (assignedRoot sources (Template.current (Template.initial m k₀) l) s gp' gm' x)
          c (assignedRoot_matches sources (Template.current (Template.initial m k₀) l) s gp gm x₀) (assignedRoot_matches sources (Template.current (Template.initial m k₀) l) s gp' gm' x) hs Xp Xm i := by
  exact left_reference_lines_squares_of_B sources (Template.initial m k₀) V outside l
    (assignedRoot sources (Template.current (Template.initial m k₀) l) s gp gm x₀) (assignedRoot sources (Template.current (Template.initial m k₀) l) s gp' gm' x)
    c (assignedRoot_matches sources (Template.current (Template.initial m k₀) l) s gp gm x₀) (assignedRoot_matches sources (Template.current (Template.initial m k₀) l) s gp' gm' x) hs k ks _ Xp Xm
    (integerInsertOrderedGiants_left_projection sources m k₀ V l s gp gm gp' gm'
      x₀ x c k hs hfixed Xp Xm) hB
end Left
end Ostmann.Arithmetic.HistoryBulkReferenceTests

end

end OAI
