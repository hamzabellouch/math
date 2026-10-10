import OAI.Analysis.PlanarPacking.BasisIntervals
import OAI.Analysis.PlanarPacking.Grid

namespace OAI

/-!
# Quadrature enclosures for cardinal moments

The certified quadrature grid and cardinal basis enclosures bound the finite moment rule.
-/

namespace SharpPlanar
open IntegerIntervals IntegerBasis IntegerAlpha IntegerGrid IntegerCompact

lemma basis_rule_value (n m : ℕ) (d e : Bool) :
    (∑ j : Fin 6, pieceRule (complexBasisMoment d e n j.val m) j.val) =
      momentRuleValue quadraturePoint fejerWeight n m d e := by
  unfold pieceRule momentRuleValue
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  apply Finset.sum_congr rfl
  intro v _
  have ht : diskAffine j.val (fejerNode v.val) = (quadraturePoint j.val v.val:ℂ) := by
    unfold diskAffine diskCenter quadraturePoint
    push_cast
    ring
  rw [ht,complexBasisMoment_ofReal]

lemma actual_grid_contains (j : Fin 6) (i k : Fin 16) :
    (gridRows j i k).Contains (quadraturePoint j.val (16*i.val+k.val)) := gridRows_contains j i k

lemma actual_rule_contains {n m : ℕ} (hn : n < 128) (hm : m < 128) (d e : Bool) :
    (momentRuleBox gridRows weightRows (aLookup n) (bLookup n) n m d e).Contains
      (momentRuleValue quadraturePoint fejerWeight n m d e) := by
  apply momentRuleBox_contains d e
  · exact actual_grid_contains
  · exact weightRows_contains
  · exact aLookup_contains n
  · exact bLookup_contains n
  · exact hn
  · exact hm

end SharpPlanar

end OAI
