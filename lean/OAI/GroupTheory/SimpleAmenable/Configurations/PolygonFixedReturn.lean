import Mathlib
import OAI.GroupTheory.SimpleAmenable.Configurations.CofinalPowers
import OAI.GroupTheory.SimpleAmenable.Configurations.PolygonComponentStable
import OAI.GroupTheory.SimpleAmenable.Simplicial.FirstBarStableH1

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits MonoidalCategory Simplicial Opposite
namespace SimpleAmenable.PolygonTracks
open FreeChains ComponentTranslation GroupoidComponentHomology

attribute [local instance 1200] Rep.hV2
lemma component_sequence_succ (a n q:ℕ) :
    (homologyDiagram (C:=PolygonObject a) q).map
      ((CofinalPowers.sequence (componentGenerator a)).map (homOfLE (Nat.le_succ n))) =
        SSet.homologyMap (nerveMap (ComponentTranslation.translate (componentGenerator a)
          (componentGenerator a^n) (componentGenerator a^(n+1)) (pow_succ' _ _).symm)) Z q := by
  change SSet.homologyMap (nerveMap (ComponentTranslation.translate
    (componentGenerator a ^ (n+1-n)) _ _ _)) Z q = _
  simp only [Nat.add_sub_cancel_left,pow_one]
  rfl
lemma finite_fullH1_iff_stable (a m:ℕ) (hm : 32 ≤ m) :
    Module.Finite ℤ (groupHomology (Rep.trivial ℤ (polygonFullGroup a m) ℤ) 1) ↔
      Module.Finite ℤ (ComponentStable.object (C:=PolygonObject a) 1 : A) := by
  refine (Module.Finite.equiv_iff (standardHomologyIso a m 1).toLinearEquiv).trans ?_
  apply CofinalPowers.finite_colimit_iff (componentGenerator a) (componentGenerator_cofinal a)
    (homologyDiagram 1) 32 m hm
  intro n hn
  rw [component_sequence_succ]
  have successorIso := successor_H1_isIso a n hn
  exact component_successor_isIso a n 1
lemma finite_fullH2_iff_stable (a m:ℕ) (hm : 34 ≤ m) :
    Module.Finite ℤ (groupHomology (Rep.trivial ℤ (polygonFullGroup a m) ℤ) 2) ↔
      Module.Finite ℤ (ComponentStable.object (C:=PolygonObject a) 2 : A) := by
  refine (Module.Finite.equiv_iff (standardHomologyIso a m 2).toLinearEquiv).trans ?_
  apply CofinalPowers.finite_colimit_iff (componentGenerator a) (componentGenerator_cofinal a)
    (homologyDiagram 2) 34 m hm
  intro n hn
  rw [component_sequence_succ]
  have successorIso := successor_H2_isIso a n hn
  exact component_successor_isIso a n 2
lemma fullH1_finite_of_bar (a m:ℕ) (hm : 32 ≤ m)
    [Module.Finite ℤ ((IntervalBar.Diagram.bar (C:=PolygonObject a)).homology Z 1 : A)]
    [Module.Finite ℤ ((IntervalBar.Diagram.bar (C:=PolygonObject a)).homology Z 2 : A)] :
    Module.Finite ℤ (groupHomology (Rep.trivial ℤ (polygonFullGroup a m) ℤ) 1) :=
  (finite_fullH1_iff_stable a m hm).mpr (MarkedH1.stableH1_finite (C:=PolygonObject a))
end SimpleAmenable.PolygonTracks

end

end OAI
