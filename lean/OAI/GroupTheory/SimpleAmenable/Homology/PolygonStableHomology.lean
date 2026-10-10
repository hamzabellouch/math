import Mathlib
import OAI.GroupTheory.SimpleAmenable.Homology.FullH2
import OAI.GroupTheory.SimpleAmenable.Homology.FiniteGroupHomology

namespace OAI

open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits Representation Rep
namespace SimpleAmenable.PolygonTracks

attribute [local instance 1200] Rep.hV2

noncomputable def successorStabilize (a n : ℕ) :
    polygonFullGroup a n →* polygonFullGroup a (n+1) :=
  (castFull a (Nat.add_comm 1 n)).toMonoidHom.comp (stabilize a 1 n)

noncomputable def fullHomologySequence (a j : ℕ) : ℕ ⥤ ModuleCat ℤ :=
  Functor.ofSequence (fun n => TrivialHomology.map (successorStabilize a n) j)

lemma successor_H1_isIso (a n : ℕ) (hn : 32 ≤ n) :
    IsIso (TrivialHomology.map (successorStabilize a n) 1) := by
  unfold successorStabilize
  rw [TrivialHomology.map_comp]
  have := PolygonPlacement.Configuration.stabilize_H1_isIso a n hn
  have := TrivialHomology.isIso_equiv (castFull a (Nat.add_comm 1 n)) 1
  infer_instance

lemma successor_H2_isIso (a n : ℕ) (hn : 34 ≤ n) :
    IsIso (TrivialHomology.map (successorStabilize a n) 2) := by
  unfold successorStabilize
  rw [TrivialHomology.map_comp]
  have := PolygonPlacement.Configuration.stabilize_H2_isIso a n hn
  have := TrivialHomology.isIso_equiv (castFull a (Nat.add_comm 1 n)) 2
  infer_instance
lemma fullH1_eventuallyConstant (a : ℕ) :
    (fullHomologySequence a 1).IsEventuallyConstantFrom 32 := by
  apply Functor.isEventuallyConstantFrom_of_succ
  intro n hn
  dsimp only [fullHomologySequence]
  erw [Functor.ofSequence_map_homOfLE_succ]
  exact successor_H1_isIso a n hn
lemma fullH2_eventuallyConstant (a : ℕ) :
    (fullHomologySequence a 2).IsEventuallyConstantFrom 34 := by
  apply Functor.isEventuallyConstantFrom_of_succ
  intro n hn
  dsimp only [fullHomologySequence]
  erw [Functor.ofSequence_map_homOfLE_succ]
  exact successor_H2_isIso a n hn

lemma fullH1_colimit_ι_isIso (a m : ℕ) (hm : 32 ≤ m) :
    IsIso (colimit.ι (fullHomologySequence a 1) m) :=
  (fullH1_eventuallyConstant a).isIso_ι_of_isColimit'
    (colimit.isColimit _) m (homOfLE hm)

lemma fullH2_colimit_ι_isIso (a m : ℕ) (hm : 34 ≤ m) :
    IsIso (colimit.ι (fullHomologySequence a 2) m) :=
  (fullH2_eventuallyConstant a).isIso_ι_of_isColimit'
    (colimit.isColimit _) m (homOfLE hm)
noncomputable def fullH1_colimitIso (a m : ℕ) (hm : 32 ≤ m) :
    groupHomology (Rep.trivial ℤ (polygonFullGroup a m) ℤ) 1 ≅
      colimit (fullHomologySequence a 1) := by
  haveI := fullH1_colimit_ι_isIso a m hm
  let e := asIso (colimit.ι (fullHomologySequence a 1) m)
  exact e
noncomputable def fullH2_colimitIso (a m : ℕ) (hm : 34 ≤ m) :
    groupHomology (Rep.trivial ℤ (polygonFullGroup a m) ℤ) 2 ≅
      colimit (fullHomologySequence a 2) := by
  haveI := fullH2_colimit_ι_isIso a m hm
  let e := asIso (colimit.ι (fullHomologySequence a 2) m)
  exact e
lemma finite_fullH1_iff_colimit (a m : ℕ) (hm : 32 ≤ m) :
    Module.Finite ℤ (groupHomology (Rep.trivial ℤ (polygonFullGroup a m) ℤ) 1) ↔
      Module.Finite ℤ (colimit (fullHomologySequence a 1) : ModuleCat ℤ) := by
  have h := FixedStageReturn.finite_stage_iff_colimit (fullHomologySequence a 1) 32 m
    (fun n hn => by
      dsimp only [fullHomologySequence]
      erw [Functor.ofSequence_map_homOfLE_succ]
      exact successor_H1_isIso a n hn) hm
  exact h
lemma finite_fullH2_iff_colimit (a m : ℕ) (hm : 34 ≤ m) :
    Module.Finite ℤ (groupHomology (Rep.trivial ℤ (polygonFullGroup a m) ℤ) 2) ↔
      Module.Finite ℤ (colimit (fullHomologySequence a 2) : ModuleCat ℤ) := by
  have h := FixedStageReturn.finite_stage_iff_colimit (fullHomologySequence a 2) 34 m
    (fun n hn => by
      dsimp only [fullHomologySequence]
      erw [Functor.ofSequence_map_homOfLE_succ]
      exact successor_H2_isIso a n hn) hm
  exact h
end SimpleAmenable.PolygonTracks

end OAI
