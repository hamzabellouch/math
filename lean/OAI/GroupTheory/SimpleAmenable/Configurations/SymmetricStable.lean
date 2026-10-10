import Mathlib
import OAI.GroupTheory.SimpleAmenable.Homology.SymmetricH1
import OAI.GroupTheory.SimpleAmenable.Homology.FiniteGroupHomology

namespace OAI

open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits Representation Rep
namespace SimpleAmenable.SymmetricConfiguration

attribute [local instance 1200] Rep.hV2

noncomputable def successorStabilize (n : ℕ) :
    G n →* G (n+1) :=
  (castGroup (Nat.add_comm 1 n)).toMonoidHom.comp (stabilize 1 n)

noncomputable def fullHomologySequence (j : ℕ) : ℕ ⥤ ModuleCat ℤ :=
  Functor.ofSequence (fun n => TrivialHomology.map (successorStabilize n) j)

lemma successor_H1_isIso (n : ℕ) (hn : 32 ≤ n) :
    IsIso (TrivialHomology.map (successorStabilize n) 1) := by
  unfold successorStabilize
  rw [TrivialHomology.map_comp]
  have := stabilize_one_H1_isIso n hn
  have := TrivialHomology.isIso_equiv (castGroup (Nat.add_comm 1 n)) 1
  infer_instance

lemma successor_H2_isIso (n : ℕ) (hn : 34 ≤ n) :
    IsIso (TrivialHomology.map (successorStabilize n) 2) := by
  unfold successorStabilize
  rw [TrivialHomology.map_comp]
  have := stabilize_one_H2_isIso n hn
  have := TrivialHomology.isIso_equiv (castGroup (Nat.add_comm 1 n)) 2
  infer_instance
lemma fullH1_eventuallyConstant  :
    (fullHomologySequence 1).IsEventuallyConstantFrom 32 := by
  apply Functor.isEventuallyConstantFrom_of_succ
  intro n hn
  dsimp only [fullHomologySequence]
  erw [Functor.ofSequence_map_homOfLE_succ]
  exact successor_H1_isIso n hn
lemma fullH2_eventuallyConstant  :
    (fullHomologySequence 2).IsEventuallyConstantFrom 34 := by
  apply Functor.isEventuallyConstantFrom_of_succ
  intro n hn
  dsimp only [fullHomologySequence]
  erw [Functor.ofSequence_map_homOfLE_succ]
  exact successor_H2_isIso n hn

lemma fullH1_colimit_ι_isIso (m : ℕ) (hm : 32 ≤ m) :
    IsIso (colimit.ι (fullHomologySequence 1) m) :=
  (fullH1_eventuallyConstant).isIso_ι_of_isColimit'
    (colimit.isColimit _) m (homOfLE hm)

lemma fullH2_colimit_ι_isIso (m : ℕ) (hm : 34 ≤ m) :
    IsIso (colimit.ι (fullHomologySequence 2) m) :=
  (fullH2_eventuallyConstant).isIso_ι_of_isColimit'
    (colimit.isColimit _) m (homOfLE hm)
noncomputable def fullH1_colimitIso (m : ℕ) (hm : 32 ≤ m) :
    groupHomology (Rep.trivial ℤ (G m) ℤ) 1 ≅
      colimit (fullHomologySequence 1) := by
  have := fullH1_colimit_ι_isIso m hm
  let e := asIso (colimit.ι (fullHomologySequence 1) m)
  exact e
noncomputable def fullH2_colimitIso (m : ℕ) (hm : 34 ≤ m) :
    groupHomology (Rep.trivial ℤ (G m) ℤ) 2 ≅
      colimit (fullHomologySequence 2) := by
  have := fullH2_colimit_ι_isIso m hm
  let e := asIso (colimit.ι (fullHomologySequence 2) m)
  exact e
lemma finite_fullH1_iff_colimit (m : ℕ) (hm : 32 ≤ m) :
    Module.Finite ℤ (groupHomology (Rep.trivial ℤ (G m) ℤ) 1) ↔
      Module.Finite ℤ (colimit (fullHomologySequence 1) : ModuleCat ℤ) := by
  have h := FixedStageReturn.finite_stage_iff_colimit (fullHomologySequence 1) 32 m
    (fun n hn => by
      dsimp only [fullHomologySequence]
      erw [Functor.ofSequence_map_homOfLE_succ]
      exact successor_H1_isIso n hn) hm
  exact h
lemma finite_fullH2_iff_colimit (m : ℕ) (hm : 34 ≤ m) :
    Module.Finite ℤ (groupHomology (Rep.trivial ℤ (G m) ℤ) 2) ↔
      Module.Finite ℤ (colimit (fullHomologySequence 2) : ModuleCat ℤ) := by
  have h := FixedStageReturn.finite_stage_iff_colimit (fullHomologySequence 2) 34 m
    (fun n hn => by
      dsimp only [fullHomologySequence]
      erw [Functor.ofSequence_map_homOfLE_succ]
      exact successor_H2_isIso n hn) hm
  exact h
lemma stableH1_finite : Module.Finite ℤ (colimit (fullHomologySequence 1) : ModuleCat ℤ) := by
  have := FiniteGroupHomology.finite (Rep.trivial ℤ (G 32) ℤ) 1
  exact Module.Finite.equiv (fullH1_colimitIso 32 (by omega)).toLinearEquiv
lemma stableH2_finite : Module.Finite ℤ (colimit (fullHomologySequence 2) : ModuleCat ℤ) := by
  have := FiniteGroupHomology.finite (Rep.trivial ℤ (G 34) ℤ) 2
  exact Module.Finite.equiv (fullH2_colimitIso 34 (by omega)).toLinearEquiv
end SimpleAmenable.SymmetricConfiguration

end OAI
