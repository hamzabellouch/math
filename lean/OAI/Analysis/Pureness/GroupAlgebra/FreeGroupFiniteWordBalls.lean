import OAI.Analysis.Pureness.GroupAlgebra.FreeGroupInitialSubgroups
import Mathlib.GroupTheory.FreeGroup.Reduce
import Mathlib.Data.Set.Finite.List

namespace OAI
noncomputable section
namespace CuntzPureness
local instance freeGroupFiniteWordBallsDecidableEq {X : Type*} : DecidableEq X :=
  Classical.decEq X

def boundedGeneratorSubgroup (n : ℕ) : Subgroup (FreeGroup ℕ) where
  carrier := {g | ∀ p ∈ g.toWord, p.1 < n}
  one_mem' := by simp
  mul_mem' := by
    intro g h hg hh p hp
    have hm := (FreeGroup.toWord_mul_sublist g h).subset hp
    rcases List.mem_append.mp hm with hm | hm
    · exact hg p hm
    · exact hh p hm
  inv_mem' := by
    intro g hg p hp
    rw [FreeGroup.toWord_inv, FreeGroup.invRev, List.mem_reverse] at hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    exact hg q hq

lemma initialFreeSubgroup_word_bound (n : ℕ) (g : FreeGroup ℕ)
    (hg : g ∈ initialFreeSubgroup n) : ∀ p ∈ g.toWord, p.1 < n := by
  have hs : initialFreeSubgroup n ≤ boundedGeneratorSubgroup n := by
    apply (Subgroup.closure_le (boundedGeneratorSubgroup n)).mpr
    rintro _ ⟨k, hk, rfl⟩
    change ∀ p ∈ (FreeGroup.of k).toWord, p.1 < n
    simpa only [FreeGroup.toWord_of, List.mem_singleton, forall_eq] using (show k < n from hk)
  exact hs hg

theorem initialFreeSubgroup_wordBall_finite (n m : ℕ) :
    {g : FreeGroup ℕ | g ∈ initialFreeSubgroup n ∧ g.toWord.length ≤ m}.Finite := by
  let decode : List (Fin n × Bool) → FreeGroup ℕ := fun l =>
    FreeGroup.mk (l.map (fun p => (p.1.val, p.2)))
  apply ((List.finite_length_le (Fin n × Bool) m).image decode).subset
  intro g hg
  have hb := initialFreeSubgroup_word_bound n g hg.1
  let l : List (Fin n × Bool) := g.toWord.attach.map
    (fun p => (⟨p.val.1, hb p.val p.property⟩, p.val.2))
  refine ⟨l, ?_, ?_⟩
  · simpa [l] using hg.2
  · change FreeGroup.mk (l.map (fun p => (p.1.val, p.2))) = g
    have hl : l.map (fun p => (p.1.val, p.2)) = g.toWord := by
      simpa only [l, List.map_map, Function.comp_def] using List.attach_map_subtype_val g.toWord
    rw [hl, FreeGroup.mk_toWord]
end CuntzPureness

end

end OAI
