import Mathlib
import OAI.Combinatorics.TriangleRemoval.Embeddings.TriangleGrowth
import OAI.Combinatorics.TriangleRemoval.Process.PathSuffix
import OAI.Combinatorics.TriangleRemoval.Process.RestrictedParent

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter
open scoped BigOperators Topology
open scoped BigOperators

namespace SharpTerminalLeave.TriangleGrowth
variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} {N R : ℕ}
variable (A : TriangleGrowth G N R)

noncomputable def nonrootForest : PathForest N := by
  refine ⟨fun v => if R ≤ v.val then A.parent v else none,?_⟩
  intro v p hp
  change (if R ≤ v.val then A.parent v else none) = some p at hp
  split_ifs at hp with hv
  exact A.parent_lt v p hv hp

lemma nonrootForest_step {x y : Fin N} (h : A.Parent x y) :
    A.nonrootForest.Step x y := by
  change (if R ≤ y.val then A.parent y else none) = some x
  rw [ite_eq_left h.1]
  exact h.2

lemma nonrootForest_ancestor {x y : Fin N} (h : A.Ancestor x y) :
    A.nonrootForest.Ancestor x y := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail y z hxy hyz ih =>
    exact Relation.ReflTransGen.tail ih (A.nonrootForest_step hyz)

lemma pathNonroots_parent_closed (a b : Fin N) :
    ∀ v ∈ A.pathSuffix a b R, ∀ p, A.nonrootForest.parent v = some p →
      p ∈ A.pathSuffix a b R := by
  intro v hv p hp
  obtain ⟨hvP,hvR⟩ := (A.mem_pathSuffix a b v R).mp hv
  change (if R ≤ v.val then A.parent v else none) = some p at hp
  rw [ite_eq_left hvR] at hp
  exact (A.mem_pathSuffix a b p R).mpr
    ⟨A.pathUnion_older_closed hvP (A.parent_mem_older hvR hp),A.parent_nonroot v p hvR hp⟩

lemma pathNonroots_cover (a b : Fin N) :
    ∀ v ∈ A.pathSuffix a b R,
      (a ∈ A.pathSuffix a b R ∧ A.nonrootForest.Ancestor v a) ∨
      (b ∈ A.pathSuffix a b R ∧ A.nonrootForest.Ancestor v b) := by
  intro v hv
  obtain ⟨hvP,hvR⟩ := (A.mem_pathSuffix a b v R).mp hv
  rcases (A.mem_pathUnion a b v).mp hvP with hroot | ha | hb
  · omega
  · exact Or.inl ⟨(A.mem_pathSuffix a b a R).mpr
      ⟨A.left_mem_pathUnion a b,hvR.trans (A.ancestor_le ha)⟩,A.nonrootForest_ancestor ha⟩
  · exact Or.inr ⟨(A.mem_pathSuffix a b b R).mpr
      ⟨A.right_mem_pathUnion a b,hvR.trans (A.ancestor_le hb)⟩,A.nonrootForest_ancestor hb⟩

noncomputable def pathForest (a b : Fin N) : PathForest (A.pathSuffix a b R).card :=
  A.nonrootForest.restrict (A.pathSuffix a b R) (A.pathNonroots_parent_closed a b)

theorem pathForest_two_path_cover (a b : Fin N) :
    ∀ i, (A.pathForest a b).OnPath (PathForest.restrictMark (A.pathSuffix a b R) a) i ∨
      (A.pathForest a b).OnPath (PathForest.restrictMark (A.pathSuffix a b R) b) i :=
  A.nonrootForest.restrict_two_path_cover _ (A.pathNonroots_parent_closed a b) a b
    (A.pathNonroots_cover a b)

theorem older_focus {v p : Fin N} (hv : R ≤ v.val) (hp : A.parent v = some p) :
    ∃ u ∈ A.older p, A.older v = {p,u} := by
  classical
  obtain ⟨x,y,hxy,hpair⟩ := Finset.card_eq_two.mp ((A.older_invariants v).2 hv).1
  have hpm := A.parent_mem_older hv hp
  rw [hpair,Finset.mem_insert,Finset.mem_singleton] at hpm
  have hsub : A.older v ⊆ insert p (A.older p) := by
    rw [older,dite_eq_left hv,hp]
    exact Finset.filter_subset _ _
  rcases hpm with rfl | rfl
  · refine ⟨y,?_,hpair⟩
    exact (Finset.mem_insert.mp (hsub (by rw [hpair]; simp))).resolve_left (Ne.symm hxy)
  · refine ⟨x,?_,?_⟩
    · exact (Finset.mem_insert.mp (hsub (by rw [hpair]; simp))).resolve_left hxy
    · simpa only [Finset.pair_comm] using hpair

end SharpTerminalLeave.TriangleGrowth

open scoped BigOperators

end

end OAI
