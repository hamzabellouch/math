import Mathlib
import OAI.Combinatorics.TriangleRemoval.Embeddings.TriangleGrowth
import OAI.Combinatorics.TriangleRemoval.Process.OlderSeed

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open Filter
open scoped BigOperators Topology
open scoped BigOperators

namespace SharpTerminalLeave.TriangleGrowth
variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} {N R : ℕ}
variable (A : TriangleGrowth G N R)

def Parent (x y : Fin N) : Prop := R ≤ y.val ∧ A.parent y = some x

def Ancestor : Fin N → Fin N → Prop := Relation.ReflTransGen A.Parent

lemma parent_older {x y : Fin N} (h : A.Parent x y) : x ∈ A.older y :=
  A.parent_mem_older h.1 h.2

lemma parent_le {x y : Fin N} (h : A.Parent x y) : x ≤ y :=
  le_of_lt (A.parent_lt y x h.1 h.2)

lemma ancestor_le {x y : Fin N} (h : A.Ancestor x y) : x ≤ y := by
  induction h with
  | refl => exact le_rfl
  | @tail y z _ hyz ih => exact ih.trans (A.parent_le hyz)

lemma ancestor_trans {x y z : Fin N} (hxy : A.Ancestor x y) (hyz : A.Ancestor y z) :
    A.Ancestor x z := hxy.trans hyz

lemma older_ancestor (v : Fin N) : ∀ x ∈ A.older v,
    x.val < R ∨ A.Ancestor x v := by
  induction v using (measure (fun v : Fin N => v.val)).wf.induction with
  | h v ih =>
    intro x hx
    by_cases hv : R ≤ v.val
    · cases hp : A.parent v with
      | none => exact Or.inl (A.older_root_of_none hv hp hx)
      | some p =>
        have hstep : A.Ancestor p v := Relation.ReflTransGen.single ⟨hv,hp⟩
        have hpv := A.parent_lt v p hv hp
        rw [older,dite_eq_left hv,hp] at hx
        rcases Finset.mem_insert.mp (Finset.mem_filter.mp hx).1 with rfl | hx
        · exact Or.inr hstep
        · exact (ih p hpv x hx).imp_right (fun h => h.trans hstep)
    · rw [A.older_eq_seed (Nat.lt_of_not_ge hv)] at hx
      exact Or.inl (A.seed_root v x hx (Nat.lt_of_not_ge hv))

noncomputable def pathUnion (a b : Fin N) : Finset (Fin N) := by
  classical
  exact Finset.univ.filter (fun x => x.val < R ∨ A.Ancestor x a ∨ A.Ancestor x b)

@[simp] lemma mem_pathUnion (a b x : Fin N) :
    x ∈ A.pathUnion a b ↔ x.val < R ∨ A.Ancestor x a ∨ A.Ancestor x b := by
  classical
  simp only [pathUnion,Finset.mem_filter,Finset.mem_univ,true_and]

lemma left_mem_pathUnion (a b : Fin N) : a ∈ A.pathUnion a b :=
  (A.mem_pathUnion a b a).mpr (Or.inr (Or.inl Relation.ReflTransGen.refl))

lemma right_mem_pathUnion (a b : Fin N) : b ∈ A.pathUnion a b :=
  (A.mem_pathUnion a b b).mpr (Or.inr (Or.inr Relation.ReflTransGen.refl))

lemma pathUnion_older_closed {a b v x : Fin N} (hv : v ∈ A.pathUnion a b)
    (hx : x ∈ A.older v) : x ∈ A.pathUnion a b := by
  apply (A.mem_pathUnion a b x).mpr
  rcases A.older_ancestor v x hx with hroot | hanc
  · exact Or.inl hroot
  · rcases (A.mem_pathUnion a b v).mp hv with hroot | ha | hb
    · exact Or.inl (lt_of_le_of_lt (A.ancestor_le hanc) hroot)
    · exact Or.inr (Or.inl (hanc.trans ha))
    · exact Or.inr (Or.inr (hanc.trans hb))

lemma pathUnion_subset_lower {a b : Fin N} {S : Set (Fin N)} (hS : IsLowerSet S)
    (hroots : ∀ x : Fin N, x.val < R → x ∈ S) (ha : a ∈ S) (hb : b ∈ S) :
    ↑(A.pathUnion a b) ⊆ S := by
  intro x hx
  rcases (A.mem_pathUnion a b x).mp hx with hroot | hanc | hanc
  · exact hroots x hroot
  · exact hS (A.ancestor_le hanc) ha
  · exact hS (A.ancestor_le hanc) hb

end SharpTerminalLeave.TriangleGrowth

end

end OAI
