import Mathlib
import OAI.Combinatorics.TriangleRemoval.Embeddings.TriangleGrowth
import OAI.Combinatorics.TriangleRemoval.Process.Parent
import OAI.Combinatorics.TriangleRemoval.Process.Within
import OAI.Combinatorics.TriangleRemoval.Tracking.RootedExposedCollisionWitness

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

lemma pathUnion_ancestor_closed {a b x y : Fin N} (hxy : A.Ancestor x y)
    (hy : y ∈ A.pathUnion a b) : x ∈ A.pathUnion a b := by
  apply (A.mem_pathUnion a b x).mpr
  rcases (A.mem_pathUnion a b y).mp hy with hroot | ha | hb
  · exact Or.inl (lt_of_le_of_lt (A.ancestor_le hxy) hroot)
  · exact Or.inr (Or.inl (hxy.trans ha))
  · exact Or.inr (Or.inr (hxy.trans hb))

noncomputable def pathSuffix (a b : Fin N) (cut : ℕ) : Finset (Fin N) :=
  (A.pathUnion a b).filter (fun x => cut ≤ x.val)

@[simp] lemma mem_pathSuffix (a b x : Fin N) (cut : ℕ) :
    x ∈ A.pathSuffix a b cut ↔ x ∈ A.pathUnion a b ∧ cut ≤ x.val := by
  simp only [pathSuffix,Finset.mem_filter]

lemma within_pathSuffix {a b x y : Fin N} {cut : ℕ} (hxy : A.Ancestor x y)
    (hy : y ∈ A.pathUnion a b) (hx : cut ≤ x.val) :
    A.birthGraph.Within (A.pathSuffix a b cut) x y := by
  induction hxy using Relation.ReflTransGen.head_induction_on with
  | refl => exact Relation.ReflTransGen.refl
  | @head x c hxc hcy ih =>
    have hc : cut ≤ c.val := hx.trans (A.parent_le hxc)
    have hxP : x ∈ A.pathUnion a b := A.pathUnion_ancestor_closed
      (Relation.ReflTransGen.head hxc hcy) hy
    have hcP : c ∈ A.pathUnion a b := A.pathUnion_ancestor_closed hcy hy
    exact Relation.ReflTransGen.head
      ⟨(A.mem_pathSuffix a b x cut).mpr ⟨hxP,hx⟩,
        (A.mem_pathSuffix a b c cut).mpr ⟨hcP,hc⟩,A.parent_older hxc⟩ (ih hc)

theorem pathSuffix_covered (a b : Fin N) (cut : ℕ) (hcut : R ≤ cut) :
    A.birthGraph.Covered (A.pathSuffix a b cut) a b := by
  intro x hx
  obtain ⟨hxP,hxc⟩ := (A.mem_pathSuffix a b x cut).mp hx
  rcases (A.mem_pathUnion a b x).mp hxP with hroot | ha | hb
  · exact False.elim ((Nat.not_le_of_gt hroot) (hcut.trans hxc))
  · refine Or.inl ⟨?_,A.within_pathSuffix ha (A.left_mem_pathUnion a b) hxc⟩
    exact (A.mem_pathSuffix a b a cut).mpr
      ⟨A.left_mem_pathUnion a b,hxc.trans (A.ancestor_le ha)⟩
  · refine Or.inr ⟨?_,A.within_pathSuffix hb (A.right_mem_pathUnion a b) hxc⟩
    exact (A.mem_pathSuffix a b b cut).mpr
      ⟨A.right_mem_pathUnion a b,hxc.trans (A.ancestor_le hb)⟩

lemma pathSuffix_mark {a b : Fin N} {cut : ℕ} (hcut : R ≤ cut)
    (hne : (A.pathSuffix a b cut).Nonempty) :
    a ∈ A.pathSuffix a b cut ∨ b ∈ A.pathSuffix a b cut := by
  obtain ⟨x,hx⟩ := hne
  exact (A.pathSuffix_covered a b cut hcut x hx).imp And.left And.left

theorem pathSuffix_sparse {a b : Fin N} {cut : ℕ} (hcut : R ≤ cut)
    {I U : Finset (Fin N)} (hI : Disjoint I (A.pathSuffix a b cut))
    (hU : U ⊆ A.pathSuffix a b cut) (hproper : U ≠ A.pathSuffix a b cut) :
    ((insert ({a,b} : Finset (Fin N)) (A.birthGraph.backEdges (A.pathSuffix a b cut))).filter
      (fun e => e ⊆ I ∪ U)).card ≤ 2 * U.card := by
  apply A.birthGraph.proper_suffix_sparse hI hU hproper
  · intro v hv
    exact ((A.older_invariants v).2 (hcut.trans ((A.mem_pathSuffix a b v cut).mp hv).2)).1
  · exact A.pathSuffix_covered a b cut hcut

theorem injective_path_collision {v w : Fin N} (hne : v ≠ w) {T : Finset V}
    (hv : A.birthGraph.ExposedAt G A.label v T)
    (hw : A.birthGraph.ExposedAt G A.label w T) :
    ∃ a b : Fin N, A.birthGraph.ExtraEdge G A.label a b ∧
      Set.InjOn A.label (A.pathUnion a b) := by
  obtain ⟨S,hS,hi,hroots,a,ha,b,hb,he⟩ :=
    A.birthGraph.rooted_exposed_collision_witness G A.label A.spawnRules R A.roots_injective
      (fun z hz => ((A.older_invariants z).2 hz).1) hne hv hw
  exact ⟨a,b,he,hi.mono (A.pathUnion_subset_lower hS hroots ha hb)⟩

end SharpTerminalLeave.TriangleGrowth

end

end OAI
