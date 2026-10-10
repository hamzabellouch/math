import Mathlib
import OAI.Combinatorics.TriangleRemoval.Embeddings.TriangleGrowth
import OAI.Combinatorics.TriangleRemoval.Process.LookupGraph
import OAI.Combinatorics.TriangleRemoval.Process.PathSuffix
import OAI.Combinatorics.TriangleRemoval.Coupling.OrderEmbRank
import OAI.Combinatorics.TriangleRemoval.Process.Restrict

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
variable {n N R : ℕ} {G : Graph n} (A : TriangleGrowth (lookupGraph G) N R)

noncomputable def pathPattern (a b : Fin N) : BirthGraph (A.pathUnion a b).card :=
  A.birthGraph.restrict (A.pathUnion a b)
    (fun _ hv _ hx => A.pathUnion_older_closed hv hx)

noncomputable def pathIndex (a b x : Fin N) (hx : x ∈ A.pathUnion a b) :
    Fin (A.pathUnion a b).card := (A.pathUnion a b).orderIsoOfFin rfl |>.symm ⟨x,hx⟩

@[simp] lemma pathIndex_image (a b x : Fin N) (hx : x ∈ A.pathUnion a b) :
    (A.pathUnion a b).orderEmbOfFin rfl (A.pathIndex a b x hx) = x :=
  congrArg Subtype.val ((A.pathUnion a b).orderIsoOfFin rfl |>.apply_symm_apply ⟨x,hx⟩)

noncomputable def pathAssignment (a b : Fin N)
    (hi : Set.InjOn A.label (A.pathUnion a b)) : Fin (A.pathUnion a b).card ↪ Fin n where
  toFun i := A.label ((A.pathUnion a b).orderEmbOfFin rfl i)
  inj' := by
    intro i j he
    apply (A.pathUnion a b).orderEmbOfFin rfl |>.injective
    exact hi ((A.pathUnion a b).orderEmbOfFin_mem rfl i)
      ((A.pathUnion a b).orderEmbOfFin_mem rfl j) he

@[simp] lemma pathAssignment_index (a b x : Fin N) (hx : x ∈ A.pathUnion a b)
    (hi : Set.InjOn A.label (A.pathUnion a b)) :
    A.pathAssignment a b hi (A.pathIndex a b x hx) = A.label x := by
  change A.label ((A.pathUnion a b).orderEmbOfFin rfl (A.pathIndex a b x hx)) = A.label x
  rw [A.pathIndex_image]

theorem pathPattern_nonroot (a b : Fin N) (i : Fin (A.pathUnion a b).card)
    (hi : R ≤ i.val) : ((A.pathPattern a b).older i).card = 2 := by
  rw [pathPattern,BirthGraph.restrict_older_card]
  exact ((A.older_invariants _).2 (orderEmb_nonroot _
    (fun x hx => (A.mem_pathUnion a b x).mpr (Or.inl hx)) i hi)).1

theorem pathAssignment_mem {a b : Fin N}
    (hi : Set.InjOn A.label (A.pathUnion a b))
    (he : A.birthGraph.ExtraEdge (lookupGraph G) A.label a b) :
    A.pathAssignment a b hi ∈ graphEmbeddingSet
      (insert ({A.pathIndex a b a (A.left_mem_pathUnion a b),
        A.pathIndex a b b (A.right_mem_pathUnion a b)} : Finset _)
        ((A.pathPattern a b).backEdges Finset.univ)) G := by
  classical
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _,?_⟩
  intro e he'
  obtain ⟨f,hf,rfl⟩ := Finset.mem_image.mp he'
  rcases Finset.mem_insert.mp hf with rfl | hf
  · simpa only [Finset.map_insert,Finset.map_singleton,A.pathAssignment_index] using he.2.2.2
  · obtain ⟨v,_,u,hu,rfl⟩ := (A.pathPattern a b).backEdges_mem_pair hf
    have hAdj : A.birthGraph.graph.Adj ((A.pathUnion a b).orderEmbOfFin rfl u)
        ((A.pathUnion a b).orderEmbOfFin rfl v) := by
      exact (BirthGraph.restrict_graph_adj _ _ _ _ _).mp (Or.inl hu)
    have h := A.spawnRules.edge_labels _ _ hAdj
    simp only [Finset.map_insert,Finset.map_singleton]
    change ({A.label ((A.pathUnion a b).orderEmbOfFin rfl u),
      A.label ((A.pathUnion a b).orderEmbOfFin rfl v)} : Finset (Fin n)) ∈ G
    exact h.2

lemma pathPattern_extra {a b : Fin N}
    (he : A.birthGraph.ExtraEdge (lookupGraph G) A.label a b) :
    let a' := A.pathIndex a b a (A.left_mem_pathUnion a b)
    let b' := A.pathIndex a b b (A.right_mem_pathUnion a b)
    a' ≠ b' ∧ ¬ (A.pathPattern a b).graph.Adj a' b' := by
  dsimp only
  constructor
  · intro h
    have hh := congrArg ((A.pathUnion a b).orderEmbOfFin rfl) h
    apply he.1
    simpa only [A.pathIndex_image] using hh
  · intro h
    have hh := (BirthGraph.restrict_graph_adj _ _ _ _ _).mp h
    apply he.2.1
    simpa only [A.pathIndex_image] using hh

theorem pathPattern_covered (a b : Fin N) (k : ℕ)
    (hR : R ≤ k) (hk : k < (A.pathUnion a b).card) :
    (A.pathPattern a b).Covered (Finset.univ.filter (fun x => k ≤ x.val))
      (A.pathIndex a b a (A.left_mem_pathUnion a b))
      (A.pathIndex a b b (A.right_mem_pathUnion a b)) := by
  classical
  let s := A.pathUnion a b
  let y := s.orderEmbOfFin rfl ⟨k,hk⟩
  have hRy : R ≤ y.val := orderEmb_nonroot s
    (fun x hx => (A.mem_pathUnion a b x).mpr (Or.inl hx)) ⟨k,hk⟩ hR
  have hZ : A.pathSuffix a b y.val ⊆ s := by
    intro x hx
    exact ((A.mem_pathSuffix a b x y.val).mp hx).1
  have heq : reindexSet s (A.pathSuffix a b y.val) =
      Finset.univ.filter (fun x => k ≤ x.val) := by
    ext i
    simp only [mem_reindexSet,A.mem_pathSuffix,Finset.mem_filter,Finset.mem_univ,true_and]
    have him := s.orderEmbOfFin_mem rfl i
    have hiff : y ≤ s.orderEmbOfFin rfl i ↔ (⟨k,hk⟩ : Fin s.card) ≤ i :=
      (s.orderEmbOfFin rfl).le_iff_le
    exact ⟨fun h => hiff.mp h.2,fun h => ⟨him,hiff.mpr h⟩⟩
  have h := A.birthGraph.restrict_covered s
    (fun _ hv _ hx => A.pathUnion_older_closed hv hx)
    (A.pathSuffix a b y.val) hZ (A.left_mem_pathUnion a b) (A.right_mem_pathUnion a b)
    (A.pathSuffix_covered a b y.val hRy)
  rw [heq] at h
  exact h

end SharpTerminalLeave.TriangleGrowth

end

end OAI
