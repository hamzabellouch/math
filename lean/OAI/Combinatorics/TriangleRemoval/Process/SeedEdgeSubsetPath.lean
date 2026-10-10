import Mathlib
import OAI.Combinatorics.TriangleRemoval.Process.PathPattern
import OAI.Combinatorics.TriangleRemoval.Embeddings.PathBirthIndex
import OAI.Combinatorics.TriangleRemoval.Process.RootClosers

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
variable {n N R : ℕ} {G : Graph n} (A : TriangleGrowth (lookupGraph G) N R)

lemma seed_edge_subset_pathUnion (a b : Fin N) {e : Finset (Fin N)}
    (he : e ∈ A.seed.backEdges A.roots) : e ⊆ A.pathUnion a b := by
  obtain ⟨v,hv,u,hu,rfl⟩ := A.seed.backEdges_mem_pair he
  have hvR := (A.mem_roots v).mp hv
  have huR := A.seed_root v u hu hvR
  intro x hx
  rcases Finset.mem_insert.mp hx with rfl | hx
  · exact (A.mem_pathUnion a b x).mpr (Or.inl huR)
  · have h := Finset.mem_singleton.mp hx
    subst x
    exact (A.mem_pathUnion a b v).mpr (Or.inl hvR)

lemma pathRootEdges_card (a b : Fin N) :
    (A.pathRootEdges a b).card = (A.seed.backEdges A.roots).card := by
  classical
  apply Finset.card_image_of_injOn
  intro e he f hf h
  exact reindexSet_inj (A.seed_edge_subset_pathUnion a b he)
    (A.seed_edge_subset_pathUnion a b hf) h

lemma pathPattern_rootEdges (a b : Fin N) (hR : R ≤ N) :
    (A.pathPattern a b).backEdges (initialVertices (A.pathUnion a b).card R) =
      A.pathRootEdges a b := by
  classical
  let S := A.pathUnion a b
  have hroot : ∀ x : Fin N, x.val < R → x ∈ S :=
    fun x hx => (A.mem_pathUnion a b x).mpr (Or.inl hx)
  ext e
  constructor
  · intro he
    obtain ⟨v,hv,u,hu,rfl⟩ := (A.pathPattern a b).backEdges_mem_pair he
    have hv' := (mem_initialVertices _ _ _).mp hv
    have hvR : (S.orderEmbOfFin rfl v).val < R := by
      rw [orderEmb_initial S hR hroot v hv']
      exact hv'
    have hu' : S.orderEmbOfFin rfl u ∈ A.seed.older (S.orderEmbOfFin rfl v) := by
      change u ∈ reindexSet S (A.older (S.orderEmbOfFin rfl v)) at hu
      rw [mem_reindexSet] at hu
      rwa [A.older_eq_seed hvR] at hu
    have hem : ({S.orderEmbOfFin rfl u,S.orderEmbOfFin rfl v} : Finset (Fin N)) ∈
        A.seed.backEdges A.roots :=
      Finset.mem_biUnion.mpr ⟨_,(A.mem_roots _).mpr hvR,Finset.mem_image.mpr ⟨_,hu',rfl⟩⟩
    apply Finset.mem_image.mpr
    refine ⟨_,hem,?_⟩
    rw [reindexSet_pair S _ _ (S.orderEmbOfFin_mem rfl u) (S.orderEmbOfFin_mem rfl v)]
    simp only [PathForest.index_embed]
  · intro he
    obtain ⟨f,hf,rfl⟩ := Finset.mem_image.mp he
    obtain ⟨v,hv,u,hu,rfl⟩ := A.seed.backEdges_mem_pair hf
    have hvR := (A.mem_roots v).mp hv
    have huR := A.seed_root v u hu hvR
    have hvP := hroot v hvR
    have huP := hroot u huR
    rw [reindexSet_pair S u v huP hvP]
    apply Finset.mem_biUnion.mpr
    refine ⟨PathForest.index S v hvP,?_,Finset.mem_image.mpr
      ⟨PathForest.index S u huP,?_,rfl⟩⟩
    · apply (mem_initialVertices _ _ _).mpr
      change ((S.orderIsoOfFin rfl).symm ⟨v,hvP⟩).val < R
      rw [initial_rank S hroot v hvR]
      exact hvR
    · change PathForest.index S u huP ∈
        reindexSet S (A.older (S.orderEmbOfFin rfl (PathForest.index S v hvP)))
      rw [mem_reindexSet]
      rw [PathForest.embed_index,PathForest.embed_index,A.older_eq_seed hvR]
      exact hu

lemma pathPattern_root_small (a b : Fin N) (hR : R ≤ N)
    (v : Fin (A.pathUnion a b).card) (hv : v.val < R) :
    ((A.pathPattern a b).older v).card ≤ 1 := by
  rw [pathPattern,BirthGraph.restrict_older_card]
  have hvR : ((A.pathUnion a b).orderEmbOfFin rfl v).val < R := by
    rw [orderEmb_initial _ hR (fun x hx => (A.mem_pathUnion a b x).mpr (Or.inl hx)) v hv]
    exact hv
  change (A.older _).card ≤ 1
  rw [A.older_eq_seed hvR]
  exact A.seed_small _ hvR

lemma pathPattern_rootClosers (a b : Fin N) (hR : R ≤ N) :
    ((A.pathPattern a b).rootClosers R).card = (A.seed.backEdges A.roots).card := by
  rw [(A.pathPattern a b).rootClosers_card R (A.pathPattern_root_small a b hR),
    A.pathPattern_rootEdges a b hR,A.pathRootEdges_card]

lemma path_mark_reaches_suffix (a b : Fin N) (k : ℕ)
    (hR : R ≤ k) (hk : k < (A.pathUnion a b).card) :
    k ≤ (A.pathIndex a b a (A.left_mem_pathUnion a b)).val ∨
      k ≤ (A.pathIndex a b b (A.right_mem_pathUnion a b)).val := by
  have hc := A.pathPattern_covered a b k hR hk ⟨k,hk⟩
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _,le_refl _⟩)
  rcases hc with ⟨ha,_⟩ | ⟨hb,_⟩
  · exact Or.inl (Finset.mem_filter.mp ha).2
  · exact Or.inr (Finset.mem_filter.mp hb).2

end SharpTerminalLeave.TriangleGrowth

end

end OAI
