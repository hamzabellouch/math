import Mathlib
import OAI.Combinatorics.TriangleRemoval.Embeddings.ReindexEmbedding
import OAI.Combinatorics.TriangleRemoval.Process.RealCardFiberBound

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open Filter
open scoped BigOperators Topology
open scoped BigOperators

namespace SharpTerminalLeave

def restrictLabel {N n : ℕ} (P : Finset (Fin N)) (φ : Fin N ↪ Fin n) :
    {x // x ∈ P} ↪ Fin n := (Function.Embedding.subtype _).trans φ

@[simp] lemma restrictLabel_apply {N n : ℕ} (P : Finset (Fin N))
    (φ : Fin N ↪ Fin n) (x : {x // x ∈ P}) : restrictLabel P φ x = φ x := rfl

noncomputable def graphEmbeddingSet {N n : ℕ} (F : Graph N) (G : Graph n) :
    Finset (Fin N ↪ Fin n) := Finset.univ.filter (fun φ => F.image (fun e => e.map φ) ⊆ G)

theorem graphEmbeddingSet_count_glue {N n : ℕ}
    (s I P : Finset (Fin N)) (E F : Graph N) (G : Graph n)
    (hE : ∀ e ∈ E, e ⊆ s) (hsimple : ∀ e ∈ E, e.card = 2)
    (hind : ∀ e ∈ E, ¬ e ⊆ I) (hIP : I ⊆ P)
    (hcover : P ∪ s = Finset.univ) (hEF : E ⊆ F)
    (A : Finset ({x // x ∈ P} ↪ Fin n))
    (hA : ∀ φ ∈ graphEmbeddingSet F G, restrictLabel P φ ∈ A)
    (κ : ℝ) (hκ : ∀ ξ ∈ A, rootedCount (reindexTemplate s E I hE hsimple hind)
      (boundaryInjection s I P hIP ξ) G ≤ κ) :
    ((graphEmbeddingSet F G).card : ℝ) ≤ κ * A.card := by
  classical
  apply real_card_le_fiber_bound _ A (restrictLabel P) hA κ
  intro ξ hξ
  have heq : (graphEmbeddingSet F G).filter (fun φ => restrictLabel P φ = ξ) =
      Finset.univ.filter (fun φ : Fin N ↪ Fin n =>
        (∀ x : {x // x ∈ P}, φ x = ξ x) ∧ F.image (fun e => e.map φ) ⊆ G) := by
    ext φ
    simp only [graphEmbeddingSet,Finset.mem_filter,Finset.mem_univ,true_and,
      Function.Embedding.ext_iff,restrictLabel_apply,and_comm]
  rw [heq]
  exact (graphEmbedding_fiber_le_rootedCount s I P E F G hE hsimple hind hIP hcover hEF ξ).trans
    (hκ ξ hξ)

end SharpTerminalLeave

end

end OAI
