import Mathlib
import OAI.Combinatorics.TriangleRemoval.Embeddings.GraphEmbeddings

namespace OAI

section
section
open Filter
open scoped BigOperators Topology
open InnerProductSpace
open scoped InnerProductSpace
open scoped BigOperators NNReal
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator
open Matrix InnerProductSpace
open scoped BigOperators

namespace SharpTerminalLeave
section EmbeddingCyclicSeed
variable {A B V : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
  [Fintype V] [DecidableEq V]
variable (H : SimpleGraph A) (G : SimpleGraph V) [DecidableRel G.Adj]

omit [DecidableEq B] in

theorem graphEmbeddings_restriction_le (hH : H.Preconnected) (Δ : ℕ)
    (hΔ : ∀ x : V, (Finset.univ.filter (G.Adj x)).card ≤ Δ)
    (c : B ↪ A) (hB : Nonempty B) (t : Finset (B ↪ V))
    (ht : ∀ f ∈ graphEmbeddings H G, c.trans f ∈ t) :
    (graphEmbeddings H G).card ≤ t.card * Δ ^ (Fintype.card A - Fintype.card B) := by
  classical
  let S : Finset A := Finset.univ.map c
  have hS : S.Nonempty := by
    obtain ⟨b⟩ := hB
    exact ⟨c b, Finset.mem_map.mpr ⟨b, Finset.mem_univ _, rfl⟩⟩
  have hSc : Sᶜ.card = Fintype.card A - Fintype.card B := by
    simp [S, Finset.card_compl]
  have hfib : ∀ χ ∈ t,
      ((graphEmbeddings H G).filter (fun f => c.trans f = χ)).card ≤
        Δ ^ (Fintype.card A - Fintype.card B) := by
    intro χ _
    let sf := (graphEmbeddings H G).filter (fun f => c.trans f = χ)
    by_cases hs : sf.Nonempty
    · obtain ⟨f₀, hf₀⟩ := hs
      have hcomp := (Finset.mem_filter.mp hf₀).2
      have heq : sf = rootedEmbeddingFiber H G S f₀ := by
        ext f
        simp only [sf, Finset.mem_filter, mem_rootedEmbeddingFiber]
        constructor
        · rintro ⟨hf, he⟩
          refine ⟨hf, ?_⟩
          intro a ha
          obtain ⟨b, _, rfl⟩ := Finset.mem_map.mp ha
          have hh := congrArg (fun χ : B ↪ V => χ b) (he.trans hcomp.symm)
          exact hh
        · rintro ⟨hf, he⟩
          refine ⟨hf, ?_⟩
          rw [← hcomp]
          apply Function.Embedding.ext
          intro b
          exact he (c b) (Finset.mem_map.mpr ⟨b, Finset.mem_univ _, rfl⟩)
      change sf.card ≤ _
      rw [heq, ← hSc]
      exact rootedEmbeddingFiber_le hH Δ hΔ S hS f₀
    · have he : sf = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
      change sf.card ≤ _
      rw [he, Finset.card_empty]
      exact Nat.zero_le _
  calc
    _ = ∑ χ ∈ t, ((graphEmbeddings H G).filter (fun f => c.trans f = χ)).card :=
      Finset.card_eq_sum_card_fiberwise ht
    _ ≤ ∑ _χ ∈ t, Δ ^ (Fintype.card A - Fintype.card B) := Finset.sum_le_sum hfib
    _ = _ := by simp

theorem connected_embedding_count (hH : H.Preconnected) (a : A) (Δ : ℕ)
    (hΔ : ∀ x : V, (Finset.univ.filter (G.Adj x)).card ≤ Δ) :
    (graphEmbeddings H G).card ≤ Fintype.card V * Δ ^ (Fintype.card A - 1) := by
  classical
  let c : Unit ↪ A := ⟨fun _ => a, fun _ _ _ => Subsingleton.elim _ _⟩
  have hh := graphEmbeddings_restriction_le H G hH Δ hΔ c inferInstance
    Finset.univ (fun _ _ => Finset.mem_univ _)
  have hunit : Fintype.card (Unit ↪ V) = Fintype.card V := by
    let e : (Unit ↪ V) ≃ V :=
      { toFun := fun f => f ()
        invFun := fun v => ⟨fun _ => v, fun _ _ _ => Subsingleton.elim _ _⟩
        left_inv := by intro f; ext x; cases x; rfl
        right_inv := fun _ => rfl }
    exact Fintype.card_congr e
  simpa only [Finset.card_univ, Fintype.card_unit, hunit] using hh

omit [DecidableEq B] in

theorem cyclic_seed_embedding_count (hH : H.Preconnected) (K : SimpleGraph B)
    (c : B ↪ A) (hB : Nonempty B)
    (hc : ∀ b b', K.Adj b b' → H.Adj (c b) (c b')) (Δ : ℕ)
    (hΔ : ∀ x : V, (Finset.univ.filter (G.Adj x)).card ≤ Δ) :
    (graphEmbeddings H G).card ≤
      (graphEmbeddings K G).card * Δ ^ (Fintype.card A - Fintype.card B) := by
  apply graphEmbeddings_restriction_le H G hH Δ hΔ c hB (graphEmbeddings K G)
  intro f hf
  apply (mem_graphEmbeddings (c.trans f)).mpr
  intro b b' hb
  exact (mem_graphEmbeddings f).mp hf _ _ (hc b b' hb)

end EmbeddingCyclicSeed
end SharpTerminalLeave

open scoped BigOperators

end
end

end OAI
