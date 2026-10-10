import Mathlib
import OAI.Combinatorics.TriangleRemoval.Embeddings.GraphEmbeddingsRestriction
import OAI.Combinatorics.TriangleRemoval.Spectral.CountClosedWalk

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

theorem canonical_cycle_spanning (n : ℕ) (v : Fin (n+3)) :
    v ∈ (SimpleGraph.cycleGraph.cycle n).support := by
  let f : Fin (n+3) → Fin (n+3) := fun i => (SimpleGraph.cycleGraph.cycle n).getVert i
  have hf : Function.Injective f := by
    intro i j hij
    apply Fin.ext
    exact SimpleGraph.cycleGraph.isCycle_cycle.getVert_injOn'
      (by simp only [Set.mem_ofPred_eq, SimpleGraph.cycleGraph.length_cycle]; omega)
      (by simp only [Set.mem_ofPred_eq, SimpleGraph.cycleGraph.length_cycle]; omega) hij
  obtain ⟨i, hi⟩ := Finite.surjective_of_injective hf v
  exact hi ▸ (SimpleGraph.cycleGraph.cycle n).getVert_mem_support i

section WalkPatterns
variable {r k : ℕ}

def closedWalkPattern (σ : Fin r → Fin k) : SimpleGraph (Fin k) :=
  (SimpleGraph.cycleGraph r).map σ

def PatternProper (σ : Fin r → Fin k) : Prop :=
  ∀ i j, (SimpleGraph.cycleGraph r).Adj i j → σ i ≠ σ j

noncomputable def patternHom (σ : Fin r → Fin k) (hσ : PatternProper σ) :
    SimpleGraph.cycleGraph r →g closedWalkPattern σ :=
  SimpleGraph.Hom.map σ _ (fun hij => hσ _ _ hij)

@[simp] lemma patternHom_apply (σ : Fin r → Fin k) (hσ : PatternProper σ) (i : Fin r) :
    patternHom σ hσ i = σ i := rfl

lemma pattern_preconnected (σ : Fin r → Fin k) (hσ : PatternProper σ)
    (hs : Function.Surjective σ) : (closedWalkPattern σ).Preconnected :=
  SimpleGraph.Preconnected.map (patternHom σ hσ) hs SimpleGraph.cycleGraph_preconnected

theorem pattern_spanning_walk {n k : ℕ} (σ : Fin (n+3) → Fin k)
    (hσ : PatternProper σ) (hs : Function.Surjective σ) :
    ∃ a : Fin k, ∃ p : (closedWalkPattern σ).Walk a a,
      p.length = n+3 ∧ ∀ v, v ∈ p.support := by
  let p := (SimpleGraph.cycleGraph.cycle n).map (patternHom σ hσ)
  refine ⟨σ 0, p, ?_, ?_⟩
  · change ((SimpleGraph.cycleGraph.cycle n).map (patternHom σ hσ)).length = n+3
    rw [SimpleGraph.Walk.length_map, SimpleGraph.cycleGraph.length_cycle]
  · intro v
    obtain ⟨i, rfl⟩ := hs v
    change σ i ∈ ((SimpleGraph.cycleGraph.cycle n).map (patternHom σ hσ)).support
    rw [SimpleGraph.Walk.support_map]
    exact List.mem_map.mpr ⟨i, canonical_cycle_spanning n i, rfl⟩

end WalkPatterns

section PatternCounting
variable {A V : Type*} [Fintype A] [DecidableEq A] [Fintype V] [DecidableEq V]
variable (H : SimpleGraph A) (G : SimpleGraph V) [DecidableRel G.Adj]

theorem noninjective_pattern_count (r : ℕ) (hH : H.Preconnected)
    (hsize : Fintype.card A < r) (a : A) (p : H.Walk a a)
    (hlength : p.length = r) (hspan : ∀ v, v ∈ p.support)
    (Δ C : ℕ) (hΔ0 : 1 ≤ Δ)
    (hΔ : ∀ x : V, (Finset.univ.filter (G.Adj x)).card ≤ Δ)
    (hcyc : ∀ b, 3 ≤ b → b < r →
      (graphEmbeddings (SimpleGraph.cycleGraph b) G).card ≤ C * Δ ^ b) :
    (graphEmbeddings H G).card ≤
      Fintype.card V * Δ ^ (r / 2) + C * Δ ^ (r-1) := by
  classical
  by_cases htree : H.IsAcyclic
  · have hv := acyclic_spanning_walk_vertices p htree hspan
    rw [hlength] at hv
    calc
      _ ≤ Fintype.card V * Δ ^ (Fintype.card A - 1) :=
        connected_embedding_count H G hH a Δ hΔ
      _ ≤ Fintype.card V * Δ ^ (r/2) :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hΔ0 hv)
      _ ≤ _ := Nat.le_add_right _ _
  · obtain ⟨v, c, hc⟩ : ∃ v : A, ∃ c : H.Walk v v, c.IsCycle := by
      simpa only [SimpleGraph.IsAcyclic, not_forall, not_not] using htree
    have hb : 3 ≤ c.length := hc.three_le_length
    obtain ⟨f⟩ := (SimpleGraph.cycleGraph_isContained_iff (by omega : 2 < c.length)).mpr
      ⟨v, c, hc, rfl⟩
    have hcard : c.length ≤ Fintype.card A := by
      simpa using Fintype.card_le_of_injective f.toEmbedding f.injective
    have hh := cyclic_seed_embedding_count H G hH (SimpleGraph.cycleGraph c.length)
      f.toEmbedding (by exact Fin.pos_iff_nonempty.mp (by omega))
      (fun i j hij => f.toHom.map_adj hij) Δ hΔ
    have hp : Δ ^ c.length * Δ ^ (Fintype.card A - c.length) =
        Δ ^ Fintype.card A := by rw [← pow_add, Nat.add_sub_of_le hcard]
    calc
      _ ≤ (graphEmbeddings (SimpleGraph.cycleGraph c.length) G).card *
          Δ ^ (Fintype.card A-c.length) := by simpa using hh
      _ ≤ (C * Δ ^ c.length) * Δ ^ (Fintype.card A-c.length) :=
        Nat.mul_le_mul_right _ (hcyc _ hb (hcard.trans_lt hsize))
      _ = C * Δ ^ Fintype.card A := by rw [mul_assoc, hp]
      _ ≤ C * Δ ^ (r-1) := Nat.mul_le_mul_left _
        (Nat.pow_le_pow_right hΔ0 (by omega))
      _ ≤ _ := Nat.le_add_left _ _

end PatternCounting
end SharpTerminalLeave

end
end

end OAI
