import Mathlib
import OAI.Combinatorics.TriangleRemoval.Spectral.ClosedWalkPattern

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
section ClosedWords
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def closedWords (r : ℕ) : Finset (Fin r → V) := by
  classical
  exact Finset.univ.filter (fun f => ∀ i j, (SimpleGraph.cycleGraph r).Adj i j →
    G.Adj (f i) (f j))

noncomputable def nonsimpleWords (r : ℕ) : Finset (Fin r → V) := by
  classical
  exact (closedWords G r).filter (fun f => ¬Function.Injective f)

theorem nonsimple_word_factor {r : ℕ} {f : Fin r → V}
    (hf : f ∈ nonsimpleWords G r) :
    ∃ k : Fin r, ∃ σ : Fin r → Fin k.val,
      PatternProper σ ∧ Function.Surjective σ ∧
      ∃ τ ∈ graphEmbeddings (closedWalkPattern σ) G, (fun i => τ (σ i)) = f := by
  classical
  have hfadj : ∀ i j, (SimpleGraph.cycleGraph r).Adj i j → G.Adj (f i) (f j) := by
    simpa only [nonsimpleWords, closedWords, Finset.mem_filter, Finset.mem_univ,
      true_and] using (Finset.mem_filter.mp hf).1
  have hnot := (Finset.mem_filter.mp hf).2
  let S := Finset.univ.image f
  have hcard : S.card < r := by
    have hle : S.card ≤ r := by simpa [S] using (Finset.card_image_le (s := Finset.univ) (f := f))
    refine lt_of_le_of_ne hle ?_
    intro heq
    apply hnot
    have hi : Set.InjOn f (↑(Finset.univ : Finset (Fin r))) :=
      Finset.card_image_iff.mp (by simpa [S] using heq)
    exact fun i j hij => hi (by simp) (by simp) hij
  let e : S ≃ Fin S.card := (Fintype.equivFin S).trans (finCongr (Fintype.card_coe S))
  let σ : Fin r → Fin S.card := fun i => e ⟨f i, Finset.mem_image.mpr ⟨i, by simp, rfl⟩⟩
  let τ : Fin S.card ↪ V := e.symm.toEmbedding.trans (Function.Embedding.subtype _)
  have hτσ : ∀ i, τ (σ i) = f i := by intro i; simp [τ, σ]
  have hs : Function.Surjective σ := by
    intro a
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp (e.symm a).property
    refine ⟨i, ?_⟩
    apply e.symm.injective
    apply Subtype.ext
    simpa [σ] using hi
  have hp : PatternProper σ := by
    intro i j hij heq
    exact (hfadj i j hij).ne (by rw [← hτσ i, ← hτσ j, heq])
  refine ⟨⟨S.card, hcard⟩, σ, hp, hs, τ, ?_, funext hτσ⟩
  apply (mem_graphEmbeddings τ).mpr
  intro a b hab
  obtain ⟨_, i, j, hij, hi, hj⟩ := hab
  subst a; subst b
  simpa only [hτσ] using hfadj i j hij

theorem nonsimpleWords_card_le (n : ℕ) (Δ C : ℕ) (hΔ0 : 1 ≤ Δ)
    (hΔ : ∀ x : V, (Finset.univ.filter (G.Adj x)).card ≤ Δ)
    (hcyc : ∀ b, 3 ≤ b → b < n+3 →
      (graphEmbeddings (SimpleGraph.cycleGraph b) G).card ≤ C * Δ ^ b) :
    (nonsimpleWords G (n+3)).card ≤
      (n+3) ^ (n+4) * (Fintype.card V * Δ ^ ((n+3)/2) + C * Δ ^ (n+2)) := by
  classical
  let t : (k : Fin (n+3)) → Finset (Fin (n+3) → Fin k.val) := fun _ =>
    Finset.univ.filter (fun σ => PatternProper σ ∧ Function.Surjective σ)
  let R := fun (k : Fin (n+3)) (σ : Fin (n+3) → Fin k.val) =>
    (graphEmbeddings (closedWalkPattern σ) G).image (fun τ i => τ (σ i))
  have hsub : nonsimpleWords G (n+3) ⊆ Finset.univ.biUnion (fun k => (t k).biUnion (R k)) := by
    intro f hf
    obtain ⟨k, σ, hp, hs, τ, hτ, rfl⟩ := nonsimple_word_factor G hf
    exact Finset.mem_biUnion.mpr ⟨k, by simp, Finset.mem_biUnion.mpr
      ⟨σ, by simp [t, hp, hs], Finset.mem_image.mpr ⟨τ, hτ, rfl⟩⟩⟩
  let B := Fintype.card V * Δ ^ ((n+3)/2) + C * Δ ^ (n+2)
  have hR : ∀ k, ∀ σ ∈ t k, (R k σ).card ≤ B := by
    intro k σ hσ
    have hh : PatternProper σ ∧ Function.Surjective σ := by simpa only
      [t, Finset.mem_filter, Finset.mem_univ, true_and] using hσ
    obtain ⟨a, p, hp, hs⟩ := pattern_spanning_walk σ hh.1 hh.2
    exact (Finset.card_image_le).trans (by
      simpa [B] using noninjective_pattern_count (closedWalkPattern σ) G (n+3)
        (pattern_preconnected σ hh.1 hh.2) (by simpa only [Fintype.card_fin] using k.isLt)
        a p hp hs Δ C hΔ0 hΔ hcyc)
  calc
    _ ≤ (Finset.univ.biUnion (fun k => (t k).biUnion (R k))).card := Finset.card_le_card hsub
    _ ≤ ∑ k : Fin (n+3), ∑ σ ∈ t k, (R k σ).card := by
      exact (Finset.card_biUnion_le).trans (Finset.sum_le_sum (fun k _ => Finset.card_biUnion_le))
    _ ≤ ∑ k : Fin (n+3), (t k).card * B := by
      apply Finset.sum_le_sum
      intro k hk
      simpa using Finset.sum_le_sum (hR k)
    _ ≤ ∑ _k : Fin (n+3), (n+3)^(n+3) * B := by
      apply Finset.sum_le_sum
      intro k hk
      apply Nat.mul_le_mul_right B
      calc
        (t k).card ≤ Fintype.card (Fin (n+3) → Fin k.val) := Finset.card_le_univ _
        _ = k.val^(n+3) := by simp
        _ ≤ (n+3)^(n+3) := Nat.pow_le_pow_left k.isLt.le _
    _ = (n+3)^(n+4) * B := by simp only [Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, smul_eq_mul]; rw [show n+4 = (n+3)+1 by omega, pow_succ]; ring

end ClosedWords
end SharpTerminalLeave

end
end

end OAI
