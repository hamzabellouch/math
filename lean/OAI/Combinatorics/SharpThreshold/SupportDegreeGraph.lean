import OAI.Combinatorics.SharpThreshold.Model
import OAI.Combinatorics.SharpThreshold.SupportDegree

namespace OAI

namespace Problem313

open Finset

lemma support_vertices_card_le {n : ℕ} (S : Finset (GraphEdge n)) :
    (S.biUnion (fun e => e.val)).card ≤ 2 * S.card := by
  classical
  have h := SupportCombinatorics.card_vertices_le
    (S := S.image Subtype.val) (by
      intro e he
      obtain ⟨f, hf, rfl⟩ := mem_image.mp he
      exact f.property)
  have hv : SupportCombinatorics.vertices (S.image Subtype.val) =
      S.biUnion (fun e => e.val) := by
    ext u
    simp [SupportCombinatorics.vertices]
  simpa [hv, card_image_of_injective S Subtype.val_injective] using h

lemma support_exists_small_positive_degree {n : ℕ} (S : Finset (GraphEdge n))
    (hS : S.Nonempty) :
    ∃ u ∈ S.biUnion (fun e => e.val),
      1 ≤ (S.filter (fun e => u ∈ e.val)).card ∧
      (S.filter (fun e => u ∈ e.val)).card ^ 2 ≤ 2 * S.card := by
  classical
  obtain ⟨u, hu, hpos, hsmall⟩ := SupportCombinatorics.exists_small_positive_degree
    (S := S.image Subtype.val) (by
      intro e he
      obtain ⟨f, hf, rfl⟩ := mem_image.mp he
      exact f.property) (hS.image Subtype.val)
  have hdeg : SupportCombinatorics.degree (S.image Subtype.val) u =
      (S.filter (fun e => u ∈ e.val)).card := by
    unfold SupportCombinatorics.degree
    rw [filter_image]
    exact card_image_of_injective _ Subtype.val_injective
  refine ⟨u, ?_, ?_, ?_⟩
  · simpa [SupportCombinatorics.vertices] using hu
  · simpa [hdeg] using hpos
  · simpa [hdeg, card_image_of_injective S Subtype.val_injective] using hsmall

lemma support_exists_degree_le_cutoff {n : ℕ} (S : Finset (GraphEdge n))
    (hS : S.Nonempty) {k : ℝ} (hk : 0 ≤ k)
    (hcard : (S.card : ℝ) ≤ k ^ 2 / 2) :
    ∃ u ∈ S.biUnion (fun e => e.val),
      1 ≤ (S.filter (fun e => u ∈ e.val)).card ∧
      ((S.filter (fun e => u ∈ e.val)).card : ℝ) ≤ k := by
  obtain ⟨u, hu, hpos, hsquare⟩ := support_exists_small_positive_degree S hS
  refine ⟨u, hu, hpos, ?_⟩
  have hsquare' : ((S.filter (fun e => u ∈ e.val)).card : ℝ)^2 ≤ 2 * S.card :=
    by exact_mod_cast hsquare
  nlinarith [Nat.cast_nonneg (α := ℝ) (S.filter (fun e => u ∈ e.val)).card]

end Problem313

end OAI
