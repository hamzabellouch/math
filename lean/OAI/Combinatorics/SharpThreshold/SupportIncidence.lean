import OAI.Combinatorics.SharpThreshold.Model
import OAI.Combinatorics.SharpThreshold.SupportDegree

namespace OAI

noncomputable section

namespace Problem313

open Finset

lemma support_vertices_image {n : ℕ} (S : Finset (GraphEdge n)) :
    SupportCombinatorics.vertices (S.image Subtype.val) = S.biUnion Subtype.val := by
  ext u
  simp [SupportCombinatorics.vertices]

lemma support_degree_image {n : ℕ} (S : Finset (GraphEdge n)) (u : Fin n) :
    SupportCombinatorics.degree (S.image Subtype.val) u =
      (S.filter (fun e => u ∈ e.val)).card := by
  classical
  unfold SupportCombinatorics.degree
  rw [Finset.filter_image]
  exact Finset.card_image_of_injective _ Subtype.val_injective

lemma graph_support_vertices_card_le {n : ℕ} (S : Finset (GraphEdge n)) :
    (S.biUnion Subtype.val).card ≤ 2 * S.card := by
  classical
  have hS : ∀ e ∈ S.image Subtype.val, e.card = 2 := by
    intro e he
    obtain ⟨e, _, rfl⟩ := Finset.mem_image.mp he
    exact e.property
  have h := SupportCombinatorics.card_vertices_le hS
  rw [support_vertices_image, Finset.card_image_of_injective _ Subtype.val_injective] at h
  exact h

lemma exists_graph_support_degree_sq_le {n : ℕ} (S : Finset (GraphEdge n))
    (hne : S.Nonempty) :
    ∃ u ∈ S.biUnion Subtype.val,
      1 ≤ (S.filter (fun e => u ∈ e.val)).card ∧
      (S.filter (fun e => u ∈ e.val)).card ^ 2 ≤ 2 * S.card := by
  classical
  have hS : ∀ e ∈ S.image Subtype.val, e.card = 2 := by
    intro e he
    obtain ⟨e, _, rfl⟩ := Finset.mem_image.mp he
    exact e.property
  obtain ⟨u, hu, hd, hsq⟩ := SupportCombinatorics.exists_small_positive_degree
    hS (hne.image Subtype.val)
  rw [support_vertices_image] at hu
  rw [support_degree_image] at hd hsq
  rw [Finset.card_image_of_injective _ Subtype.val_injective] at hsq
  exact ⟨u, hu, hd, hsq⟩

/-- The graph support vertex needed in block-capture, already in the real cutoff form. -/
lemma exists_graph_support_degree_le {n : ℕ} (S : Finset (GraphEdge n))
    (hne : S.Nonempty) {k : ℝ} (hk : 0 ≤ k)
    (hcard : (S.card : ℝ) ≤ k ^ 2 / 2) :
    ∃ u ∈ S.biUnion Subtype.val,
      1 ≤ (S.filter (fun e => u ∈ e.val)).card ∧
      ((S.filter (fun e => u ∈ e.val)).card : ℝ) ≤ k := by
  obtain ⟨u, hu, hd, hsq⟩ := exists_graph_support_degree_sq_le S hne
  refine ⟨u, hu, hd, ?_⟩
  have hsq' : ((S.filter (fun e => u ∈ e.val)).card : ℝ) ^ 2 ≤
      2 * (S.card : ℝ) := by exact_mod_cast hsq
  nlinarith [sq_nonneg (((S.filter (fun e => u ∈ e.val)).card : ℝ) - k)]

lemma graph_support_vertices_card_le_cutoff {n : ℕ} (S : Finset (GraphEdge n))
    {k : ℝ} (hcard : (S.card : ℝ) ≤ k ^ 2 / 2) :
    ((S.biUnion Subtype.val).card : ℝ) ≤ k ^ 2 := by
  have h : ((S.biUnion Subtype.val).card : ℝ) ≤ 2 * (S.card : ℝ) := by
    exact_mod_cast graph_support_vertices_card_le S
  linarith

end Problem313

end

end OAI
