import Mathlib
import OAI.Combinatorics.TriangleRemoval.Embeddings.BirthGraph
import OAI.Combinatorics.TriangleRemoval.Tracking.PrefixEmbeddings
import OAI.Combinatorics.TriangleRemoval.Process.LookupGraph
import OAI.Combinatorics.TriangleRemoval.Process.BornEdges

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter
open scoped BigOperators Topology
open scoped BigOperators

namespace SharpTerminalLeave

lemma product_two_values (R : ℕ) (T : Finset ℕ) (hT : T ⊆ Finset.range R) (x y : ℝ) :
    (∏ i ∈ Finset.range R, if i ∈ T then x else y) = x^T.card * y^(R-T.card) := by
  classical
  have ht : (Finset.range R).filter (fun i => i ∈ T) = T := by
    ext i
    simp only [Finset.mem_filter]
    exact ⟨And.right,fun hi => ⟨hT hi,hi⟩⟩
  have hc := Finset.card_filter_add_card_filter_not (s := Finset.range R) (fun i => i ∈ T)
  rw [ht,Finset.card_range] at hc
  have hn : ((Finset.range R).filter (fun i => i ∉ T)).card = R-T.card := by omega
  rw [Finset.prod_ite]
  simp only [Finset.prod_const,ht,hn]

namespace BirthGraph
variable {N : ℕ} (B : BirthGraph N)

noncomputable def rootClosers (R : ℕ) : Finset ℕ :=
  ((initialVertices N R).filter (fun v => (B.older v).Nonempty)).image Fin.val

lemma rootClosers_subset (R : ℕ) : B.rootClosers R ⊆ Finset.range R := by
  intro i hi
  obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hi
  exact Finset.mem_range.mpr ((mem_initialVertices N R v).mp (Finset.mem_filter.mp hv).1)

lemma rootClosers_card (R : ℕ)
    (hs : ∀ v : Fin N, v.val < R → (B.older v).card ≤ 1) :
    (B.rootClosers R).card = (B.backEdges (initialVertices N R)).card := by
  classical
  rw [rootClosers,Finset.card_image_of_injective _ Fin.val_injective,
    B.backEdges_card,Finset.card_filter]
  apply Finset.sum_congr rfl
  intro v hv
  have hs' := hs v ((mem_initialVertices N R v).mp hv)
  by_cases hn : (B.older v).Nonempty
  · rw [ite_eq_left hn]
    have hp := Finset.card_pos.mpr hn
    omega
  · rw [ite_eq_right hn,Finset.not_nonempty_iff_eq_empty.mp hn,Finset.card_empty]

lemma rootClosers_predecessor (R : ℕ) (i : ℕ) (hi : i ∈ B.rootClosers R)
    (hN : i+1 ≤ N) : ∃ u : Fin i,
      B.graph.Adj (Fin.castLE (show i ≤ N by omega) u) ⟨i,by omega⟩ := by
  obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hi
  obtain ⟨u,hu⟩ := (Finset.mem_filter.mp hv).2
  have hlt := B.older_lt v u hu
  refine ⟨⟨u.val,hlt⟩,?_⟩
  exact Or.inl hu

theorem prefixEmbeddings_unordered_roots {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (R : ℕ) (hR : R ≤ N) (Δ : ℝ)
    (hΔ0 : 0 ≤ Δ)
    (hΔ : ∀ x : V, ((Finset.univ.filter (G.Adj x)).card : ℝ) ≤ Δ) :
    letI : DecidableRel B.graph.Adj := Classical.decRel _
    ((prefixEmbeddings B.graph G R hR).card : ℝ) ≤
      (Fintype.card V : ℝ)^(R-(B.rootClosers R).card) * Δ^(B.rootClosers R).card := by
  classical
  let b : ℕ → ℝ := fun i => if i ∈ B.rootClosers R then Δ else Fintype.card V
  have hb0 : ∀ i < N, 0 ≤ b i := by
    intro i _
    dsimp only [b]
    split_ifs <;> first | exact hΔ0 | positivity
  have hb : ∀ i (hi : i+1 ≤ N), ∀ ψ ∈ prefixEmbeddings B.graph G i (by omega),
      ((compatibleNext B.graph G hi ψ).card : ℝ) ≤ b i := by
    intro i hi ψ _
    dsimp only [b]
    by_cases hclose : i ∈ B.rootClosers R
    · rw [ite_eq_left hclose]
      obtain ⟨u,hu⟩ := B.rootClosers_predecessor R i hclose hi
      exact compatibleNext_le_degree hi ψ u hu Δ hΔ
    · rw [ite_eq_right hclose]
      exact_mod_cast compatibleNext_le_order hi ψ
  have h := prefixEmbeddings_product_bound (J := B.graph) (G := G) b hb0 hb R hR
  change _ ≤ ∏ i ∈ Finset.range R, if i ∈ B.rootClosers R then Δ else (Fintype.card V : ℝ) at h
  rw [product_two_values R (B.rootClosers R) (B.rootClosers_subset R)] at h
  simpa only [mul_comm] using h

end BirthGraph
end SharpTerminalLeave

end

end OAI
