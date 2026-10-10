import OAI.MeasureTheory.Falconer.Incidence.GridCount
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace OAI

/-!
# Degrees of the higher-dimensional retained graph

The vertex sets are the eligible depth-`p` grid cells for a
fixed pair of caps. A parallel test controls the first unknown cell; the
scalar constraint then controls the second, in its own cap direction.
-/

namespace Falconer
attribute [local instance] Classical.propDecidable

@[simp] theorem perpendicularPart_neg {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (w v : E) :
    perpendicularPart w (-v) = -perpendicularPart w v := by
  simp only [perpendicularPart, inner_neg_right, neg_smul]
  abel

/-- The three center tests for a fixed pair of angular caps. -/
def retainedGridEdge {d : ℕ} (s : ℝ) (w₁ w₂ : Space d) (τ : ℝ)
    (row col : (Fin d → ℤ) × (Fin d → ℤ)) : Prop :=
  ‖perpendicularPart w₁ (scaledGridPoint s col.1 - scaledGridPoint s row.1)‖ ≤ τ ∧
  ‖perpendicularPart w₂ (scaledGridPoint s col.2 - scaledGridPoint s row.2)‖ ≤ τ ∧
  |inner ℝ w₁ (scaledGridPoint s col.1 - scaledGridPoint s row.1) +
    inner ℝ w₂ (scaledGridPoint s col.2 - scaledGridPoint s row.2)| ≤ τ

theorem retainedGridEdge_symm {d : ℕ} (s : ℝ) (w₁ w₂ : Space d) (τ : ℝ)
    (row col : (Fin d → ℤ) × (Fin d → ℤ)) :
    retainedGridEdge s w₁ w₂ τ row col ↔ retainedGridEdge s w₁ w₂ τ col row := by
  have hn (u v : Space d) : u - v = -(v-u) := by abel
  simp only [retainedGridEdge, hn (scaledGridPoint s row.1),
    hn (scaledGridPoint s row.2), perpendicularPart_neg, norm_neg,
    inner_neg_right, ← neg_add, abs_neg]

theorem retainedGridEdge_swap {d : ℕ} (s : ℝ) (w₁ w₂ : Space d) (τ : ℝ)
    (row col : (Fin d → ℤ) × (Fin d → ℤ)) :
    retainedGridEdge s w₁ w₂ τ row col ↔
      retainedGridEdge s w₂ w₁ τ row.swap col.swap := by
  simp only [retainedGridEdge, Prod.fst_swap, Prod.snd_swap, add_comm]
  tauto

/-- Counting a finite set of pairs by its first-coordinate candidates and
the uniformly bounded second-coordinate fibers. -/
theorem pair_card_le {α β : Type*} [DecidableEq α] [DecidableEq β]
    (S : Finset (α × β)) (A : Finset α) (K : ℕ)
    (hA : ∀ z ∈ S, z.1 ∈ A)
    (hK : ∀ a ∈ A, ((S.filter (fun z => z.1 = a)).image Prod.snd).card ≤ K) :
    S.card ≤ K * A.card := by
  apply Finset.card_le_mul_card_image_of_maps_to hA K
  intro a ha
  have hinj : Set.InjOn Prod.snd (↑(S.filter (fun z => z.1 = a)) : Set (α × β)) := by
    intro x hx y hy hxy
    exact Prod.ext ((Finset.mem_filter.mp hx).2.trans (Finset.mem_filter.mp hy).2.symm) hxy
  rw [← Finset.card_image_of_injOn hinj]
  exact hK a ha

/-- Row degree from the first endpoint's parallel-test count. The second
endpoint only uses its unit cap direction and the grid packing bound. -/
theorem retainedGrid_degree_first {d L C : ℕ} {s τ : ℝ} (hs : 0 < s)
    (hL : 4 * τ * s ≤ L) (A B : Finset (Fin d → ℤ))
    (w₁ w₂ : Space d) (hw₂ : ‖w₂‖ = 1)
    (row : (Fin d → ℤ) × (Fin d → ℤ))
    (hparallel : (A.filter (fun z =>
      ‖perpendicularPart w₁ (scaledGridPoint s z - scaledGridPoint s row.1)‖ ≤ τ)).card ≤ C) :
    ((A ×ˢ B).filter (retainedGridEdge s w₁ w₂ τ row)).card ≤
      (2 * L + 1)^d * C := by
  classical
  let S := (A ×ˢ B).filter (retainedGridEdge s w₁ w₂ τ row)
  let T := A.filter (fun z =>
    ‖perpendicularPart w₁ (scaledGridPoint s z - scaledGridPoint s row.1)‖ ≤ τ)
  have hcount : S.card ≤ (2 * L + 1)^d * T.card := by
    apply pair_card_le S T
    · intro z hz
      obtain ⟨hz, he⟩ := Finset.mem_filter.mp hz
      exact Finset.mem_filter.mpr ⟨(Finset.mem_product.mp hz).1, he.1⟩
    · intro a _ha
      apply retained_grid_card_translated hs hL _ w₂ (scaledGridPoint s row.2) hw₂
        (c := -inner ℝ w₁ (scaledGridPoint s a - scaledGridPoint s row.1))
      · intro b hb
        obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hb
        obtain ⟨hz, hza⟩ := Finset.mem_filter.mp hz
        obtain ⟨_, he⟩ := Finset.mem_filter.mp hz
        simpa only [sub_neg_eq_add, ← hza, add_comm] using he.2.2
      · intro b hb
        obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hb
        exact (Finset.mem_filter.mp (Finset.mem_filter.mp hz).1).2.2.1
  exact hcount.trans (Nat.mul_le_mul_left _ hparallel)

/-- Both choices of the first unknown are valid, so the smaller parallel
count controls the degree. -/
theorem retainedGrid_degree_min {d L C₁ C₂ : ℕ} {s τ : ℝ} (hs : 0 < s)
    (hL : 4 * τ * s ≤ L) (A B : Finset (Fin d → ℤ))
    (w₁ w₂ : Space d) (hw₁ : ‖w₁‖ = 1) (hw₂ : ‖w₂‖ = 1)
    (row : (Fin d → ℤ) × (Fin d → ℤ))
    (h₁ : (A.filter (fun z =>
      ‖perpendicularPart w₁ (scaledGridPoint s z - scaledGridPoint s row.1)‖ ≤ τ)).card ≤ C₁)
    (h₂ : (B.filter (fun z =>
      ‖perpendicularPart w₂ (scaledGridPoint s z - scaledGridPoint s row.2)‖ ≤ τ)).card ≤ C₂) :
    ((A ×ˢ B).filter (retainedGridEdge s w₁ w₂ τ row)).card ≤
      (2 * L + 1)^d * min C₁ C₂ := by
  classical
  have hfirst := retainedGrid_degree_first hs hL A B w₁ w₂ hw₂ row h₁
  have hsecond := retainedGrid_degree_first hs hL B A w₂ w₁ hw₁ row.swap h₂
  have heq : ((A ×ˢ B).filter (retainedGridEdge s w₁ w₂ τ row)).card =
      ((B ×ˢ A).filter (retainedGridEdge s w₂ w₁ τ row.swap)).card := by
    apply Finset.card_bij (fun z _ => z.swap)
    · intro z hz
      obtain ⟨hz, he⟩ := Finset.mem_filter.mp hz
      exact Finset.mem_filter.mpr ⟨by simpa only [Finset.mem_product, Prod.fst_swap, Prod.snd_swap] using
        (Finset.mem_product.mp hz).symm, (retainedGridEdge_swap _ _ _ _ _ _).mp he⟩
    · intro a _ b _ hab
      exact Prod.swap_injective hab
    · intro z hz
      refine ⟨z.swap, ?_, Prod.swap_swap z⟩
      obtain ⟨hz, he⟩ := Finset.mem_filter.mp hz
      exact Finset.mem_filter.mpr ⟨by simpa only [Finset.mem_product, Prod.fst_swap, Prod.snd_swap] using
        (Finset.mem_product.mp hz).symm, (retainedGridEdge_swap _ _ _ _ _ _).mpr he⟩
  rw [← heq] at hsecond
  by_cases h : C₁ ≤ C₂
  · simpa only [min_eq_left h] using hfirst
  · simpa only [min_eq_right (le_of_not_ge h)] using hsecond

/-- Reversing every edge gives the identical column degree bound. -/
theorem retainedGrid_column_degree_min {d L C₁ C₂ : ℕ} {s τ : ℝ} (hs : 0 < s)
    (hL : 4 * τ * s ≤ L) (A B : Finset (Fin d → ℤ))
    (w₁ w₂ : Space d) (hw₁ : ‖w₁‖ = 1) (hw₂ : ‖w₂‖ = 1)
    (col : (Fin d → ℤ) × (Fin d → ℤ))
    (h₁ : (A.filter (fun z =>
      ‖perpendicularPart w₁ (scaledGridPoint s z - scaledGridPoint s col.1)‖ ≤ τ)).card ≤ C₁)
    (h₂ : (B.filter (fun z =>
      ‖perpendicularPart w₂ (scaledGridPoint s z - scaledGridPoint s col.2)‖ ≤ τ)).card ≤ C₂) :
    ((A ×ˢ B).filter (fun row => retainedGridEdge s w₁ w₂ τ row col)).card ≤
      (2 * L + 1)^d * min C₁ C₂ := by
  classical
  simpa only [retainedGridEdge_symm s w₁ w₂ τ _ col] using
    retainedGrid_degree_min hs hL A B w₁ w₂ hw₁ hw₂ col h₁ h₂

end Falconer

end OAI
