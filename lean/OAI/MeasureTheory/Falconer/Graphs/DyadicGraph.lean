import OAI.MeasureTheory.Falconer.Estimates.DyadicCenters
import OAI.MeasureTheory.Falconer.Graphs.GraphSchur

namespace OAI

/-!
# Retained graph on the actual dyadic cells

The grid degree estimate is transported to arbitrary finite collections
of equal-depth descendants. Their original cube centers define every
test. The final Schur bound can therefore be applied directly to the
endpoint transforms restricted to those cells.
-/

namespace Falconer
attribute [local instance] Classical.propDecidable

def retainedDyadicEdge {d : ℕ} (Q₁ Q₂ : DyadicCube d) (w₁ w₂ : Space d) (τ : ℝ)
    (row col : List (Fin d → Bool) × List (Fin d → Bool)) : Prop :=
  ‖perpendicularPart w₁ ((Q₁.descendant col.1).center - (Q₁.descendant row.1).center)‖ ≤ τ ∧
  ‖perpendicularPart w₂ ((Q₂.descendant col.2).center - (Q₂.descendant row.2).center)‖ ≤ τ ∧
  |inner ℝ w₁ ((Q₁.descendant col.1).center - (Q₁.descendant row.1).center) +
    inner ℝ w₂ ((Q₂.descendant col.2).center - (Q₂.descendant row.2).center)| ≤ τ

theorem retainedDyadicEdge_symm {d : ℕ} (Q₁ Q₂ : DyadicCube d) (w₁ w₂ : Space d) (τ : ℝ)
    (row col : List (Fin d → Bool) × List (Fin d → Bool)) :
    retainedDyadicEdge Q₁ Q₂ w₁ w₂ τ row col ↔ retainedDyadicEdge Q₁ Q₂ w₁ w₂ τ col row := by
  have hn (x y : Space d) : x-y = -(y-x) := by abel
  simp only [retainedDyadicEdge, hn (Q₁.descendant row.1).center,
    hn (Q₂.descendant row.2).center, perpendicularPart_neg, norm_neg,
    inner_neg_right, ← neg_add, abs_neg]

theorem retainedDyadicEdge_iff_grid {d n : ℕ} (Q₁ Q₂ : DyadicCube d)
    (hside : Q₂.side = Q₁.side) (w₁ w₂ : Space d) (τ : ℝ)
    (row col : List (Fin d → Bool) × List (Fin d → Bool))
    (hr₁ : row.1.length = n) (hr₂ : row.2.length = n)
    (hc₁ : col.1.length = n) (hc₂ : col.2.length = n) :
    retainedDyadicEdge Q₁ Q₂ w₁ w₂ τ row col ↔
      retainedGridEdge ((2 : ℝ)^n/Q₁.side) w₁ w₂ τ
        (dyadicCode row.1, dyadicCode row.2) (dyadicCode col.1, dyadicCode col.2) := by
  unfold retainedDyadicEdge retainedGridEdge
  rw [Q₁.center_sub_eq_grid_sub col.1 row.1 hc₁ hr₁,
    Q₂.center_sub_eq_grid_sub col.2 row.2 hc₂ hr₂, hside]

private theorem dyadic_candidate_grid_bound {d n C : ℕ} (Q : DyadicCube d)
    (A : Finset (List (Fin d → Bool))) (hA : ∀ p ∈ A, p.length = n)
    (w : Space d) (τ : ℝ) (a : List (Fin d → Bool)) (ha : a.length = n)
    (hb : (A.filter (fun p => ‖perpendicularPart w
      ((Q.descendant p).center - (Q.descendant a).center)‖ ≤ τ)).card ≤ C) :
    ((A.image dyadicCode).filter (fun z => ‖perpendicularPart w
      (scaledGridPoint ((2 : ℝ)^n/Q.side) z -
        scaledGridPoint ((2 : ℝ)^n/Q.side) (dyadicCode a))‖ ≤ τ)).card ≤ C := by
  classical
  rw [Finset.filter_image]
  apply Finset.card_image_le.trans
  have heq : A.filter (fun p => ‖perpendicularPart w
      (scaledGridPoint ((2 : ℝ)^n/Q.side) (dyadicCode p) -
        scaledGridPoint ((2 : ℝ)^n/Q.side) (dyadicCode a))‖ ≤ τ) =
      A.filter (fun p => ‖perpendicularPart w
        ((Q.descendant p).center - (Q.descendant a).center)‖ ≤ τ) := by
    apply Finset.filter_congr
    intro p hp
    rw [Q.center_sub_eq_grid_sub p a (hA p hp) ha]
  rwa [heq]

theorem retainedDyadic_degree {d n L C₁ C₂ : ℕ} (Q₁ Q₂ : DyadicCube d)
    (hQ : 0 < Q₁.side) (hside : Q₂.side = Q₁.side)
    (A B : Finset (List (Fin d → Bool)))
    (hA : ∀ p ∈ A, p.length = n) (hB : ∀ p ∈ B, p.length = n)
    (w₁ w₂ : Space d) (hw₁ : ‖w₁‖ = 1) (hw₂ : ‖w₂‖ = 1) (τ : ℝ)
    (hL : 4*τ*((2 : ℝ)^n/Q₁.side) ≤ L)
    (row : List (Fin d → Bool) × List (Fin d → Bool)) (hr : row ∈ A ×ˢ B)
    (h₁ : (A.filter (fun p => ‖perpendicularPart w₁
      ((Q₁.descendant p).center - (Q₁.descendant row.1).center)‖ ≤ τ)).card ≤ C₁)
    (h₂ : (B.filter (fun p => ‖perpendicularPart w₂
      ((Q₂.descendant p).center - (Q₂.descendant row.2).center)‖ ≤ τ)).card ≤ C₂) :
    ((A ×ˢ B).filter (retainedDyadicEdge Q₁ Q₂ w₁ w₂ τ row)).card ≤
      (2*L+1)^d * min C₁ C₂ := by
  classical
  let s := (2 : ℝ)^n/Q₁.side
  let code := fun a : List (Fin d → Bool) × List (Fin d → Bool) =>
    (dyadicCode a.1, dyadicCode a.2)
  have hrA := (Finset.mem_product.mp hr).1
  have hrB := (Finset.mem_product.mp hr).2
  have hc₁ := dyadic_candidate_grid_bound Q₁ A hA w₁ τ row.1 (hA _ hrA) h₁
  have hc₂ := dyadic_candidate_grid_bound Q₂ B hB w₂ τ row.2 (hB _ hrB) h₂
  rw [hside] at hc₂
  have hgrid := retainedGrid_degree_min (show 0 < s by dsimp [s]; positivity) hL
    (A.image dyadicCode) (B.image dyadicCode) w₁ w₂ hw₁ hw₂ (code row) hc₁ hc₂
  apply le_trans _ hgrid
  apply Finset.card_le_card_of_injOn code
  · intro col hcol
    obtain ⟨hcol, hedge⟩ := Finset.mem_filter.mp hcol
    obtain ⟨ha, hb⟩ := Finset.mem_product.mp hcol
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨Finset.mem_image.mpr ⟨col.1,ha,rfl⟩,
      Finset.mem_image.mpr ⟨col.2,hb,rfl⟩⟩, ?_⟩
    exact (retainedDyadicEdge_iff_grid Q₁ Q₂ hside w₁ w₂ τ row col
      (hA _ hrA) (hB _ hrB) (hA _ ha) (hB _ hb)).mp hedge
  · intro col hcol col' hcol' heq
    obtain ⟨ha,hb⟩ := Finset.mem_product.mp (Finset.mem_filter.mp hcol).1
    obtain ⟨ha',hb'⟩ := Finset.mem_product.mp (Finset.mem_filter.mp hcol').1
    exact Prod.ext
      (dyadicCode_injective_at_depth (hA _ ha) (hA _ ha') (congrArg Prod.fst heq))
      (dyadicCode_injective_at_depth (hB _ hb) (hB _ hb') (congrArg Prod.snd heq))

theorem retainedDyadic_schur {d n L C₁ C₂ : ℕ} (Q₁ Q₂ : DyadicCube d)
    (hQ : 0 < Q₁.side) (hside : Q₂.side = Q₁.side)
    (A B : Finset (List (Fin d → Bool)))
    (hA : ∀ p ∈ A, p.length = n) (hB : ∀ p ∈ B, p.length = n)
    (w₁ w₂ : Space d) (hw₁ : ‖w₁‖ = 1) (hw₂ : ‖w₂‖ = 1) (τ : ℝ)
    (hL : 4*τ*((2 : ℝ)^n/Q₁.side) ≤ L)
    (h₁ : ∀ a ∈ A, (A.filter (fun p => ‖perpendicularPart w₁
      ((Q₁.descendant p).center - (Q₁.descendant a).center)‖ ≤ τ)).card ≤ C₁)
    (h₂ : ∀ a ∈ B, (B.filter (fun p => ‖perpendicularPart w₂
      ((Q₂.descendant p).center - (Q₂.descendant a).center)‖ ≤ τ)).card ≤ C₂)
    (F : List (Fin d → Bool) × List (Fin d → Bool) → ℂ) :
    (∑ row ∈ A ×ˢ B, ∑ col ∈ A ×ˢ B,
      if retainedDyadicEdge Q₁ Q₂ w₁ w₂ τ row col then ‖F row * star (F col)‖ else 0) ≤
      ((2*L+1)^d * min C₁ C₂ : ℕ) * ∑ row ∈ A ×ˢ B, ‖F row‖^2 := by
  apply finite_graph_schur
  · intro row hr
    exact_mod_cast retainedDyadic_degree Q₁ Q₂ hQ hside A B hA hB w₁ w₂ hw₁ hw₂ τ hL
      row hr (h₁ _ (Finset.mem_product.mp hr).1) (h₂ _ (Finset.mem_product.mp hr).2)
  · intro col hc
    have hh := retainedDyadic_degree Q₁ Q₂ hQ hside A B hA hB w₁ w₂ hw₁ hw₂ τ hL
      col hc (h₁ _ (Finset.mem_product.mp hc).1) (h₂ _ (Finset.mem_product.mp hc).2)
    have he : (A ×ˢ B).filter (fun row => retainedDyadicEdge Q₁ Q₂ w₁ w₂ τ row col) =
        (A ×ˢ B).filter (retainedDyadicEdge Q₁ Q₂ w₁ w₂ τ col) := by
      apply Finset.filter_congr
      intro row _
      exact retainedDyadicEdge_symm Q₁ Q₂ w₁ w₂ τ row col
    rw [he]
    exact_mod_cast hh

end Falconer

end OAI
