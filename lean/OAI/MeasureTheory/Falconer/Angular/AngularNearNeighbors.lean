import OAI.MeasureTheory.Falconer.Geometry.ScaledDyadicPacking
import OAI.MeasureTheory.Falconer.Estimates.ProductOccupiedVertices

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory
attribute [local instance] Classical.propDecidable

def angularNear (Q₁ Q₂ : DyadicSquare) (p : ℕ)
    (row col : CellPath × CellPath) : Prop :=
  dist (Q₁.descendant row.1).center (Q₁.descendant col.1).center ≤ 20/(2:ℝ)^p ∧
  dist (Q₂.descendant row.2).center (Q₂.descendant col.2).center ≤ 20/(2:ℝ)^p

theorem angularNear_symm (Q₁ Q₂ : DyadicSquare) (p : ℕ) (row col : CellPath × CellPath) :
    angularNear Q₁ Q₂ p row col ↔ angularNear Q₁ Q₂ p col row := by
  simp only [angularNear,dist_comm]

theorem dyadic_twenty_neighbors (Q : DyadicSquare) (hQ : Q.side = 1)
    (p : ℕ) (x : Plane) :
    (((dyadicPaths p).filter (fun c => dist x (Q.descendant c).center ≤ 20/(2:ℝ)^p)).card : ℝ) ≤ 1936 := by
  classical
  have hpos : 0 < Q.side := by rw [hQ]; norm_num
  have hsub : (dyadicPaths p).filter (fun c => dist x (Q.descendant c).center ≤ 20/(2:ℝ)^p) ⊆
      cellsMeeting Q p x (21/(2:ℝ)^p) := by
    intro c hc
    obtain ⟨hc,hb⟩ := Finset.mem_filter.mp hc
    refine Finset.mem_filter.mpr ⟨hc,(Q.descendant c).center,
      (Q.descendant c).center_mem (Q.descendant_side_pos hpos c),?_⟩
    rw [mem_ball,dist_comm]
    exact hb.trans_lt (div_lt_div_of_pos_right (by norm_num) (by positivity))
  have hh := dyadic_scaled_ball_card_le Q hpos p x (C₀ := 21) (by norm_num)
    (r := 21/(2:ℝ)^p) (by rw [hQ]; ring_nf; exact le_rfl)
  norm_num at hh
  exact (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans (by exact_mod_cast hh)

theorem angularNear_degree (Q₁ Q₂ : DyadicSquare) (hQ₁ : Q₁.side = 1) (hQ₂ : Q₂.side = 1)
    (p : ℕ) (C : Finset (CellPath × CellPath))
    (hC : C ⊆ (dyadicPaths p) ×ˢ (dyadicPaths p)) (row : CellPath × CellPath) :
    ((C.filter (angularNear Q₁ Q₂ p row)).card : ℝ) ≤ 3748096 := by
  classical
  let S₁ := (dyadicPaths p).filter (fun c =>
    dist (Q₁.descendant row.1).center (Q₁.descendant c).center ≤ 20/(2:ℝ)^p)
  let S₂ := (dyadicPaths p).filter (fun c =>
    dist (Q₂.descendant row.2).center (Q₂.descendant c).center ≤ 20/(2:ℝ)^p)
  have hsub : C.filter (angularNear Q₁ Q₂ p row) ⊆ S₁ ×ˢ S₂ := by
    intro col hc
    obtain ⟨hc,hnear⟩ := Finset.mem_filter.mp hc
    obtain ⟨h1,h2⟩ := Finset.mem_product.mp (hC hc)
    exact Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨h1,hnear.1⟩,
      Finset.mem_filter.mpr ⟨h2,hnear.2⟩⟩
  have h1 := dyadic_twenty_neighbors Q₁ hQ₁ p (Q₁.descendant row.1).center
  have h2 := dyadic_twenty_neighbors Q₂ hQ₂ p (Q₂.descendant row.2).center
  have hh := Nat.cast_le (α := ℝ).mpr (Finset.card_le_card hsub)
  rw [Finset.card_product,Nat.cast_mul] at hh
  exact hh.trans (by nlinarith [mul_le_mul h1 h2 (Nat.cast_nonneg S₂.card) (by norm_num : (0:ℝ) ≤ 1936)])

end PlanarFalconer

end OAI
