import OAI.MeasureTheory.Falconer.Estimates.ComparablePositiveRebin
import OAI.MeasureTheory.Falconer.Geometry.ScaledDyadicPacking

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory
attribute [local instance] Classical.propDecidable

theorem dyadic_two_thousand_neighbors (Q : DyadicSquare) (hQ : Q.side = 1)
    (p : ℕ) (x : Plane) :
    (((dyadicPaths p).filter (fun c => dist x (Q.descendant c).center ≤ 2000/(2:ℝ)^p)).card : ℝ) ≤ 16032016 := by
  classical
  have hpos : 0 < Q.side := by rw [hQ]; norm_num
  have hsub : (dyadicPaths p).filter (fun c => dist x (Q.descendant c).center ≤ 2000/(2:ℝ)^p) ⊆
      cellsMeeting Q p x (2001/(2:ℝ)^p) := by
    intro c hc
    obtain ⟨hc,hb⟩ := Finset.mem_filter.mp hc
    refine Finset.mem_filter.mpr ⟨hc,(Q.descendant c).center,
      (Q.descendant c).center_mem (Q.descendant_side_pos hpos c),?_⟩
    rw [mem_ball,dist_comm]
    exact hb.trans_lt (div_lt_div_of_pos_right (by norm_num) (by positivity))
  have hh := dyadic_scaled_ball_card_le Q hpos p x (C₀ := 2001) (by norm_num)
    (r := 2001/(2:ℝ)^p) (by rw [hQ]; ring_nf; exact le_rfl)
  norm_num at hh
  exact (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans (by exact_mod_cast hh)

theorem angularSeparated_degree_real (Q₁ Q₂ : DyadicSquare) (hQ₁ : Q₁.side = 1) (hQ₂ : Q₂.side = 1)
    (p : ℕ) (C : Finset (CellPath × CellPath))
    (hC : C ⊆ (dyadicPaths p) ×ˢ (dyadicPaths p)) (row : CellPath × CellPath) :
    ((C.filter (angularSeparated Q₁ Q₂ p row)).card : ℝ) ≤ 257025537024256 := by
  classical
  let S₁ := (dyadicPaths p).filter (fun c =>
    dist (Q₁.descendant row.1).center (Q₁.descendant c).center ≤ 2000/(2:ℝ)^p)
  let S₂ := (dyadicPaths p).filter (fun c =>
    dist (Q₂.descendant row.2).center (Q₂.descendant c).center ≤ 2000/(2:ℝ)^p)
  have hsub : C.filter (angularSeparated Q₁ Q₂ p row) ⊆ S₁ ×ˢ S₂ := by
    intro col hc
    obtain ⟨hc,hnear⟩ := Finset.mem_filter.mp hc
    simp only [angularSeparated,Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),Real.rpow_natCast,← div_eq_mul_inv] at hnear
    obtain ⟨h1,h2⟩ := Finset.mem_product.mp (hC hc)
    exact Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨h1,hnear.1.2⟩,
      Finset.mem_filter.mpr ⟨h2,hnear.2.2⟩⟩
  have h1 := dyadic_two_thousand_neighbors Q₁ hQ₁ p (Q₁.descendant row.1).center
  have h2 := dyadic_two_thousand_neighbors Q₂ hQ₂ p (Q₂.descendant row.2).center
  have hh := Nat.cast_le (α := ℝ).mpr (Finset.card_le_card hsub)
  rw [Finset.card_product,Nat.cast_mul] at hh
  exact hh.trans (by nlinarith [mul_le_mul h1 h2 (Nat.cast_nonneg S₂.card) (by norm_num : (0:ℝ) ≤ 16032016)])

theorem angularSeparated_degree (Q₁ Q₂ : DyadicSquare) (hQ₁ : Q₁.side = 1) (hQ₂ : Q₂.side = 1)
    (p : ℕ) (C : Finset (CellPath × CellPath))
    (hC : C ⊆ (dyadicPaths p) ×ˢ (dyadicPaths p)) (row : CellPath × CellPath) :
    (C.filter (angularSeparated Q₁ Q₂ p row)).card ≤ 257025537024256 := by
  exact_mod_cast angularSeparated_degree_real Q₁ Q₂ hQ₁ hQ₂ p C hC row

end PlanarFalconer

end OAI
