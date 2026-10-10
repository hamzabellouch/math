import OAI.MeasureTheory.Falconer.Angular.AngularNearNeighbors

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory

theorem dyadic_far_points (Q : DyadicSquare) (hQ : Q.side = 1)
    (p : ℕ) (P P' : CellPath) (hP : P.length = p) (hP' : P'.length = p)
    (hfar : 20/(2:ℝ)^p < dist (Q.descendant P).center (Q.descendant P').center)
    (x x' : Plane) (hx : x ∈ (Q.descendant P).carrier) (hx' : x' ∈ (Q.descendant P').carrier) :
    16/(2:ℝ)^p < dist x x' := by
  have hQpos : 0 < Q.side := by rw [hQ]; norm_num
  have h1 := (Q.descendant P).dist_le (Q.descendant_side_pos hQpos P).le
    ((Q.descendant P).center_mem (Q.descendant_side_pos hQpos P)) hx
  have h2 := (Q.descendant P').dist_le (Q.descendant_side_pos hQpos P').le hx'
    ((Q.descendant P').center_mem (Q.descendant_side_pos hQpos P'))
  rw [Q.descendant_side,hP,hQ,mul_one_div] at h1
  rw [Q.descendant_side,hP',hQ,mul_one_div] at h2
  have ht := (dist_triangle (Q.descendant P).center x (Q.descendant P').center).trans
    (add_le_add (le_refl _) (dist_triangle x x' (Q.descendant P').center))
  have he : 20/(2:ℝ)^p = 16/(2:ℝ)^p+2/(2:ℝ)^p+2/(2:ℝ)^p := by ring
  rw [he] at hfar
  linarith

theorem angular_far_displacement (Q₁ Q₂ : DyadicSquare)
    (hQ₁ : Q₁.side = 1) (hQ₂ : Q₂.side = 1) (p : ℕ) (row col : CellPath × CellPath)
    (hr : row ∈ (dyadicPaths p) ×ˢ (dyadicPaths p))
    (hc : col ∈ (dyadicPaths p) ×ˢ (dyadicPaths p))
    (hfar : ¬ angularNear Q₁ Q₂ p row col)
    (x x' y y' : Plane) (hx : x ∈ (Q₁.descendant row.1).carrier)
    (hx' : x' ∈ (Q₁.descendant col.1).carrier) (hy : y ∈ (Q₂.descendant row.2).carrier)
    (hy' : y' ∈ (Q₂.descendant col.2).carrier) :
    16/(2:ℝ)^p < dist x x' ∨ 16/(2:ℝ)^p < dist y y' := by
  simp only [Finset.mem_product,mem_dyadicPaths] at hr hc
  unfold angularNear at hfar
  by_cases h1 : dist (Q₁.descendant row.1).center (Q₁.descendant col.1).center ≤ 20/(2:ℝ)^p
  · exact Or.inr (dyadic_far_points Q₂ hQ₂ p row.2 col.2 hr.2 hc.2
      (lt_of_not_ge (fun h2 => hfar ⟨h1,h2⟩)) y y' hy hy')
  · exact Or.inl (dyadic_far_points Q₁ hQ₁ p row.1 col.1 hr.1 hc.1 (lt_of_not_ge h1) x x' hx hx')

end PlanarFalconer

end OAI
