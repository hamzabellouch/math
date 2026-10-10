import OAI.MeasureTheory.Falconer.Angular.AngularFarDepth

namespace OAI

namespace PlanarFalconer
open Set Metric

 theorem comparable_cells_strong_separation (P Q : DyadicSquare)
    (hP : 0 < P.side) (hQ : 0 < Q.side) {l : ℝ} (hl : 0 < l)
    (hsP : P.side ≤ l) (hsQ : Q.side ≤ l) {x y : Plane}
    (hx : x ∈ P.carrier) (hy : y ∈ Q.carrier)
    (hlo : 256*l < dist x y) (hhi : dist x y ≤ 1024*l) :
    100*l ≤ dist P.center Q.center ∧ dist P.center Q.center ≤ 2000*l := by
  have hpx := (P.dist_le hP.le (P.center_mem hP) hx).trans (mul_le_mul_of_nonneg_left hsP (by norm_num))
  have hqy := (Q.dist_le hQ.le hy (Q.center_mem hQ)).trans (mul_le_mul_of_nonneg_left hsQ (by norm_num))
  have ht₁ := (dist_triangle P.center x Q.center).trans
    (add_le_add (le_refl _) (dist_triangle x y Q.center))
  have ht₂ := (dist_triangle x P.center y).trans
    (add_le_add (le_refl _) (dist_triangle P.center Q.center y))
  rw [dist_comm x P.center,dist_comm Q.center y] at ht₂
  constructor <;> linarith

 theorem comparable_dyadic_cells_strong_separation (Q₁ Q₂ : DyadicSquare)
    (hQ₁ : Q₁.side = 1) (hQ₂ : Q₂.side = 1) (b : ℕ) (P Q : CellPath)
    (hP : P.length = b) (hQ : Q.length = b) {x y : Plane}
    (hx : x ∈ (Q₁.descendant P).carrier) (hy : y ∈ (Q₂.descendant Q).carrier)
    (hlo : 256*(2:ℝ)^(-(b:ℝ)) < dist x y) (hhi : dist x y ≤ 1024*(2:ℝ)^(-(b:ℝ))) :
    100*(2:ℝ)^(-(b:ℝ)) ≤ dist (Q₁.descendant P).center (Q₂.descendant Q).center ∧
      dist (Q₁.descendant P).center (Q₂.descendant Q).center ≤ 2000*(2:ℝ)^(-(b:ℝ)) := by
  have hp : 0 < Q₁.side := by rw [hQ₁]; norm_num
  have hq : 0 < Q₂.side := by rw [hQ₂]; norm_num
  apply comparable_cells_strong_separation (Q₁.descendant P) (Q₂.descendant Q)
    (Q₁.descendant_side_pos hp P) (Q₂.descendant_side_pos hq Q) (by positivity) _ _ hx hy hlo hhi
  · rw [Q₁.descendant_side,hP,hQ₁,Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),Real.rpow_natCast]
    simp
  · rw [Q₂.descendant_side,hQ,hQ₂,Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),Real.rpow_natCast]
    simp

end PlanarFalconer

end OAI
