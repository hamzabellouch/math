import OAI.MeasureTheory.Falconer.Angular.AngularMeanAssembly

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory
open scoped ENNReal

theorem stripHitBound_quarterTurn (W : ℝ) (z : Plane) :
    stripHitBound W (quarterTurn z) = stripHitBound W z := by
  have hz : quarterTurn z = 0 ↔ z = 0 := by
    rw [← norm_eq_zero, norm_quarterTurn,norm_eq_zero]
  simp only [stripHitBound,hz,norm_quarterTurn]

theorem projection_center_mem (Q : DyadicSquare) (hQ : 0 < Q.side)
    (ρ : Measure Plane) (p u : ℕ) (P : CellPath) {c : CellPath}
    (hc : c ∈ projectionTestCells Q ρ p u P) :
    (Q.descendant c).center ∈ (Q.descendant P).carrier := by
  rw [← (Finset.mem_filter.mp hc).2.2]
  exact Q.descendant_subset_take hQ c p
    ((Q.descendant c).center_mem (Q.descendant_side_pos hQ c))

theorem projection_cells_subset_parallel (Q : DyadicSquare) (hQ : Q.side = 1)
    (ρ : Measure Plane) (p u : ℕ) {P : CellPath} (hP : P.length = p)
    {a : CellPath} (ha : a ∈ projectionTestCells Q ρ p u P) :
    projectionTestCells Q ρ p u P ⊆ parallelTestCells Q ρ p u a := by
  classical
  have hside : 0 < Q.side := by rw [hQ]; norm_num
  intro c hc
  refine Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hc).1,(Finset.mem_filter.mp hc).2.1,?_⟩
  have hd := (Q.descendant P).dist_le (Q.descendant_side_pos hside P).le
    (projection_center_mem Q hside ρ p u P hc) (projection_center_mem Q hside ρ p u P ha)
  rw [Q.descendant_side,hP,hQ] at hd
  change dist (Q.descendant c).center (Q.descendant a).center < _
  exact hd.trans_lt (by
    rw [mul_one_div]
    exact div_lt_div_of_pos_right (by norm_num) (by positivity))

theorem projection_cells_subset_ball (Q : DyadicSquare) (hQ : Q.side = 1)
    (ρ : Measure Plane) (p u : ℕ) {P : CellPath} (hP : P.length = p) :
    projectionTestCells Q ρ p u P ⊆
      occupiedCenterCells Q ρ u (Q.descendant P).center (3/(2:ℝ)^p) := by
  classical
  have hside : 0 < Q.side := by rw [hQ]; norm_num
  intro c hc
  refine Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hc).1,(Finset.mem_filter.mp hc).2.1,?_⟩
  have hd := (Q.descendant P).dist_le (Q.descendant_side_pos hside P).le
    (projection_center_mem Q hside ρ p u P hc)
    ((Q.descendant P).center_mem (Q.descendant_side_pos hside P))
  rw [Q.descendant_side,hP,hQ] at hd
  change dist (Q.descendant c).center (Q.descendant P).center < _
  exact hd.trans_lt (by
    rw [mul_one_div]
    exact div_lt_div_of_pos_right (by norm_num) (by positivity))

theorem projection_strip_sum_rows (Q : DyadicSquare) (hQ : Q.side = 1)
    (ρ : Measure Plane) (p u : ℕ) {P : CellPath} (hP : P.length = p) (W : ℝ) :
    ∑ cc ∈ (projectionTestCells Q ρ p u P).product (projectionTestCells Q ρ p u P),
      stripHitBound W ((Q.descendant cc.1).center-(Q.descendant cc.2).center) ≤
    ∑ a ∈ projectionTestCells Q ρ p u P,
      ∑ c ∈ parallelTestCells Q ρ p u a,
        stripHitBound W (quarterTurn ((Q.descendant c).center-(Q.descendant a).center)) := by
  classical
  change (∑ cc ∈ (projectionTestCells Q ρ p u P) ×ˢ (projectionTestCells Q ρ p u P),
    stripHitBound W ((Q.descendant cc.1).center-(Q.descendant cc.2).center)) ≤ _
  rw [Finset.sum_product]
  apply Finset.sum_le_sum
  intro a ha
  have he (c : CellPath) :
      stripHitBound W ((Q.descendant a).center-(Q.descendant c).center) =
      stripHitBound W (quarterTurn ((Q.descendant c).center-(Q.descendant a).center)) := by
    rw [stripHitBound_quarterTurn]
    simp only [stripHitBound,sub_eq_zero,norm_sub_rev]
    simp only [eq_comm]
  simp_rw [he]
  exact Finset.sum_le_sum_of_subset (projection_cells_subset_parallel Q hQ ρ p u hP ha)

end PlanarFalconer

end OAI
