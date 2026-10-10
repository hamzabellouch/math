import OAI.MeasureTheory.Falconer.Radial.ProjectionCellPartition

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal

theorem projection_center_replacement (Q : DyadicSquare) (hQ : 0 < Q.side)
    {u : ℕ} {C D : CellPath} (hC : C.length = u) (hD : D.length = u)
    {x y ω : Plane} (hx : x ∈ (Q.descendant C).carrier)
    (hy : y ∈ (Q.descendant D).carrier) (hω : ‖ω‖ ≤ 1) :
    |planeDot ((Q.descendant C).center-(Q.descendant D).center) ω| ≤
      |planeDot (x-y) ω|+4*Q.side/(2:ℝ)^u := by
  have he : planeDot ((Q.descendant C).center-(Q.descendant D).center) ω =
      planeDot (x-y) ω +
      planeDot (((Q.descendant C).center-x)-((Q.descendant D).center-y)) ω := by
    simp [planeDot]; ring
  have hc := (Q.descendant C).dist_le (Q.descendant_side_pos hQ C).le
    ((Q.descendant C).center_mem (Q.descendant_side_pos hQ C)) hx
  have hd := (Q.descendant D).dist_le (Q.descendant_side_pos hQ D).le
    ((Q.descendant D).center_mem (Q.descendant_side_pos hQ D)) hy
  rw [dist_eq_norm,Q.descendant_side,hC] at hc
  rw [dist_eq_norm,Q.descendant_side,hD] at hd
  have hnorm : ‖((Q.descendant C).center-x)-((Q.descendant D).center-y)‖ ≤
      4*Q.side/(2:ℝ)^u := by
    exact (norm_sub_le _ _).trans ((add_le_add hc hd).trans_eq (by ring))
  rw [he]
  apply (abs_add_le _ _).trans
  apply add_le_add le_rfl
  exact (planeDot_abs_le _ _).trans
    ((mul_le_mul_of_nonneg_left hω (norm_nonneg _)).trans (by simpa using hnorm))

theorem projection_collision_le_count (Q : DyadicSquare) (hQ : 0 < Q.side)
    (ρ : Measure Plane) [IsFiniteMeasure ρ] {p u : ℕ} (hpu : p ≤ u)
    {P : CellPath} (hP : P.length = p) {ω : Plane} (hω : ‖ω‖ ≤ 1)
    (w : ℝ) {H : ℝ≥0∞}
    (hm : ∀ C ∈ projectionTestCells Q ρ p u P, ρ (Q.descendant C).carrier ≤ H) :
    ((ρ.restrict (Q.descendant P).carrier).prod (ρ.restrict (Q.descendant P).carrier))
      {z : Plane × Plane | |planeDot (z.1-z.2) ω| ≤ w} ≤
      (projectionTestCount Q ρ p u P (w+4*Q.side/(2:ℝ)^u) ω : ℝ≥0∞)*H^2 := by
  classical
  let S := projectionTestCells Q ρ p u P
  let T := (S.product S).filter fun cc =>
    |planeDot ((Q.descendant cc.1).center-(Q.descendant cc.2).center) ω| ≤
      w+4*Q.side/(2:ℝ)^u
  let μ := ρ.restrict (Q.descendant P).carrier
  have hcover : ∀ᵐ z ∂μ.prod μ,
      |planeDot (z.1-z.2) ω| ≤ w →
        z ∈ ⋃ cc ∈ T, (Q.descendant cc.1).carrier ×ˢ (Q.descendant cc.2).carrier := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae (ae_projection_cell Q hQ ρ hpu hP),
      Measure.quasiMeasurePreserving_snd.ae (ae_projection_cell Q hQ ρ hpu hP)] with z hx hy
    intro hz
    obtain ⟨C,hC,hx⟩ := hx
    obtain ⟨D,hD,hy⟩ := hy
    refine mem_iUnion₂.mpr ⟨(C,D),?_,hx,hy⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨hC,hD⟩,?_⟩
    exact (projection_center_replacement Q hQ
      ((mem_dyadicPaths _ _).mp (Finset.mem_filter.mp hC).1)
      ((mem_dyadicPaths _ _).mp (Finset.mem_filter.mp hD).1) hx hy hω).trans
      (add_le_add hz le_rfl)
  calc
    _ ≤ (μ.prod μ) (⋃ cc ∈ T, (Q.descendant cc.1).carrier ×ˢ (Q.descendant cc.2).carrier) :=
      measure_mono_ae hcover
    _ ≤ ∑ cc ∈ T, (μ.prod μ) ((Q.descendant cc.1).carrier ×ˢ (Q.descendant cc.2).carrier) :=
      measure_biUnion_finset_le _ _
    _ ≤ ∑ _cc ∈ T, H^2 := by
      apply Finset.sum_le_sum
      intro cc hcc
      have hc := Finset.mem_product.mp (Finset.mem_filter.mp hcc).1
      rw [Measure.prod_prod]
      exact (mul_le_mul' (Measure.restrict_apply_le _ _) (Measure.restrict_apply_le _ _)).trans
        (by simpa only [pow_two] using mul_le_mul' (hm _ hc.1) (hm _ hc.2))
    _ = _ := by simp [projectionTestCount,stripCount,T,S]

end PlanarFalconer

end OAI
