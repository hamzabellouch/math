import OAI.MeasureTheory.Falconer.Estimates.FourPointPartition
import OAI.MeasureTheory.Falconer.Geometry.FarCellGeometry

namespace OAI

/-! # Far-label elimination under a positive original-law bound -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
attribute [local instance] Classical.propDecidable

def farDisplacementRegion (d a h : ℕ) :
    Set ((Space d × Space d) × (Space d × Space d)) :=
  {z | max (dist z.1.1 z.1.2) (dist z.2.1 z.2.2) ≤
      2*((d:ℝ)+1)*(2:ℝ)^(-(a:ℝ)) ∧
    8*((d:ℝ)+1)*(2:ℝ)^(-(h:ℝ)) < max (dist z.1.1 z.1.2) (dist z.2.1 z.2.2)}

theorem farDisplacementRegion_measurable (d a h : ℕ) :
    MeasurableSet (farDisplacementRegion d a h) := by
  have hm : Measurable (fun z : (Space d × Space d) × (Space d × Space d) =>
      max (dist z.1.1 z.1.2) (dist z.2.1 z.2.2)) := by fun_prop
  exact (measurableSet_le hm measurable_const).inter
    (measurableSet_lt measurable_const hm)

theorem sum_pair_reassociate {α β M : Type*} [AddCommMonoid M]
    (A : Finset α) (B : Finset β) (F : (α × α) → (β × β) → M) :
    (∑ row ∈ A ×ˢ B, ∑ col ∈ A ×ˢ B, F (row.1,col.1) (row.2,col.2)) =
      ∑ u ∈ A ×ˢ A, ∑ v ∈ B ×ˢ B, F u v := by
  simp only [Finset.sum_product]
  apply Finset.sum_congr rfl
  intro a _
  exact Finset.sum_comm

 theorem originalFourPoint_lintegral_rows {d : ℕ} (P Q : DyadicCube d)
    (μ ν : Measure (Space d)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (n : ℕ) (U : Set ((Space d × Space d) × (Space d × Space d)))
    (F : ((Space d × Space d) × (Space d × Space d)) → ℝ≥0∞) :
    (∑ row ∈ P.occupiedPaths μ n ×ˢ Q.occupiedPaths ν n,
      ∑ col ∈ P.occupiedPaths μ n ×ˢ Q.occupiedPaths ν n,
        ∫⁻ z in U, F z ∂fourPointChildMeasure P Q μ ν (row.1,col.1) (row.2,col.2)) =
      ∫⁻ z in U, F z ∂originalFourPointMeasure P Q μ ν := by
  rw [sum_pair_reassociate (P.occupiedPaths μ n) (Q.occupiedPaths ν n)
    (fun u v => ∫⁻ z in U, F z ∂fourPointChildMeasure P Q μ ν u v),
    originalFourPointMeasure_partition P Q μ ν n]
  simp only [PlanarFalconer.finite_measure_restrict_sum,lintegral_finsetSum_measure]

 theorem fourPointChildMeasure_far_support {d a h : ℕ}
    (Q : DyadicCube d) (hQ : Q.side = 1) (ρ : Measure (Space d)) [IsFiniteMeasure ρ]
    (hah : a ≤ h) (X Y : List (Fin d → Bool)) (hX : X.length = a) (hY : Y.length = a)
    (row col : List (Fin d → Bool) × List (Fin d → Bool))
    (hrow : row ∈ (Q.descendant X).occupiedPaths ρ (h-a) ×ˢ (Q.descendant Y).occupiedPaths ρ (h-a))
    (hcol : col ∈ (Q.descendant X).occupiedPaths ρ (h-a) ×ˢ (Q.descendant Y).occupiedPaths ρ (h-a))
    (hfar : ¬nearDyadicEdge (Q.descendant X) (Q.descendant Y)
      (10*((d:ℝ)+1)/(2:ℝ)^h) row col) :
    ∀ᵐ z ∂fourPointChildMeasure (Q.descendant X) (Q.descendant Y) ρ ρ
      (row.1,col.1) (row.2,col.2), z ∈ farDisplacementRegion d a h := by
  have hQpos : 0 < Q.side := by rw [hQ]; norm_num
  have hside (Z : List (Fin d → Bool)) (hZ : Z.length = a) :
      (Q.descendant Z).side = (2:ℝ)^(-(a:ℝ)) := by
    rw [Q.descendant_side,hQ,hZ,Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),
      Real.rpow_natCast,one_div]
  have hchild (Z : List (Fin d → Bool)) (hZ : Z.length = a)
      (p : List (Fin d → Bool)) (hp : p ∈ (Q.descendant Z).occupiedPaths ρ (h-a)) :
      ((Q.descendant Z).descendant p).side = (2:ℝ)^(-(h:ℝ)) := by
    rw [(Q.descendant Z).descendant_side,
      (mem_cubePaths _ _ _).mp (Finset.mem_filter.mp hp).1,
      Q.descendant_side,hQ,hZ,div_div,← pow_add,Nat.add_sub_of_le hah,
      Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),Real.rpow_natCast,one_div]
  obtain ⟨hr₁,hr₂⟩ := Finset.mem_product.mp hrow
  obtain ⟨hc₁,hc₂⟩ := Finset.mem_product.mp hcol
  unfold fourPointChildMeasure
  rw [Measure.prod_restrict,Measure.prod_restrict,Measure.prod_restrict]
  filter_upwards [ae_restrict_mem
    ((((Q.descendant X).descendant row.1).measurable.prod
      ((Q.descendant X).descendant col.1).measurable).prod
      (((Q.descendant Y).descendant row.2).measurable.prod
        ((Q.descendant Y).descendant col.2).measurable))] with z hz
  have hu (Z : List (Fin d → Bool)) (hZ : Z.length = a)
      (p q : List (Fin d → Bool)) (x y : Space d)
      (hx : x ∈ ((Q.descendant Z).descendant p).carrier)
      (hy : y ∈ ((Q.descendant Z).descendant q).carrier) :
      dist x y ≤ 2*((d:ℝ)+1)*(2:ℝ)^(-(a:ℝ)) := by
    have h := (Q.descendant Z).dist_le (Q.descendant_side_pos hQpos Z).le
      ((Q.descendant Z).descendant_subset p hx) ((Q.descendant Z).descendant_subset q hy)
    rw [hside Z hZ] at h
    have h' := mul_le_mul_of_nonneg_right (sqrt_dimension_le d)
      (Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 2) (-(a:ℝ)))
    have hd : 0 ≤ ((d:ℝ)+1)*(2:ℝ)^(-(a:ℝ)) := by positivity
    linarith
  refine ⟨max_le (hu X hX row.1 col.1 _ _ hz.1.1 hz.1.2)
    (hu Y hY row.2 col.2 _ _ hz.2.1 hz.2.2),?_⟩
  have hτ : 10*((d:ℝ)+1)/(2:ℝ)^h = 10*((d:ℝ)+1)*(2:ℝ)^(-(h:ℝ)) := by
    rw [Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),Real.rpow_natCast,div_eq_mul_inv]
  have hnot : ¬(dist ((Q.descendant X).descendant row.1).center
        ((Q.descendant X).descendant col.1).center ≤ 10*((d:ℝ)+1)*(2:ℝ)^(-(h:ℝ)) ∧
      dist ((Q.descendant Y).descendant row.2).center
        ((Q.descendant Y).descendant col.2).center ≤ 10*((d:ℝ)+1)*(2:ℝ)^(-(h:ℝ))) := by
    simpa only [nearDyadicEdge,hτ,dist_eq_norm,norm_sub_rev] using hfar
  by_cases hx : dist ((Q.descendant X).descendant row.1).center
      ((Q.descendant X).descendant col.1).center ≤ 10*((d:ℝ)+1)*(2:ℝ)^(-(h:ℝ))
  · have hy := lt_of_not_ge (fun hy => hnot ⟨hx,hy⟩)
    have hg := DyadicCube.far_centers_force_far_points _ _
      ((Q.descendant Y).descendant_side_pos (Q.descendant_side_pos hQpos Y) row.2)
      ((Q.descendant Y).descendant_side_pos (Q.descendant_side_pos hQpos Y) col.2)
      (hchild Y hY row.2 hr₂).le (hchild Y hY col.2 hc₂).le hy hz.2.1 hz.2.2
    exact hg.trans_le (le_max_right _ _)
  · have hg := DyadicCube.far_centers_force_far_points _ _
      ((Q.descendant X).descendant_side_pos (Q.descendant_side_pos hQpos X) row.1)
      ((Q.descendant X).descendant_side_pos (Q.descendant_side_pos hQpos X) col.1)
      (hchild X hX row.1 hr₁).le (hchild X hX col.1 hc₁).le (lt_of_not_ge hx) hz.1.1 hz.1.2
    exact hg.trans_le (le_max_left _ _)

 theorem originalFourPoint_far_rows_le {d a h : ℕ}
    (Q : DyadicCube d) (hQ : Q.side = 1) (ρ : Measure (Space d)) [IsFiniteMeasure ρ]
    (hah : a ≤ h) (X Y : List (Fin d → Bool)) (hX : X.length = a) (hY : Y.length = a)
    (F : ((Space d × Space d) × (Space d × Space d)) → ℝ≥0∞) :
    (∑ row ∈ (Q.descendant X).occupiedPaths ρ (h-a) ×ˢ (Q.descendant Y).occupiedPaths ρ (h-a),
      ∑ col ∈ (Q.descendant X).occupiedPaths ρ (h-a) ×ˢ (Q.descendant Y).occupiedPaths ρ (h-a),
        if nearDyadicEdge (Q.descendant X) (Q.descendant Y) (10*((d:ℝ)+1)/(2:ℝ)^h) row col
        then 0 else ∫⁻ z, F z ∂fourPointChildMeasure (Q.descendant X) (Q.descendant Y)
          ρ ρ (row.1,col.1) (row.2,col.2)) ≤
      ∫⁻ z in farDisplacementRegion d a h, F z
        ∂originalFourPointMeasure (Q.descendant X) (Q.descendant Y) ρ ρ := by
  rw [← originalFourPoint_lintegral_rows (Q.descendant X) (Q.descendant Y) ρ ρ (h-a)]
  apply Finset.sum_le_sum
  intro row hr
  apply Finset.sum_le_sum
  intro col hc
  by_cases hf : nearDyadicEdge (Q.descendant X) (Q.descendant Y) (10*((d:ℝ)+1)/(2:ℝ)^h) row col
  · simp only [ite_eq_left hf]; exact bot_le
  · rw [ite_eq_right hf,Measure.restrict_eq_self_of_ae_mem
      (fourPointChildMeasure_far_support Q hQ ρ hah X Y hX hY row col hr hc hf)]

end Falconer

end OAI
