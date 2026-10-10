import OAI.MeasureTheory.Falconer.Angular.AngularOccupiedFarPartition

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

instance angularFourCellMeasure_finite (Q₁ Q₂ : DyadicSquare) (ρ ν : Measure Plane)
    [IsFiniteMeasure ρ] [IsFiniteMeasure ν] (row col : CellPath × CellPath) :
    IsFiniteMeasure (angularFourCellMeasure Q₁ Q₂ ρ ν row col) := by
  let ρs : Fin 4 → Measure Plane := ![ρ,ρ,ν,ν]
  let : ∀ i, IsFiniteMeasure (ρs i) := by intro i; fin_cases i <;> dsimp [ρs] <;> infer_instance
  exact inferInstanceAs (IsFiniteMeasure (Measure.pi (fun i => (ρs i).restrict
    (![(Q₁.descendant row.1).carrier,(Q₁.descendant col.1).carrier,
       (Q₂.descendant row.2).carrier,(Q₂.descendant col.2).carrier] i))))

theorem angularFourCellMeasure_real (Q₁ Q₂ : DyadicSquare) (ρ ν : Measure Plane)
    [IsFiniteMeasure ρ] [IsFiniteMeasure ν] (row col : CellPath × CellPath) :
    (angularFourCellMeasure Q₁ Q₂ ρ ν row col).real univ =
      ((ρ (Q₁.descendant row.1).carrier).toReal*(ν (Q₂.descendant row.2).carrier).toReal)*
      ((ρ (Q₁.descendant col.1).carrier).toReal*(ν (Q₂.descendant col.2).carrier).toReal) := by
  let ρs : Fin 4 → Measure Plane := ![ρ,ρ,ν,ν]
  let : ∀ i, IsFiniteMeasure (ρs i) := by intro i; fin_cases i <;> dsimp [ρs] <;> infer_instance
  change (Measure.pi (fun i => (ρs i).restrict _)).real univ = _
  simp only [Measure.real,Measure.pi_univ,Measure.restrict_apply_univ,ENNReal.toReal_mul,
    Fin.prod_univ_four,ρs,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons]
  ring

theorem occupied_absolute_mass_sum (Q : DyadicSquare) (hQ : 0 < Q.side)
    (ρ : Measure Plane) [IsFiniteMeasure ρ] (A : CellPath) (n : ℕ) :
    (∑ P ∈ (occupiedAnchorPaths (Q.descendant A) ρ n).image (fun c => A++c),
      (ρ (Q.descendant P).carrier).toReal) = (ρ (Q.descendant A).carrier).toReal := by
  classical
  rw [Finset.sum_image (fun _ _ _ _ he => List.append_cancel_left he)]
  simp only [DyadicSquare.descendant_append]
  simpa only [div_one] using (Q.descendant A).normalized_mass_split (Q.descendant_side_pos hQ A) ρ n 1

theorem angularFourCellMeasure_mass_sum (Q₁ Q₂ : DyadicSquare)
    (hQ₁ : 0 < Q₁.side) (hQ₂ : 0 < Q₂.side)
    (ρ ν : Measure Plane) [IsFiniteMeasure ρ] [IsFiniteMeasure ν]
    (A B : CellPath) (n : ℕ) :
    (∑ row ∈ sourceProductVertices Q₁ Q₂ ρ ν A B n,
      ∑ col ∈ sourceProductVertices Q₁ Q₂ ρ ν A B n,
        (angularFourCellMeasure Q₁ Q₂ ρ ν row col).real univ) =
      (ρ (Q₁.descendant A).carrier).toReal^2*(ν (Q₂.descendant B).carrier).toReal^2 := by
  simp_rw [angularFourCellMeasure_real,← Finset.mul_sum,← Finset.sum_mul]
  simp only [sourceProductVertices,Finset.sum_product,← Finset.mul_sum,← Finset.sum_mul]
  rw [occupied_absolute_mass_sum Q₁ hQ₁,occupied_absolute_mass_sum Q₂ hQ₂]
  ring

theorem angular_four_sum_error (Q₁ Q₂ : DyadicSquare)
    (hQ₁ : 0 < Q₁.side) (hQ₂ : 0 < Q₂.side)
    (ρ ν : Measure Plane) [IsFiniteMeasure ρ] [IsFiniteMeasure ν]
    (A B : CellPath) (n : ℕ) (G : (CellPath × CellPath) → (CellPath × CellPath) → Prop)
    [DecidableRel G] (F E : (CellPath × CellPath) → (CellPath × CellPath) → ℂ)
    {ε : ℝ} (hε : 0 ≤ ε)
    (he : ∀ row ∈ sourceProductVertices Q₁ Q₂ ρ ν A B n,
      ∀ col ∈ sourceProductVertices Q₁ Q₂ ρ ν A B n, G row col →
      ‖F row col-E row col‖ ≤ ε*(angularFourCellMeasure Q₁ Q₂ ρ ν row col).real univ) :
    ‖(∑ row ∈ sourceProductVertices Q₁ Q₂ ρ ν A B n,
        ∑ col ∈ sourceProductVertices Q₁ Q₂ ρ ν A B n, if G row col then F row col else 0) -
      (∑ row ∈ sourceProductVertices Q₁ Q₂ ρ ν A B n,
        ∑ col ∈ sourceProductVertices Q₁ Q₂ ρ ν A B n, if G row col then E row col else 0)‖ ≤
      ε*((ρ (Q₁.descendant A).carrier).toReal^2*(ν (Q₂.descendant B).carrier).toReal^2) := by
  rw [← Finset.sum_sub_distrib]
  simp_rw [← Finset.sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ row ∈ sourceProductVertices Q₁ Q₂ ρ ν A B n,
        ∑ col ∈ sourceProductVertices Q₁ Q₂ ρ ν A B n,
          ε*(angularFourCellMeasure Q₁ Q₂ ρ ν row col).real univ := by
      apply Finset.sum_le_sum
      intro row hr
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro col hc
      by_cases hg : G row col
      · simpa only [hg,↓reduceIte] using he row hr col hc hg
      · simp only [hg,↓reduceIte,sub_self,norm_zero]
        positivity
    _ = _ := by simp only [← Finset.mul_sum,angularFourCellMeasure_mass_sum Q₁ Q₂ hQ₁ hQ₂]

theorem angular_four_sum_error_power (Q₁ Q₂ : DyadicSquare)
    (hQ₁ : 0 < Q₁.side) (hQ₂ : 0 < Q₂.side)
    (ρ ν : Measure Plane) [IsFiniteMeasure ρ] [IsFiniteMeasure ν]
    (A B : CellPath) (n N : ℕ) (lam U c Ma₁ Ma₂ : ℝ)
    (hc : 0 ≤ c) (hcR : c ≤ ((2:ℝ)^N)^2) (hM₁ : 0 < Ma₁) (hM₂ : 0 < Ma₂)
    (hm₁ : (ρ (Q₁.descendant A).carrier).toReal/Ma₁ ≤ ((2:ℝ)^N)^(3*lam))
    (hm₂ : (ν (Q₂.descendant B).carrier).toReal/Ma₂ ≤ ((2:ℝ)^N)^(3*lam))
    (G : (CellPath × CellPath) → (CellPath × CellPath) → Prop) [DecidableRel G]
    (F E : (CellPath × CellPath) → (CellPath × CellPath) → ℂ)
    (he : ∀ row ∈ sourceProductVertices Q₁ Q₂ ρ ν A B n,
      ∀ col ∈ sourceProductVertices Q₁ Q₂ ρ ν A B n, G row col →
      ‖F row col-E row col‖ ≤ ((2:ℝ)^N)^(-U)*(angularFourCellMeasure Q₁ Q₂ ρ ν row col).real univ) :
    ‖(c/(Ma₁^2*Ma₂^2)) •
      ((∑ row ∈ sourceProductVertices Q₁ Q₂ ρ ν A B n,
        ∑ col ∈ sourceProductVertices Q₁ Q₂ ρ ν A B n, if G row col then F row col else 0) -
      (∑ row ∈ sourceProductVertices Q₁ Q₂ ρ ν A B n,
        ∑ col ∈ sourceProductVertices Q₁ Q₂ ρ ν A B n, if G row col then E row col else 0))‖ ≤
      ((2:ℝ)^N)^(-U+12*lam+2) := by
  have hε : 0 ≤ ((2:ℝ)^N)^(-U) := by positivity
  have hp := angular_four_sum_error Q₁ Q₂ hQ₁ hQ₂ ρ ν A B n G F E hε he
  have hscale : 0 ≤ c/(Ma₁^2*Ma₂^2) := by positivity
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hscale]
  apply (mul_le_mul_of_nonneg_left hp hscale).trans
  calc
    _ = c*((2:ℝ)^N)^(-U)*
        (((ρ (Q₁.descendant A).carrier).toReal/Ma₁)^2*((ν (Q₂.descendant B).carrier).toReal/Ma₂)^2) := by
      field_simp
    _ ≤ ((2:ℝ)^N)^2*((2:ℝ)^N)^(-U)*
        ((((2:ℝ)^N)^(3*lam))^2*(((2:ℝ)^N)^(3*lam))^2) := by
      gcongr
    _ = _ := by
      simp only [← Real.rpow_mul_natCast (by positivity : (0:ℝ) ≤ (2:ℝ)^N)]
      rw [← Real.rpow_natCast ((2:ℝ)^N) 2]
      simp only [← Real.rpow_add (by positivity : (0:ℝ) < (2:ℝ)^N)]
      congr 1
      ring

end PlanarFalconer

end OAI
