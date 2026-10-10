import OAI.MeasureTheory.Falconer.Angular.AngularFourCellMass

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

theorem angular_comparable_far_ae (Q₁ Q₂ : DyadicSquare)
    (hQ₁ : Q₁.side = 1) (hQ₂ : Q₂.side = 1)
    (ρ ν : Measure Plane) [IsFiniteMeasure ρ] [IsFiniteMeasure ν]
    (h : ℕ) (row col : CellPath × CellPath)
    (hr : row ∈ (dyadicPaths h) ×ˢ (dyadicPaths h))
    (hc : col ∈ (dyadicPaths h) ×ˢ (dyadicPaths h))
    (hfar : ¬ angularNear Q₁ Q₂ h row col) :
    ∀ᵐ x ∂(angularFourCellMeasure Q₁ Q₂ ρ ν row col).restrict angularLengthComparable,
      4*(2:ℝ)^(-(h:ℝ)) ≤ ‖x 0-x 1‖ ∧ 4*(2:ℝ)^(-(h:ℝ)) ≤ ‖x 2-x 3‖ := by
  let ρs : Fin 4 → Measure Plane := ![ρ,ρ,ν,ν]
  let : ∀ i, IsFiniteMeasure (ρs i) := by intro i; fin_cases i <;> dsimp [ρs] <;> infer_instance
  let X : Fin 4 → Set Plane := ![(Q₁.descendant row.1).carrier,(Q₁.descendant col.1).carrier,
    (Q₂.descendant row.2).carrier,(Q₂.descendant col.2).carrier]
  have hae := graph_four_spatial_ae_carrier ρs X
    (by intro i; fin_cases i <;> exact DyadicSquare.measurable _)
  have haer : ∀ᵐ x ∂(angularFourCellMeasure Q₁ Q₂ ρ ν row col).restrict angularLengthComparable,
      ∀ i, x i ∈ X i := ae_restrict_of_ae hae
  filter_upwards [haer,ae_restrict_mem measurable_angularLengthComparable] with x hx hcmp
  have hf := angular_far_max_displacement Q₁ Q₂ hQ₁ hQ₂ h row col hr hc hfar x
    (hx 0) (hx 1) (hx 2) (hx 3)
  have h1 : max (dist (x 0) (x 1)) (dist (x 2) (x 3)) ≤ 2*dist (x 0) (x 1) :=
    max_le (by simpa only [two_mul] using le_add_of_nonneg_right (dist_nonneg (x := x 0) (y := x 1))) hcmp.2
  have h2 : max (dist (x 0) (x 1)) (dist (x 2) (x 3)) ≤ 2*dist (x 2) (x 3) :=
    max_le hcmp.1 (by simpa only [two_mul] using le_add_of_nonneg_right (dist_nonneg (x := x 2) (y := x 3)))
  rw [← dist_eq_norm,← dist_eq_norm]
  constructor <;> linarith [Real.rpow_pos_of_pos (by norm_num : (0:ℝ) < 2) (-(h:ℝ))]

end PlanarFalconer

end OAI
