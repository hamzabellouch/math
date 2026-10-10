import OAI.MeasureTheory.Falconer.Angular.AngularComparableCarrier

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

theorem angular_noncomparable_far_ae (Q₁ Q₂ : DyadicSquare)
    (hQ₁ : Q₁.side = 1) (hQ₂ : Q₂.side = 1)
    (ρ ν : Measure Plane) [IsFiniteMeasure ρ] [IsFiniteMeasure ν]
    (h : ℕ) (row col : CellPath × CellPath)
    (hr : row ∈ (dyadicPaths h) ×ˢ (dyadicPaths h))
    (hc : col ∈ (dyadicPaths h) ×ˢ (dyadicPaths h))
    (hfar : ¬ angularNear Q₁ Q₂ h row col) :
    ∀ᵐ x ∂(angularFourCellMeasure Q₁ Q₂ ρ ν row col).restrict (angularLengthLeft ∪ angularLengthRight),
      (4*(2:ℝ)^(-(h:ℝ)) ≤ ‖x 0-x 1‖ ∧ 2*‖x 2-x 3‖ ≤ ‖x 0-x 1‖) ∨
      (4*(2:ℝ)^(-(h:ℝ)) ≤ ‖x 2-x 3‖ ∧ 2*‖x 0-x 1‖ ≤ ‖x 2-x 3‖) := by
  let ρs : Fin 4 → Measure Plane := ![ρ,ρ,ν,ν]
  let : ∀ i, IsFiniteMeasure (ρs i) := by intro i; fin_cases i <;> dsimp [ρs] <;> infer_instance
  let X : Fin 4 → Set Plane := ![(Q₁.descendant row.1).carrier,(Q₁.descendant col.1).carrier,
    (Q₂.descendant row.2).carrier,(Q₂.descendant col.2).carrier]
  have hae := graph_four_spatial_ae_carrier ρs X
    (by intro i; fin_cases i <;> exact DyadicSquare.measurable _)
  have haer : ∀ᵐ x ∂(angularFourCellMeasure Q₁ Q₂ ρ ν row col).restrict (angularLengthLeft ∪ angularLengthRight),
      ∀ i, x i ∈ X i := ae_restrict_of_ae hae
  filter_upwards [haer,ae_restrict_mem (measurable_angularLengthLeft.union measurable_angularLengthRight)] with x hx hnc
  have hf := angular_far_max_displacement Q₁ Q₂ hQ₁ hQ₂ h row col hr hc hfar x
    (hx 0) (hx 1) (hx 2) (hx 3)
  simp only [dist_eq_norm] at hf
  rcases hnc with hn | hn
  · change 2*dist (x 2) (x 3) < dist (x 0) (x 1) at hn
    simp only [dist_eq_norm] at hn
    have hmax : max ‖x 0-x 1‖ ‖x 2-x 3‖ = ‖x 0-x 1‖ := max_eq_left (by linarith [norm_nonneg (x 2-x 3)])
    rw [hmax] at hf
    exact Or.inl ⟨by linarith [Real.rpow_pos_of_pos (by norm_num : (0:ℝ) < 2) (-(h:ℝ))],hn.le⟩
  · change 2*dist (x 0) (x 1) < dist (x 2) (x 3) at hn
    simp only [dist_eq_norm] at hn
    have hmax : max ‖x 0-x 1‖ ‖x 2-x 3‖ = ‖x 2-x 3‖ := max_eq_right (by linarith [norm_nonneg (x 0-x 1)])
    rw [hmax] at hf
    exact Or.inr ⟨by linarith [Real.rpow_pos_of_pos (by norm_num : (0:ℝ) < 2) (-(h:ℝ))],hn.le⟩

end PlanarFalconer

end OAI
