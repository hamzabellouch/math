import OAI.MeasureTheory.Falconer.Angular.AngularCellSpatialIntegral
import OAI.MeasureTheory.Falconer.Angular.AngularRestrictedIntegralSum

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
attribute [local instance] Classical.propDecidable

theorem angular_contribution_spatial_sum (Q₁ Q₂ : DyadicSquare)
    (ρ ν : Measure Plane) [IsFiniteMeasure ρ] [IsFiniteMeasure ν]
    (A B : CellPath) (n : ℕ) (a v : ℝ) {Ψ : ℝ → ℝ}
    (hΨ : Measurable Ψ) (hpos : ∀ t, 0 ≤ Ψ t)
    (hs : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4)
    {W : ℝ} (hW : 0 ≤ W) (hw : ∀ t, Ψ t ≤ W)
    (Ma₁ Ma₂ : ℝ) {Mp₁ Mp₂ : ℝ} (hMp₁ : 0 < Mp₁) (hMp₂ : 0 < Mp₂)
    (β γ : Plane → UnitCircle → ℂ)
    (hβ : Measurable (fun z : Plane × UnitCircle => β z.1 z.2))
    (hγ : Measurable (fun z : Plane × UnitCircle => γ z.1 z.2))
    {D₁ D₂ : ℝ} (hD₁ : 0 ≤ D₁) (hD₂ : 0 ≤ D₂)
    (hbβ : ∀ x u, ‖β x u‖ ≤ D₁) (hbγ : ∀ x u, ‖γ x u‖ ≤ D₂)
    (G : (CellPath × CellPath) → (CellPath × CellPath) → Prop) :
    angularCellContribution Q₁ Q₂ ρ ν A B n a v Ψ Ma₁ Ma₂ Mp₁ Mp₂ β γ G =
      (((2:ℝ)^(2*(v-a)))/(Ma₁^2*Ma₂^2)) •
        ∑ row ∈ sourceProductVertices Q₁ Q₂ ρ ν A B n,
          ∑ col ∈ sourceProductVertices Q₁ Q₂ ρ ν A B n,
            if G row col then angularCellSpatialIntegral Q₁ Q₂ ρ ν β γ row col v Ψ else 0 := by
  let := sourceAngularShellMeasure_finite v Ψ hW hw (fun t ht => by
    by_contra hn
    have := (hs t hn).2
    linarith)
  unfold angularCellContribution
  rw [angularRestrictedIntegral_sum a v Ψ _ G _ _
    (angularCellTransform_measurable Q₁ ρ Mp₁ β hβ)
    (angularCellTransform_measurable Q₂ ν Mp₂ γ hγ)
    (B := D₁*(ρ univ).toReal/Mp₁) (D := D₂*(ν univ).toReal/Mp₂) (by positivity) (by positivity)
    (fun P z => sourceAngularTransform_global_bound ρ _ hMp₁ β hD₁ hbβ z.1 z.2)
    (fun P z => sourceAngularTransform_global_bound ν _ hMp₂ γ hD₂ hbγ z.1 z.2)]
  simp_rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro row _
  apply Finset.sum_congr rfl
  intro col _
  by_cases hg : G row col
  · simp only [hg,↓reduceIte]
    rw [angular_pair_spatial_integral Q₁ Q₂ ρ ν hMp₁ hMp₂ β γ hβ hγ hD₁ hD₂ hbβ hbγ
      row col a v hΨ hpos hs hW hw,smul_smul,smul_smul]
    congr 1
    simp only [mul_inv_rev,pow_two,div_eq_mul_inv]
    field_simp
  · simp [hg]

end PlanarFalconer

end OAI
