import OAI.MeasureTheory.Falconer.Angular.AngularOriginalIntegrability
import OAI.MeasureTheory.Falconer.Angular.AngularLengthIntegralPartition
import OAI.MeasureTheory.Falconer.Graphs.GraphFourMassBound

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

noncomputable def angularFourCellMeasure (Q₁ Q₂ : DyadicSquare) (ρ ν : Measure Plane)
    (row col : CellPath × CellPath) : Measure (Fin 4 → Plane) :=
  Measure.pi (fun i => (![ρ,ρ,ν,ν] i).restrict
    (![(Q₁.descendant row.1).carrier,(Q₁.descendant col.1).carrier,
       (Q₂.descendant row.2).carrier,(Q₂.descendant col.2).carrier] i))

noncomputable def angularSpatialPiece (Q₁ Q₂ : DyadicSquare) (ρ ν : Measure Plane)
    (β γ : Plane → UnitCircle → ℂ) (row col : CellPath × CellPath)
    (v : ℝ) (Ψ : ℝ → ℝ) (S : Set (Fin 4 → Plane)) : ℂ :=
  ∫ x in S, angularOriginalSpatialKernel β γ v Ψ x
    ∂angularFourCellMeasure Q₁ Q₂ ρ ν row col

theorem angular_original_far_partition (Q₁ Q₂ : DyadicSquare)
    (hQ₁ : Q₁.side = 1) (hQ₂ : Q₂.side = 1)
    (ρ ν : Measure Plane) [IsFiniteMeasure ρ] [IsFiniteMeasure ν]
    (A B : CellPath) (a h : ℕ) (hA : A.length = a) (hB : B.length = a)
    (row col : CellPath × CellPath)
    (hr : row ∈ (dyadicPaths h) ×ˢ (dyadicPaths h))
    (hc : col ∈ (dyadicPaths h) ×ˢ (dyadicPaths h))
    (hfar : ¬ angularNear Q₁ Q₂ h row col)
    (hp₀ : (Q₁.descendant row.1).carrier ⊆ (Q₁.descendant A).carrier)
    (hp₁ : (Q₁.descendant col.1).carrier ⊆ (Q₁.descendant A).carrier)
    (hp₂ : (Q₂.descendant row.2).carrier ⊆ (Q₂.descendant B).carrier)
    (hp₃ : (Q₂.descendant col.2).carrier ⊆ (Q₂.descendant B).carrier)
    (β γ : Plane → UnitCircle → ℂ)
    (hβ : Measurable (fun z : Plane × UnitCircle => β z.1 z.2))
    (hγ : Measurable (fun z : Plane × UnitCircle => γ z.1 z.2))
    {D₁ D₂ : ℝ} (hD₁ : 0 ≤ D₁) (hD₂ : 0 ≤ D₂)
    (hbβ : ∀ x u, ‖β x u‖ ≤ D₁) (hbγ : ∀ x u, ‖γ x u‖ ≤ D₂)
    (v : ℝ) {Ψ : ℝ → ℝ} (hΨ : Measurable Ψ)
    (hs : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4)
    {C : ℝ} (hC : 0 ≤ C) (hCΨ : ∀ t, |Ψ t| ≤ C) :
    angularCellSpatialIntegral Q₁ Q₂ ρ ν β γ row col v Ψ =
      angularSpatialPiece Q₁ Q₂ ρ ν β γ row col v Ψ angularLengthLeft +
      angularSpatialPiece Q₁ Q₂ ρ ν β γ row col v Ψ angularLengthRight +
      ∑ b ∈ Finset.Icc (a+9) (h+5),
        angularSpatialPiece Q₁ Q₂ ρ ν β γ row col v Ψ (angularLengthShell b) := by
  let ρs : Fin 4 → Measure Plane := ![ρ,ρ,ν,ν]
  let X : Fin 4 → Set Plane := ![(Q₁.descendant row.1).carrier,(Q₁.descendant col.1).carrier,
    (Q₂.descendant row.2).carrier,(Q₂.descendant col.2).carrier]
  let μ := angularFourCellMeasure Q₁ Q₂ ρ ν row col
  let S : Set (Fin 4 → Plane) := {x | ∀ i, x i ∈ X i}
  let F := angularOriginalSpatialKernel β γ v Ψ
  let : ∀ i, IsFiniteMeasure (ρs i) := by intro i; fin_cases i <;> dsimp [ρs] <;> infer_instance
  let : IsFiniteMeasure μ := inferInstanceAs (IsFiniteMeasure (Measure.pi (fun i => (ρs i).restrict (X i))))
  have hX : ∀ i, MeasurableSet (X i) := by
    intro i; fin_cases i <;> exact DyadicSquare.measurable _
  have hS : MeasurableSet S := by
    convert MeasurableSet.iInter (fun i => (hX i).preimage (measurable_pi_apply i)) using 1
    ext x
    simp [S]
  have hae : ∀ᵐ x ∂μ, x ∈ S := graph_four_spatial_ae_carrier ρs X hX
  have hμ : μ.restrict S = μ := Measure.restrict_eq_self_of_ae_mem hae
  have hi : Integrable F μ := angularOriginalSpatialKernel_integrable μ β γ hβ hγ hD₁ hD₂
    hbβ hbγ v hΨ hs hC hCΨ
  have hu : ∀ x ∈ S, max (dist (x 0) (x 1)) (dist (x 2) (x 3)) ≤ 2*(2:ℝ)^(-(a:ℝ)) := by
    intro x hx
    exact parent_cell_displacement_bound Q₁ Q₂ hQ₁ hQ₂ a A B hA hB x
      (hp₀ (hx 0)) (hp₁ (hx 1)) (hp₂ (hx 2)) (hp₃ (hx 3))
  have hf : ∀ x ∈ S, 16*(2:ℝ)^(-(h:ℝ)) < max (dist (x 0) (x 1)) (dist (x 2) (x 3)) := by
    intro x hx
    exact angular_far_max_displacement Q₁ Q₂ hQ₁ hQ₂ h row col hr hc hfar x
      (hx 0) (hx 1) (hx 2) (hx 3)
  have he (T : Set (Fin 4 → Plane)) : μ.restrict (S ∩ T) = μ.restrict T := by
    apply Measure.restrict_congr_set
    filter_upwards [hae] with x hx
    exact propext (and_iff_right hx)
  have hp := angular_length_integral_partition μ S hS a h hu hf F hi.integrableOn
  simp only [hμ,he] at hp
  rw [angularCellSpatialIntegral_pair]
  exact hp

end PlanarFalconer

end OAI
