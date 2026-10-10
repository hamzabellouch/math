import OAI.MeasureTheory.Falconer.Angular.AngularOccupiedFarPartition

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

theorem angular_comparable_integral_partition (Q₁ Q₂ : DyadicSquare)
    (hQ₁ : Q₁.side = 1) (hQ₂ : Q₂.side = 1)
    (ρ ν : Measure Plane) [IsFiniteMeasure ρ] [IsFiniteMeasure ν]
    (A B : CellPath) (a d : ℕ) (hA : A.length = a) (hB : B.length = a)
    (row col : CellPath × CellPath)
    (hr : row ∈ sourceProductVertices Q₁ Q₂ ρ ν A B d)
    (hc : col ∈ sourceProductVertices Q₁ Q₂ ρ ν A B d)
    (hfar : ¬ angularNear Q₁ Q₂ (a+d) row col)
    (F : (Fin 4 → Plane) → ℂ)
    (hF : IntegrableOn F angularLengthComparable (angularFourCellMeasure Q₁ Q₂ ρ ν row col)) :
    (∫ x in angularLengthComparable, F x ∂angularFourCellMeasure Q₁ Q₂ ρ ν row col) =
      ∑ b ∈ Finset.Icc (a+9) (a+d+5),
        ∫ x in angularLengthShell b, F x ∂angularFourCellMeasure Q₁ Q₂ ρ ν row col := by
  have hp₁ : 0 < Q₁.side := by rw [hQ₁]; norm_num
  have hp₂ : 0 < Q₂.side := by rw [hQ₂]; norm_num
  have hparentr := sourceProductVertices_parent Q₁ Q₂ hp₁ hp₂ ρ ν A B d hr
  have hparentc := sourceProductVertices_parent Q₁ Q₂ hp₁ hp₂ ρ ν A B d hc
  let ρs : Fin 4 → Measure Plane := ![ρ,ρ,ν,ν]
  let : ∀ i, IsFiniteMeasure (ρs i) := by intro i; fin_cases i <;> dsimp [ρs] <;> infer_instance
  let X : Fin 4 → Set Plane := ![(Q₁.descendant row.1).carrier,(Q₁.descendant col.1).carrier,
    (Q₂.descendant row.2).carrier,(Q₂.descendant col.2).carrier]
  let μ := angularFourCellMeasure Q₁ Q₂ ρ ν row col
  let S : Set (Fin 4 → Plane) := {x | ∀ i, x i ∈ X i}
  have hX : ∀ i, MeasurableSet (X i) := by intro i; fin_cases i <;> exact DyadicSquare.measurable _
  have hS : MeasurableSet S := by
    convert MeasurableSet.iInter (fun i => (hX i).preimage (measurable_pi_apply i)) using 1
    ext x
    simp [S]
  have hae : ∀ᵐ x ∂μ, x ∈ S := graph_four_spatial_ae_carrier ρs X hX
  have he (T : Set (Fin 4 → Plane)) : μ.restrict (S ∩ T) = μ.restrict T := by
    apply Measure.restrict_congr_set
    filter_upwards [hae] with x hx
    exact propext (and_iff_right hx)
  have hu : ∀ x ∈ S, max (dist (x 0) (x 1)) (dist (x 2) (x 3)) ≤ 2*(2:ℝ)^(-(a:ℝ)) := by
    intro x hx
    exact parent_cell_displacement_bound Q₁ Q₂ hQ₁ hQ₂ a A B hA hB x
      (hparentr.1 (hx 0)) (hparentc.1 (hx 1)) (hparentr.2 (hx 2)) (hparentc.2 (hx 3))
  have hf : ∀ x ∈ S, 16*(2:ℝ)^(-((a+d:ℕ):ℝ)) < max (dist (x 0) (x 1)) (dist (x 2) (x 3)) := by
    intro x hx
    exact angular_far_max_displacement Q₁ Q₂ hQ₁ hQ₂ (a+d) row col
      (sourceProductVertices_subset Q₁ Q₂ ρ ν A B a d hA hB hr)
      (sourceProductVertices_subset Q₁ Q₂ ρ ν A B a d hA hB hc) hfar x
      (hx 0) (hx 1) (hx 2) (hx 3)
  have hint : (∫ x in S ∩ angularLengthComparable, F x ∂μ) =
      ∑ b ∈ Finset.Icc (a+9) (a+d+5), ∫ x in S ∩ angularLengthShell b, F x ∂μ := by
    rw [angular_comparable_shell_union S a (a+d) hu hf]
    apply integral_biUnion_finset
    · exact fun b _ => hS.inter (measurable_angularLengthShell b)
    · intro b _ c _ hbc
      exact (angularLengthShell_disjoint hbc).mono inter_subset_right inter_subset_right
    · intro b hb
      exact hF.mono_set (fun x hx => hx.2.1)
  simpa only [he] using hint

end PlanarFalconer

end OAI
