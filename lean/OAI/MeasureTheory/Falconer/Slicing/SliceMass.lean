import OAI.MeasureTheory.Falconer.Slicing.SliceGeometry
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

namespace OAI

/-! # Exact mass identities for the actual normalized point bands -/

namespace Falconer
open Set Metric MeasureTheory
open scoped ENNReal
variable {d : ℕ}

noncomputable def pointSliceMeasure (μ : Measure (Space d))
    (V : Submodule ℝ (Space d)) (δ : ℝ) (z : Vᗮ) : Measure (Space d) :=
  ENNReal.ofReal (δ^(-(Module.finrank ℝ Vᗮ:ℝ))) • μ.restrict (pointSliceBand V z δ)

instance pointSliceMeasure_finite (μ : Measure (Space d)) [IsFiniteMeasure μ]
    (V : Submodule ℝ (Space d)) (δ : ℝ) (z : Vᗮ) :
    IsFiniteMeasure (pointSliceMeasure μ V δ z) := by
  refine ⟨?_⟩
  change ENNReal.ofReal (δ^(-(Module.finrank ℝ Vᗮ:ℝ)))*
    (μ.restrict (pointSliceBand V z δ)) univ < ∞
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)

theorem pointSliceBand_parameter_measure (V : Submodule ℝ (Space d)) (δ : ℝ)
    (x : Space d) :
    (volume : Measure Vᗮ) {z : Vᗮ | x ∈ pointSliceBand V z δ} =
      (volume : Measure Vᗮ) (closedBall 0 δ) := by
  have he : {z : Vᗮ | x ∈ pointSliceBand V z δ} =
      closedBall (Vᗮ.orthogonalProjectionOnto x) δ := by
    ext z
    change ‖Vᗮ.starProjection x-(z:Space d)‖ ≤ δ ↔
      dist z (Vᗮ.orthogonalProjectionOnto x) ≤ δ
    rw [dist_comm,dist_eq_norm]
    rfl
  rw [he,Measure.addHaar_closedBall_center]

theorem pointSliceBand_integrated_mass (μ : Measure (Space d)) [SFinite μ]
    (V : Submodule ℝ (Space d)) (δ : ℝ) :
    (∫⁻ z : Vᗮ, μ (pointSliceBand V z δ)) =
      (volume : Measure Vᗮ) (closedBall 0 δ)*μ univ := by
  let S : Set (Vᗮ × Space d) := {p | p.2 ∈ pointSliceBand V p.1 δ}
  have hS : MeasurableSet S := by
    change MeasurableSet {p : Vᗮ × Space d | ‖Vᗮ.starProjection p.2-(p.1:Space d)‖ ≤ δ}
    exact measurableSet_le (by fun_prop) measurable_const
  calc
    _ = ((volume : Measure Vᗮ).prod μ) S := (Measure.prod_apply hS).symm
    _ = ∫⁻ x : Space d, (volume : Measure Vᗮ) {z : Vᗮ | x ∈ pointSliceBand V z δ} ∂μ :=
      Measure.prod_apply_symm hS
    _ = ∫⁻ _ : Space d, (volume : Measure Vᗮ) (closedBall 0 δ) ∂μ := by
      apply lintegral_congr
      intro x
      exact pointSliceBand_parameter_measure V δ x
    _ = _ := by rw [lintegral_const]

theorem pointSliceMeasure_integrated_mass (μ : Measure (Space d)) [SFinite μ]
    (V : Submodule ℝ (Space d)) {δ : ℝ} (hδ : 0 < δ) :
    (∫⁻ z : Vᗮ, pointSliceMeasure μ V δ z univ) =
      (volume : Measure Vᗮ) (closedBall 0 1)*μ univ := by
  have hw : ENNReal.ofReal (δ^(-(Module.finrank ℝ Vᗮ:ℝ)))*
      ENNReal.ofReal (δ^Module.finrank ℝ Vᗮ) = 1 := by
    rw [← ENNReal.ofReal_mul (by positivity),← Real.rpow_natCast,
      ← Real.rpow_add hδ,neg_add_cancel,Real.rpow_zero,ENNReal.ofReal_one]
  simp only [pointSliceMeasure,Measure.smul_apply,smul_eq_mul,Measure.restrict_apply_univ]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,pointSliceBand_integrated_mass,
    Measure.addHaar_closedBall' volume 0 hδ.le]
  simp only [← mul_assoc,hw,one_mul]

end Falconer

end OAI
