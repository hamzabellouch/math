import OAI.MeasureTheory.Falconer.Graphs.GraphGlobalChart
import OAI.MeasureTheory.Falconer.Graphs.GraphSignSupports
import OAI.MeasureTheory.Falconer.Graphs.GraphChartRegularity

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

theorem graph_directions_sum (φ z : ℝ) :
    sourceDirection (φ+Real.arctan z) + sourceDirection (φ-Real.arctan z) =
      (2/Real.sqrt (1+z^2)) • sourceDirection φ := by
  rw [sourceDirection_add_arctan, sourceDirection_sub_arctan, ← smul_add]
  have he (u v : Plane) : (u+v)+(u-v) = (2:ℝ) • u := by
    simp [two_smul, sub_eq_add_neg, add_assoc, add_left_comm]
  rw [he, smul_smul]
  congr 1
  ring

theorem graph_directions_sum_norm (φ z : ℝ) :
    ‖sourceDirection (φ+Real.arctan z) + sourceDirection (φ-Real.arctan z)‖ =
      2/Real.sqrt (1+z^2) := by
  rw [graph_directions_sum, norm_smul, Real.norm_eq_abs, norm_sourceDirection,
    mul_one, abs_of_nonneg (by positivity)]

theorem graph_parameter_bound (φ z : ℝ)
    (hc : 1/2 ≤ ‖sourceDirection (φ+Real.arctan z) + sourceDirection (φ-Real.arctan z)‖) :
    Real.sqrt (1+z^2) ≤ 4 ∧ |z| ≤ 4 := by
  rw [graph_directions_sum_norm] at hc
  have hs : 0 < Real.sqrt (1+z^2) := by positivity
  have hh := (le_div_iff₀ hs).mp hc
  have hb : Real.sqrt (1+z^2) ≤ 4 := by linarith
  have hsq := Real.sq_sqrt (by positivity : 0 ≤ 1+z^2)
  exact ⟨hb, by nlinarith [sq_abs z, abs_nonneg z]⟩

theorem graphGlobalSlice_radius {a b z : ℝ} (ha : 0 < a)
    {η : Plane} (hη : η ∈ graphGlobalSlice a b z) :
    a < ‖η‖*Real.sqrt (1+z^2)/2 ∧ ‖η‖*Real.sqrt (1+z^2)/2 < b := by
  rcases hη with ⟨x, ⟨p,hp,rfl⟩,rfl⟩
  have hs : 0 < Real.sqrt (1+z^2) := by positivity
  have hdom := graphPolarRectangle_subset
    (by positivity : 0 < 2*a/Real.sqrt (1+z^2)) hp
  rw [graphPlaneEquiv_norm, polarCoord.right_inv hdom]
  have hlo := (div_lt_iff₀ hs).mp hp.1.1
  have hhi := (lt_div_iff₀ hs).mp hp.1.2
  constructor <;> linarith

theorem graphGlobalSlice_frequency_bounds {z : ℝ} {η : Plane}
    (hη : η ∈ graphGlobalSlice (1/4) 4 z)
    (hc : 1/2 ≤ ‖sourceDirection (graphPlaneAngle η+Real.arctan z) +
      sourceDirection (graphPlaneAngle η-Real.arctan z)‖) :
    1/8 ≤ ‖η‖ ∧ ‖η‖ ≤ 8 ∧ |z| ≤ 4 := by
  have hr := graphGlobalSlice_radius (by norm_num : (0:ℝ) < 1/4) hη
  have hb := graph_parameter_bound (graphPlaneAngle η) z hc
  have hs : 1 ≤ Real.sqrt (1+z^2) := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]
    nlinarith [sq_nonneg z]
  refine ⟨?_,?_,hb.2⟩
  · nlinarith [mul_le_mul_of_nonneg_left hb.1 (norm_nonneg η)]
  · nlinarith [mul_le_mul_of_nonneg_left hs (norm_nonneg η)]

theorem graph_plus_support_parameter (φ z : ℝ)
    (hc : (sourceUnitDirection (φ+Real.arctan z), sourceUnitDirection (φ-Real.arctan z)) ∈
      tsupport circleGraphSignPlus) :
    |z| ≤ 4 := by
  have hh := circleGraphSignPlus_tsupport hc
  change 1 ≤ ‖(sourceUnitDirection (φ+Real.arctan z) : Plane) +
    (sourceUnitDirection (φ-Real.arctan z) : Plane)‖ at hh
  apply (graph_parameter_bound φ z _).2
  change 1/2 ≤ ‖(sourceUnitDirection (φ+Real.arctan z) : Plane) +
    (sourceUnitDirection (φ-Real.arctan z) : Plane)‖
  linarith

theorem graph_minus_support_parameter (φ z : ℝ)
    (hc : (sourceUnitDirection (φ+Real.arctan z), sourceUnitDirection (φ-Real.arctan z+Real.pi)) ∈
      tsupport circleGraphSignMinus) : |z| ≤ 4 := by
  have hh := circleGraphSignMinus_tsupport hc
  change 1 ≤ ‖sourceDirection (φ+Real.arctan z) -
    sourceDirection (φ-Real.arctan z+Real.pi)‖ at hh
  rw [sourceDirection_add_pi, sub_neg_eq_add] at hh
  exact (graph_parameter_bound φ z (by linarith)).2

theorem graphCartesianEquiv_symm_norm_le {η : Plane} {z : ℝ}
    (hη : ‖η‖ ≤ 8) (hz : |z| ≤ 4) :
    ‖graphCartesianEquiv.symm (η,z)‖ ≤ 8 := by
  apply (pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ) ≤ 8)).mpr
  intro i
  fin_cases i
  · change ‖η 0‖ ≤ 8
    exact (PiLp.norm_apply_le η 0).trans hη
  · change ‖η 1‖ ≤ 8
    exact (PiLp.norm_apply_le η 1).trans hη
  · change ‖z‖ ≤ 8
    rw [Real.norm_eq_abs]
    linarith

theorem graph_global_jacobian_derivative_bound (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (η : Plane) (z : ℝ),
      η ∈ graphGlobalSlice (1/4) 4 z →
      1/2 ≤ ‖sourceDirection (graphPlaneAngle η+Real.arctan z) +
        sourceDirection (graphPlaneAngle η-Real.arctan z)‖ →
      ‖iteratedFDeriv ℝ n graphJacobianWeight (graphCartesianEquiv.symm (η,z))‖ ≤ C := by
  obtain ⟨C,hC,hbound⟩ := graphJacobianWeight_uniform_derivatives n
  refine ⟨C,hC,?_⟩
  intro η z hη hc
  have hb := graphGlobalSlice_frequency_bounds hη hc
  apply hbound _ (graphCartesianEquiv_symm_norm_le hb.2.1 hb.2.2)
  have he := congrArg Prod.fst (graphCartesianEquiv_apply (graphCartesianEquiv.symm (η,z)))
  simp only [MeasurableEquiv.apply_symm_apply] at he
  rw [← he]
  exact hb.1

end PlanarFalconer

end OAI
