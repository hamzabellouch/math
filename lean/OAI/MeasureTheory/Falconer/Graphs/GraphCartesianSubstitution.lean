import OAI.MeasureTheory.Falconer.Graphs.GraphPolarJacobian
import OAI.MeasureTheory.Falconer.Graphs.GraphLiftInverse

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal

noncomputable def graphCartesianFrequency (x : GraphLiftSpace) : Plane := WithLp.toLp 2 ![x 0,x 1]

noncomputable def graphJacobianWeight (x : GraphLiftSpace) : ℝ :=
  (‖graphCartesianFrequency x‖*Real.sqrt (1+(x 2)^2))⁻¹

theorem graphCartesianFrequency_polar (p : GraphLiftSpace) :
    graphCartesianFrequency (graphPolarMap p) = p 0 • sourceDirection (p 1) := by
  ext i
  fin_cases i <;> simp [graphCartesianFrequency, graphPolarMap, sourceDirection,
    Complex.orthonormalBasisOneI_repr_apply, -Complex.ofReal_cos, -Complex.ofReal_sin]

theorem graphJacobianWeight_polar {p : GraphLiftSpace} (hp : p ∈ graphPolarDomain) :
    graphJacobianWeight (graphPolarMap p) = (p 0*Real.sqrt (1+(p 2)^2))⁻¹ := by
  simp only [graphJacobianWeight, graphCartesianFrequency_polar, norm_smul,
    Real.norm_eq_abs, abs_of_pos hp.1, norm_sourceDirection, mul_one]
  rfl

theorem graph_chart_cartesian_lintegral (S : Set GraphLiftSpace) (hS : MeasurableSet S)
    (hdom : S ⊆ graphPolarDomain) (f : GraphLiftSpace → ℝ≥0∞) :
    (∫⁻ q in graphLiftMap '' S, f q) =
      ∫⁻ x in graphPolarMap '' S, ENNReal.ofReal (graphJacobianWeight x) *
        f (graphLiftMap (graphPolarInverse x)) := by
  rw [graphLiftMap_lintegral S hS f,
    graphPolarMap_lintegral S hS hdom]
  apply setLIntegral_congr_fun hS
  intro p hp
  dsimp only
  rw [graphPolarInverse_left (hdom hp), graphJacobianWeight_polar (hdom hp)]
  have hr : 0 < p 0 := (hdom hp).1
  have hs : 0 < Real.sqrt (1+(p 2)^2) := by positivity
  rw [← mul_assoc, ← ENNReal.ofReal_mul hr.le]
  congr 2
  field_simp

theorem graphLiftMap_endpoint_frequencies (p : GraphLiftSpace) :
    (graphLiftMap p) 0 • sourceDirection ((graphLiftMap p) 1) =
      graphB (p 2) (graphCartesianFrequency (graphPolarMap p)) ∧
    (graphLiftMap p) 0 • sourceDirection ((graphLiftMap p) 2) =
      graphA (p 2) (graphCartesianFrequency (graphPolarMap p)) := by
  have hs : Real.sqrt (1+(p 2)^2) ≠ 0 := by positivity
  have hscale : p 0*Real.sqrt (1+(p 2)^2)/2*(Real.sqrt (1+(p 2)^2))⁻¹ = (1/2:ℝ)*p 0 := by
    field_simp
  rw [graphCartesianFrequency_polar]
  constructor
  · change (p 0*Real.sqrt (1+(p 2)^2)/2) • sourceDirection (p 1+Real.arctan (p 2)) = _
    rw [sourceDirection_add_arctan, smul_smul]
    rw [hscale,graphB,quarterTurn_smul,smul_comm (p 2),← smul_add,smul_smul]
  · change (p 0*Real.sqrt (1+(p 2)^2)/2) • sourceDirection (p 1-Real.arctan (p 2)) = _
    rw [sourceDirection_sub_arctan, smul_smul]
    rw [hscale,graphA,quarterTurn_smul,smul_comm (p 2),← smul_sub,smul_smul]

end PlanarFalconer

end OAI
