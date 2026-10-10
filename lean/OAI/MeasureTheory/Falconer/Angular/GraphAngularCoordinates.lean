import OAI.MeasureTheory.Falconer.Graphs.GraphSignPartition
import OAI.MeasureTheory.Falconer.Angular.CircleMaskCoordinates
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

namespace OAI

namespace PlanarFalconer
open Set
open scoped ContDiff

theorem sourceDirection_contDiff : ContDiff ℝ ∞ sourceDirection := by
  exact Complex.orthonormalBasisOneI.repr.toContinuousLinearMap.contDiff.comp
    ((Complex.ofRealCLM.contDiff.comp Real.contDiff_cos).add
      ((Complex.ofRealCLM.contDiff.comp Real.contDiff_sin).mul contDiff_const))

theorem sourceDirection_add_arctan (φ z : ℝ) :
    sourceDirection (φ+Real.arctan z) =
      (Real.sqrt (1+z^2))⁻¹ • (sourceDirection φ+z • quarterTurn (sourceDirection φ)) := by
  ext i
  fin_cases i <;>
    simp [sourceDirection, quarterTurn, Complex.orthonormalBasisOneI_repr_apply,
      Real.cos_add, Real.sin_add, Real.cos_arctan, Real.sin_arctan,
      -Complex.ofReal_sin, -Complex.ofReal_cos] <;> ring

theorem sourceDirection_sub_arctan (φ z : ℝ) :
    sourceDirection (φ-Real.arctan z) =
      (Real.sqrt (1+z^2))⁻¹ • (sourceDirection φ-z • quarterTurn (sourceDirection φ)) := by
  simpa only [Real.arctan_neg, neg_sq, neg_smul, sub_eq_add_neg] using
    sourceDirection_add_arctan φ (-z)

theorem graph_chart_angular_lifts (u v : Plane) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (hw : u+v ≠ 0) (φ : ℝ) (hφ : u+v = ‖u+v‖ • sourceDirection φ) :
    u = sourceDirection (φ+Real.arctan (graphChartZ u v)) ∧
    v = sourceDirection (φ-Real.arctan (graphChartZ u v)) := by
  have he := graph_chart_endpoints u v hu hv hw
  have hr := graph_chart_radius_identity u v hu hv hw
  have hs : Real.sqrt (1+(graphChartZ u v)^2) ≠ 0 := by positivity
  have hn : (1/2:ℝ)*‖u+v‖ = (Real.sqrt (1+(graphChartZ u v)^2))⁻¹ := by
    rw [← one_div]
    apply (eq_div_iff hs).mpr
    nlinarith
  constructor
  · calc
      u = graphB (graphChartZ u v) (u+v) := he.1
      _ = _ := by rw [graphB, hφ, quarterTurn_smul, smul_comm (graphChartZ u v),
        ← smul_add, smul_smul, hn, sourceDirection_add_arctan]
  · calc
      v = graphA (graphChartZ u v) (u+v) := he.2
      _ = _ := by rw [graphA, hφ, quarterTurn_smul, smul_comm (graphChartZ u v),
        ← smul_sub, smul_smul, hn, sourceDirection_sub_arctan]

theorem graph_chart_axis_lift (w : Plane) (hw : w ≠ 0) :
    ∃ φ ∈ Ioc (-Real.pi) Real.pi, w = ‖w‖ • sourceDirection φ := by
  let dir : UnitCircle := ⟨‖w‖⁻¹ • w, by simp [norm_smul, norm_ne_zero_iff.mpr hw]⟩
  refine ⟨sourceAngle dir, ?_, ?_⟩
  · exact ⟨Complex.neg_pi_lt_arg _, Complex.arg_le_pi _⟩
  · have he := congrArg (fun x : UnitCircle => (x:Plane)) (sourceUnitDirection_sourceAngle dir)
    change sourceDirection (sourceAngle dir) = ‖w‖⁻¹ • w at he
    rw [he, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hw), one_smul]

theorem actual_sign_chart_angular_lifts (dir₁ dir₂ : UnitCircle) (s : ℝ)
    (hs : s = 1 ∨ s = -1) (hchart : 1/2 ≤ ‖(dir₁:Plane)+s • (dir₂:Plane)‖) :
    let z := graphChartZ (dir₁:Plane) (s • (dir₂:Plane))
    ∃ φ ∈ Ioc (-Real.pi) Real.pi,
      (dir₁:Plane) = sourceDirection (φ+Real.arctan z) ∧
      s • (dir₂:Plane) = sourceDirection (φ-Real.arctan z) ∧
      (dir₁:Plane)+s • (dir₂:Plane) =
        ‖(dir₁:Plane)+s • (dir₂:Plane)‖ • sourceDirection φ := by
  have hw : (dir₁:Plane)+s • (dir₂:Plane) ≠ 0 := norm_pos_iff.mp (by linarith)
  obtain ⟨φ,hφ,haxis⟩ := graph_chart_axis_lift _ hw
  have he := graph_chart_angular_lifts _ _ dir₁.property (circle_sign_norm s hs dir₂) hw φ haxis
  exact ⟨φ,hφ,he.1,he.2,haxis⟩

theorem graphSignPartition_angular_contDiff :
    ContDiff ℝ ∞ (fun p : ℝ × ℝ => circleGraphSignPlus
      (sourceUnitDirection p.1, sourceUnitDirection p.2)) ∧
    ContDiff ℝ ∞ (fun p : ℝ × ℝ => circleGraphSignMinus
      (sourceUnitDirection p.1, sourceUnitDirection p.2)) := by
  have hd := (sourceDirection_contDiff.comp contDiff_fst).prodMk
    (sourceDirection_contDiff.comp contDiff_snd)
  exact ⟨graphSignPlus_contDiff.comp hd, graphSignMinus_contDiff.comp hd⟩

end PlanarFalconer

end OAI
