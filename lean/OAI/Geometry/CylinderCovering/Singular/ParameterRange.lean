import OAI.Geometry.CylinderCovering.Singular.ParameterRangeDefinitions
import OAI.Geometry.RuledCovering.Main
import OAI.Geometry.CylinderCovering.Singular.Cutoff

namespace OAI

open Filter Topology

namespace CylinderCovering.SingularParameterRange
open RuledApproximation

lemma critical_exponent_bounds :
    1 < (Real.sqrt 51 - 5) / 2 ∧ (Real.sqrt 51 - 5) / 2 < 2 := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 51 by norm_num)
  have hn := Real.sqrt_nonneg (51 : ℝ)
  constructor <;> nlinarith

lemma numerator_negative_iff {p : ℝ} (hp : 0 < p) :
    2 * p ^ 2 + 10 * p - 13 < 0 ↔ p < (Real.sqrt 51 - 5) / 2 := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 51 by norm_num)
  have hn := Real.sqrt_nonneg (51 : ℝ)
  constructor
  · intro h
    by_contra hnot
    have hge : Real.sqrt 51 ≤ 2 * p + 5 := by linarith
    nlinarith
  · intro h
    have hlt : 2 * p + 5 < Real.sqrt 51 := by linarith
    nlinarith

theorem coefficient_negative_iff {p : ℝ} (hp : 1 < p) :
    singularCoefficient p < 0 ↔ p < (Real.sqrt 51 - 5) / 2 := by
  have hp0 : 0 < p := by linarith
  have he : singularCoefficient p * (480 * p) = 2 * p ^ 2 + 10 * p - 13 := by
    unfold singularCoefficient
    field_simp
    ring
  constructor
  · intro h
    apply (numerator_negative_iff hp0).mp
    rw [← he]
    exact mul_neg_of_neg_of_pos h (by positivity)
  · intro h
    have hn := (numerator_negative_iff hp0).mpr h
    have hd : 0 < 30 * p := by positivity
    exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (by norm_num) hn) hd

lemma coefficient_at_critical :
    singularCoefficient ((Real.sqrt 51 - 5) / 2) = 0 := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 51 by norm_num)
  have hn : 2 * ((Real.sqrt 51 - 5) / 2) ^ 2 +
      10 * ((Real.sqrt 51 - 5) / 2) - 13 = 0 := by nlinarith
  simp [singularCoefficient, hn]

lemma coefficient_at_one : singularCoefficient 1 = -(1 / 480 : ℝ) := by
  norm_num [singularCoefficient]

theorem coefficient_limit_at_one :
    Tendsto singularCoefficient (𝓝 1) (𝓝 (-(1 / 480 : ℝ))) := by
  have hc : ContinuousAt singularCoefficient 1 := by
    unfold singularCoefficient
    fun_prop (disch := norm_num)
  simpa only [coefficient_at_one] using hc.tendsto

theorem cutoff_window_nonempty_iff (p : ℝ) :
    (∃ γ : ℝ, 1 < γ ∧ γ < 1 / (2 - p)) ↔ 1 < p ∧ p < 2 := by
  constructor
  · rintro ⟨γ, hγ, hγp⟩
    have hpos : 0 < 1 / (2 - p) := by linarith
    have hd : 0 < 2 - p := (one_div_pos.mp hpos)
    have hmul := (lt_div_iff₀ hd).mp hγp
    constructor
    · nlinarith
    · linarith
  · rintro ⟨hp, hp2⟩
    have hd : 0 < 2 - p := by linarith
    have hlt : 1 < 1 / (2 - p) := (lt_div_iff₀ hd).mpr (by linarith)
    exact exists_between hlt

theorem endpoint_derivative_determinant {z : Plane} (hz : 0 < z 1) :
    LinearMap.det (fderiv ℝ (singularField 1) z).toLinearMap = 0 := by
  simpa using (singularField_trace_det 1 hz).2

theorem endpoint_derivative_squareZero {z : Plane} (hz : 0 < z 1) :
    (fderiv ℝ (singularField 1) z).comp (fderiv ℝ (singularField 1) z) = 0 := by
  rw [singularField_fderiv 1 hz]
  ext w i
  fin_cases i <;>
    simp [ContinuousLinearMap.comp_apply, matrixCLM_apply, vec2] <;> ring

theorem endpoint_eigenvalue_eq_zero {z : Plane} (hz : 0 < z 1) {μ : ℝ}
    (hμ : Module.End.HasEigenvalue (fderiv ℝ (singularField 1) z).toLinearMap μ) :
    μ = 0 := by
  obtain ⟨u, hu⟩ := hμ.exists_hasEigenvector
  have he : (fderiv ℝ (singularField 1) z)
      ((fderiv ℝ (singularField 1) z) u) = 0 :=
    congrArg (fun A : Plane →L[ℝ] Plane => A u) (endpoint_derivative_squareZero hz)
  change (fderiv ℝ (singularField 1) z).toLinearMap
      ((fderiv ℝ (singularField 1) z).toLinearMap u) = 0 at he
  rw [hu.apply_eq_smul, map_smul, hu.apply_eq_smul, smul_smul] at he
  have hm : μ * μ = 0 := (smul_eq_zero.mp he).resolve_right hu.2
  exact mul_self_eq_zero.mp hm

theorem statement : Statement where
  negative_range _ hp := coefficient_negative_iff hp
  critical_zero := coefficient_at_critical
  endpoint_value := coefficient_at_one
  endpoint_limit := coefficient_limit_at_one
  cutoff_window := cutoff_window_nonempty_iff
  endpoint_degenerate _ hz :=
    ⟨endpoint_derivative_determinant hz, fun _ hμ => endpoint_eigenvalue_eq_zero hz hμ⟩

end CylinderCovering.SingularParameterRange

end OAI
