import OAI.MeasureTheory.Falconer.Graphs.AllDimensionalGraphGeometry

namespace OAI

/-!
# Nonstationary directions for discarded graph edges

The sphere vector field is the tangential projection of one fixed unit
vector. Its phase derivative stays large on a cap when a perpendicular
center test fails. This is the geometric part of `graph:localization`;
integration by parts is a separate analytic step.
-/

namespace Falconer

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem perpendicularPart_self_adjoint (w u v : E) :
    inner ℝ (perpendicularPart w u) v = inner ℝ u (perpendicularPart w v) := by
  simp only [perpendicularPart, inner_sub_left, inner_sub_right,
    real_inner_smul_left, real_inner_smul_right]
  rw [real_inner_comm u w]
  ring

theorem perpendicularPart_orthogonal {w : E} (hw : ‖w‖ = 1) (v : E) :
    inner ℝ w (perpendicularPart w v) = 0 := by
  simp only [perpendicularPart, inner_sub_right, real_inner_smul_right,
    real_inner_self_eq_norm_sq, hw, one_pow, mul_one, sub_self]

theorem perpendicularPart_inner_original {w : E} (hw : ‖w‖ = 1) (v : E) :
    inner ℝ (perpendicularPart w v) v = ‖perpendicularPart w v‖^2 := by
  have hp := perpendicularPart_orthogonal hw v
  have hp' : inner ℝ (perpendicularPart w v) w = 0 := by
    rw [real_inner_comm, hp]
  have hid : v = perpendicularPart w v + inner ℝ w v • w := by
    dsimp [perpendicularPart]
    abel
  calc
    _ = inner ℝ (perpendicularPart w v)
        (perpendicularPart w v + inner ℝ w v • w) :=
      congrArg (inner ℝ (perpendicularPart w v)) hid
    _ = _ := by
      rw [inner_add_right, real_inner_smul_right, hp', mul_zero, add_zero,
        real_inner_self_eq_norm_sq]

/-- A fixed unit tangent at the cap center whose scalar product with the
center displacement equals its perpendicular length. -/
theorem exists_unit_tangent {w : E} (hw : ‖w‖ = 1) (v : E)
    (hne : perpendicularPart w v ≠ 0) :
    ∃ t : E, ‖t‖ = 1 ∧ inner ℝ w t = 0 ∧
      inner ℝ t v = ‖perpendicularPart w v‖ := by
  let p := perpendicularPart w v
  have hp : 0 < ‖p‖ := norm_pos_iff.mpr hne
  refine ⟨‖p‖⁻¹ • p, ?_, ?_, ?_⟩
  · rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hp), inv_mul_cancel₀ hp.ne']
  · rw [real_inner_smul_right, perpendicularPart_orthogonal hw v, mul_zero]
  · rw [real_inner_smul_left, perpendicularPart_inner_original hw v]
    dsimp only [p]
    field_simp

/-- The sphere field `t - ⟪w,t⟫ w` is tangent and has the expected
uniform phase-derivative error under cap and point replacement. -/
theorem angular_phase_derivative_error {w w₀ t : E}
    (hw : ‖w‖ = 1) (hw₀ : ‖w₀‖ = 1) (ht : ‖t‖ = 1)
    (htan : inner ℝ w₀ t = 0) (v d : E) :
    |inner ℝ (perpendicularPart w t) v - inner ℝ t d| ≤
      ‖v-d‖ + 2 * ‖w-w₀‖ * ‖d‖ := by
  have hbase : inner ℝ t (perpendicularPart w₀ d) = inner ℝ t d := by
    have htzero : inner ℝ t w₀ = 0 := by rw [real_inner_comm, htan]
    simp only [perpendicularPart, inner_sub_right, real_inner_smul_right,
      htzero, mul_zero, sub_zero]
  rw [perpendicularPart_self_adjoint, ← hbase, ← inner_sub_right]
  calc
    _ ≤ ‖t‖ * ‖perpendicularPart w v - perpendicularPart w₀ d‖ := abs_real_inner_le_norm _ _
    _ = ‖perpendicularPart w v - perpendicularPart w₀ d‖ := by rw [ht, one_mul]
    _ ≤ _ := perpendicularPart_test_error hw hw₀ v d

/-- One fixed tangent direction witnesses nonstationarity throughout the
allowed perturbations of a discarded perpendicular edge. -/
theorem perpendicular_failure_nonstationary {w₀ d : E} (hw₀ : ‖w₀‖ = 1)
    {τ : ℝ} (hτ : 0 < τ) (hbad : τ < ‖perpendicularPart w₀ d‖) :
    ∃ t : E, ‖t‖ = 1 ∧ inner ℝ w₀ t = 0 ∧
      ∀ w v : E, ‖w‖ = 1 →
        ‖v-d‖ + 2 * ‖w-w₀‖ * ‖d‖ ≤ τ/2 →
        τ/2 ≤ |inner ℝ (perpendicularPart w t) v| := by
  have hne : perpendicularPart w₀ d ≠ 0 := by
    intro he
    rw [he, norm_zero] at hbad
    linarith
  obtain ⟨t, ht, htan, hvalue⟩ := exists_unit_tangent hw₀ d hne
  refine ⟨t, ht, htan, ?_⟩
  intro w v hw herr
  have he := (angular_phase_derivative_error hw hw₀ ht htan v d).trans herr
  rw [hvalue] at he
  have habs := abs_sub_le ‖perpendicularPart w₀ d‖
    (inner ℝ (perpendicularPart w t) v) 0
  rw [sub_zero, abs_of_nonneg (norm_nonneg _), sub_zero, abs_sub_comm] at habs
  linarith

/-- Failure of the longitudinal center test gives a radial phase
derivative bounded away from zero after the two endpoint replacements. -/
theorem longitudinal_failure_nonstationary {w₁ w₂ z₁ z₂ : E}
    (hw₁ : ‖w₁‖ = 1) (hw₂ : ‖w₂‖ = 1)
    (v₁ v₂ d₁ d₂ : E) {τ : ℝ}
    (hbad : τ < |inner ℝ z₁ d₁ + inner ℝ z₂ d₂|)
    (herr : (‖v₁-d₁‖ + ‖w₁-z₁‖ * ‖d₁‖) +
      (‖v₂-d₂‖ + ‖w₂-z₂‖ * ‖d₂‖) ≤ τ/2) :
    τ/2 ≤ |inner ℝ w₁ v₁ + inner ℝ w₂ v₂| := by
  have he₁ := longitudinal_test_error hw₁ v₁ d₁ (z := z₁)
  have he₂ := longitudinal_test_error hw₂ v₂ d₂ (z := z₂)
  have he : |(inner ℝ w₁ v₁ + inner ℝ w₂ v₂) -
      (inner ℝ z₁ d₁ + inner ℝ z₂ d₂)| ≤ τ/2 := by
    calc
      _ = |(inner ℝ w₁ v₁ - inner ℝ z₁ d₁) +
          (inner ℝ w₂ v₂ - inner ℝ z₂ d₂)| := by congr 1; ring
      _ ≤ _ := (abs_add_le _ _).trans ((add_le_add he₁ he₂).trans herr)
  have ht := abs_sub_le (inner ℝ z₁ d₁ + inner ℝ z₂ d₂)
    (inner ℝ w₁ v₁ + inner ℝ w₂ v₂) 0
  rw [sub_zero, sub_zero, abs_sub_comm] at ht
  linarith

end Falconer

end OAI
