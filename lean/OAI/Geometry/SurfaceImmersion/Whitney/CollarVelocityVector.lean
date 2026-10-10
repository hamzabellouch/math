import OAI.Geometry.SurfaceImmersion.Whitney.CollarVelocityPeriod
import OAI.Geometry.SurfaceImmersion.Primitive.VelocityPlane

namespace OAI

/-! The actual collar velocity in an orthonormal frame of the velocity plane. -/
noncomputable section

namespace ClosedSurfaceR4.CollarVelocity
open CovarianceCorrector
open VelocityPlane (Space)

def vectorLoop (e₁ e₂ : Space) (R v a : ℝ) : C(Period, Space) :=
  ⟨fun t => (R * loopX (amplitude R v a) t) • e₁ +
      (R * loopY (amplitude R v a) t) • e₂,
    (((loopX (amplitude R v a)).continuous.const_mul R).smul continuous_const).add
      (((loopY (amplitude R v a)).continuous.const_mul R).smul continuous_const)⟩

lemma vectorLoop_average (e₁ e₂ : Space) {R v a : ℝ}
    (hR : 0 < R) (hv : 0 < v) (hquad : R ^ 2 = v ^ 2 + a ^ 2) :
    average (vectorLoop e₁ e₂ R v a) = v • e₁ := by
  change average (fun t => (R * loopX (amplitude R v a) t) • e₁ +
    (R * loopY (amplitude R v a) t) • e₂) = _
  rw [average_add
    (f := fun t => (R * loopX (amplitude R v a) t) • e₁)
    (g := fun t => (R * loopY (amplitude R v a) t) • e₂)
    (((loopX (amplitude R v a)).continuous.const_mul R).smul continuous_const)
    (((loopY (amplitude R v a)).continuous.const_mul R).smul continuous_const)]
  rw [average_smul_const, average_smul_const]
  rw [show average (fun t => R * loopX (amplitude R v a) t) =
    R * average (loopX (amplitude R v a)) from average_const_smul R _,
    show average (fun t => R * loopY (amplitude R v a) t) =
    R * average (loopY (amplitude R v a)) from average_const_smul R _]
  rw [average_calibrated_loopX hR hv hquad, average_loopY, mul_zero, zero_smul, add_zero]
  congr 1
  field_simp

lemma vectorLoop_norm_sq {e₁ e₂ : Space} (h₁ : ‖e₁‖ = 1) (h₂ : ‖e₂‖ = 1)
    (horth : inner ℝ e₁ e₂ = 0) (R v a : ℝ) (t : Period) :
    ‖vectorLoop e₁ e₂ R v a t‖ ^ 2 = R ^ 2 := by
  have h₁' : inner ℝ e₁ e₁ = 1 := by rw [real_inner_self_eq_norm_sq, h₁, one_pow]
  have h₂' : inner ℝ e₂ e₂ = 1 := by rw [real_inner_self_eq_norm_sq, h₂, one_pow]
  have horth' : inner ℝ e₂ e₁ = 0 := (real_inner_comm _ _).trans horth
  rw [← real_inner_self_eq_norm_sq]
  change inner ℝ ((R * loopX (amplitude R v a) t) • e₁ +
    (R * loopY (amplitude R v a) t) • e₂)
    ((R * loopX (amplitude R v a) t) • e₁ +
    (R * loopY (amplitude R v a) t) • e₂) = _
  simp only [inner_add_left, inner_add_right, real_inner_smul_left,
    real_inner_smul_right, h₁', h₂', horth, horth', mul_zero, zero_add, add_zero, mul_one]
  calc
    _ = R ^ 2 * (loopX (amplitude R v a) t ^ 2 + loopY (amplitude R v a) t ^ 2) := by ring
    _ = R ^ 2 := by rw [loop_unit, mul_one]

lemma vectorLoop_mem (P : Submodule ℝ Space) {e₁ e₂ : Space}
    (h₁ : e₁ ∈ P) (h₂ : e₂ ∈ P) (R v a : ℝ) (t : Period) :
    vectorLoop e₁ e₂ R v a t ∈ P :=
  P.add_mem (P.smul_mem _ h₁) (P.smul_mem _ h₂)

/-- The collar loop gives the exact leading metric required by the primitive addition. -/
theorem vectorLoop_leading_metric {X Y C e₁ e₂ : Space} {R v a : ℝ}
    (h₁ : ‖e₁‖ = 1) (h₂ : ‖e₂‖ = 1) (horth : inner ℝ e₁ e₂ = 0)
    (hp₁ : e₁ ∈ VelocityPlane.velocityPlane Y C)
    (hp₂ : e₂ ∈ VelocityPlane.velocityPlane Y C)
    (hproj : (VelocityPlane.velocityPlane Y C).starProjection X = v • e₁)
    (hquad : R ^ 2 = v ^ 2 + a ^ 2) (t : Period) :
    ‖X - v • e₁ + vectorLoop e₁ e₂ R v a t‖ ^ 2 = ‖X‖ ^ 2 + a ^ 2 ∧
      inner ℝ (X - v • e₁ + vectorLoop e₁ e₂ R v a t) Y = inner ℝ X Y := by
  have hn : ‖(VelocityPlane.velocityPlane Y C).starProjection X‖ ^ 2 = v ^ 2 := by
    rw [hproj, norm_smul, h₁, mul_one, Real.norm_eq_abs, sq_abs]
  have hm := VelocityPlane.leading_metric (a := a)
    (vectorLoop_mem _ hp₁ hp₂ R v a t)
    (by rw [vectorLoop_norm_sq h₁ h₂ horth, hn, hquad])
  simpa only [hproj] using hm

lemma vectorLoop_zero_amplitude (e₁ e₂ : Space) (R v : ℝ) (t : Period) :
    vectorLoop e₁ e₂ R v 0 t = R • e₁ := by
  simp [vectorLoop, amplitude]

end ClosedSurfaceR4.CollarVelocity

end

end OAI
