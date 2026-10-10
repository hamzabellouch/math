import OAI.Geometry.CylinderCovering.Nilpotent.ProfileDefinitions

namespace OAI

noncomputable section
open Set
namespace CylinderCovering.Nilpotent.Profile
open RuledApproximation

@[simp] theorem derivative_apply (dv dw p t : ℝ) (z : Plane) :
    derivative dv dw p t z = (t⁻¹ * (z 0 - p * z 1)) • vec2 dv dw := by
  simp [derivative]

theorem field_on_ray (v w : ℝ → ℝ) (p t : ℝ) (ht : t ≠ 0) :
    field v w (vec2 (p * t) t) = vec2 (v p) (w p) := by
  simp [field, vec2, ht]

private theorem angle_hasFDerivAt (p t : ℝ) (ht : t ≠ 0) :
    HasFDerivAt (fun b : Plane => b 0 / b 1)
      (t⁻¹ • (EuclideanSpace.proj 0 - p • EuclideanSpace.proj 1 : Plane →L[ℝ] ℝ))
      (vec2 (p * t) t) := by
  let P : Plane →L[ℝ] ℝ := EuclideanSpace.proj 0
  let Q : Plane →L[ℝ] ℝ := EuclideanSpace.proj 1
  have hp := P.hasFDerivAt (x := vec2 (p * t) t)
  have hq := Q.hasFDerivAt (x := vec2 (p * t) t)
  have h := hp.mul ((hasDerivAt_inv ht).comp_hasFDerivAt (vec2 (p * t) t) hq)
  convert! h using 1
  ext z
  simp [P, Q, vec2]
  field_simp [ht]
  ring

theorem field_hasFDerivAt {v w : ℝ → ℝ} {dv dw p t : ℝ}
    (hv : HasDerivAt v dv p) (hw : HasDerivAt w dw p) (ht : t ≠ 0) :
    HasFDerivAt (field v w) (derivative dv dw p t) (vec2 (p * t) t) := by
  have hang := angle_hasFDerivAt p t ht
  have hv' : HasDerivAt v dv ((vec2 (p * t) t : Plane) 0 /
      (vec2 (p * t) t : Plane) 1) := by simpa [vec2, ht] using hv
  have hw' : HasDerivAt w dw ((vec2 (p * t) t : Plane) 0 /
      (vec2 (p * t) t : Plane) 1) := by simpa [vec2, ht] using hw
  have hf := hv'.comp_hasFDerivAt (vec2 (p * t) t) hang
  have hg := hw'.comp_hasFDerivAt (vec2 (p * t) t) hang
  have hpair := (hf.smul_const (vec2 1 0)).add (hg.smul_const (vec2 0 1))
  convert! hpair using 1
  · funext b
    ext i
    fin_cases i <;> simp [field, vec2]
  · ext z i
    fin_cases i <;> simp [derivative, vec2] <;> ring

theorem derivative_square_zero {dv dw p t : ℝ} (halign : dv = p * dw) :
    (derivative dv dw p t).comp (derivative dv dw p t) = 0 := by
  ext z i
  fin_cases i <;> simp [derivative, vec2, halign]

theorem field_fderiv_square_zero {v w : ℝ → ℝ} {dv dw p t : ℝ}
    (hv : HasDerivAt v dv p) (hw : HasDerivAt w dw p) (ht : t ≠ 0)
    (halign : dv = p * dw) :
    (fderiv ℝ (field v w) (vec2 (p * t) t)).comp
      (fderiv ℝ (field v w) (vec2 (p * t) t)) = 0 := by
  rw [(field_hasFDerivAt hv hw ht).fderiv]
  exact derivative_square_zero halign

theorem tangentAt_iff (v w : ℝ → ℝ) (p : ℝ) :
    TangentAt v w p ↔ v p = p * w p := by
  constructor
  · rintro ⟨μ, hμ⟩
    have h0 := congrArg (fun z : Plane => z 0) hμ
    have h1 := congrArg (fun z : Plane => z 1) hμ
    simp [vec2] at h0 h1
    rw [h0, h1, mul_comm]
  · intro h
    refine ⟨w p, ?_⟩
    ext i
    fin_cases i <;> simp [vec2, h, mul_comm]

theorem quadratic_hasDerivAt (c p : ℝ) :
    HasDerivAt (fun q : ℝ => c / 2 * (1 + q ^ 2)) (c * p) p := by
  convert! (((hasDerivAt_id p).pow 2).const_add 1).const_mul (c / 2) using 1
  simp only [id_eq]
  ring

theorem linear_hasDerivAt (c p : ℝ) :
    HasDerivAt (fun q : ℝ => c * q) c p := by
  simpa using (hasDerivAt_id p).const_mul c

theorem quadratic_boundary_tangent (c : ℝ) :
    TangentAt (fun p => c / 2 * (1 + p ^ 2)) (fun p => c * p) (-1) ∧
    TangentAt (fun p => c / 2 * (1 + p ^ 2)) (fun p => c * p) 1 := by
  constructor <;> rw [tangentAt_iff] <;> ring

theorem quadratic_unique {V : ℝ → ℝ} {c : ℝ}
    (hV : ∀ p ∈ Icc (-1 : ℝ) 1, HasDerivAt V (c * p) p)
    (hwall : V (-1) = c) :
    ∀ p ∈ Icc (-1 : ℝ) 1, V p = c / 2 * (1 + p ^ 2) := by
  apply eq_of_has_deriv_right_eq
    (fun p hp => (hV p (mem_Icc_of_Ico hp)).hasDerivWithinAt)
    (fun p _ => (quadratic_hasDerivAt c p).hasDerivWithinAt)
    (fun p hp => (hV p hp).continuousAt.continuousWithinAt)
    (by fun_prop)
  calc
    V (-1) = c := hwall
    _ = c / 2 * (1 + (-1 : ℝ) ^ 2) := by ring

theorem source_profiles (p : ℝ) :
    (1 / 2 : ℝ) / 2 * (1 + p ^ 2) = Nilpotent.v p ∧
    (1 / 2 : ℝ) * p = Nilpotent.w p := by
  constructor <;> simp [Nilpotent.v, Nilpotent.w] <;> ring

end CylinderCovering.Nilpotent.Profile

end

end OAI
