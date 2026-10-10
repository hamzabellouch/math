import OAI.Analysis.Mahler.HemisphereJacobian
import OAI.Analysis.Mahler.PunctureCutoff

namespace OAI

noncomputable section
open Set MeasureTheory
namespace MahlerStokes

lemma smul_coordBall_unit {n : ℕ} {r : ℝ} (hr : 0 < r) :
    (fun x : Fin n → ℝ => r • x) '' coordBall n 1 = coordBall n r := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    change radiusSq (r • x) < r^2
    rw [radiusSq_smul]
    have hh : radiusSq x < 1 := by simpa [coordBall] using hx
    nlinarith [sq_pos_of_pos hr]
  · intro hy
    refine ⟨r⁻¹ • y, ?_, by simp [smul_smul, hr.ne']⟩
    change radiusSq (r⁻¹ • y) < 1^2
    rw [radiusSq_smul, inv_pow, inv_mul_eq_div, one_pow]
    exact (div_lt_one (sq_pos_of_pos hr)).2 hy

/-- Positive dilation of the actual coordinate Lebesgue integral. -/
theorem setIntegral_coordBall_scale {n : ℕ} {r : ℝ} (hr : 0 < r)
    (f : (Fin n → ℝ) → ℝ) :
    (∫ y in coordBall n r, f y) = r^n * ∫ x in coordBall n 1, f (r • x) := by
  rw [← smul_coordBall_unit hr]
  have hd (x : Fin n → ℝ) : HasFDerivAt (fun x : Fin n → ℝ => r • x)
      (r • ContinuousLinearMap.id ℝ (Fin n → ℝ)) x := (hasFDerivAt_id x).const_smul r
  rw [integral_image_eq_integral_abs_det_fderiv_smul volume (measurableSet_coordBall n 1)
    (fun x _ => (hd x).hasFDerivWithinAt) (by
      intro x _ y _ h
      exact (smul_right_injective _ hr.ne') h)]
  have he : (r • ContinuousLinearMap.id ℝ (Fin n → ℝ)).det = r^n := by
    change LinearMap.det (r • LinearMap.id) = _
    rw [LinearMap.det_smul]
    simp
  simp only [he, abs_of_pos (pow_pos hr n), smul_eq_mul]
  exact integral_const_mul _ _

lemma chord_pos_scale {n : ℕ} {r : ℝ} (hr : 0 < r) (y : Fin n → ℝ) :
    chord r (r • y) = r * chord 1 y := by
  unfold chord
  rw [radiusSq_smul]
  have he : r^2-r^2*radiusSq y = r^2*(1^2-radiusSq y) := by ring
  rw [he, Real.sqrt_mul (sq_nonneg r), Real.sqrt_sq_eq_abs, abs_of_pos hr]

lemma insertNth_smul_boundary {n : ℕ} (i : Fin (n+1)) (r t : ℝ) (y : Fin n → ℝ) :
    i.insertNth (r*t) (r • y) = r • i.insertNth t y := by
  apply funext
  rw [i.forall_iff_succAbove]
  constructor
  · simp
  · intro j; simp

/-- Radius scaling of the coordinate sphere flux, without exterior
algebra or flux-form identities. -/
theorem sphereFlux_pos_scale {n : ℕ} {r : ℝ} (hr : 0 < r)
    (ω : (Fin (n+1) → ℝ) → (Fin (n+1) → ℝ) [⋀^Fin n]→L[ℝ] ℝ) :
    sphereFlux r ω = r^n * sphereFlux 1 (fun x => ω (r • x)) := by
  unfold sphereFlux
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [setIntegral_coordBall_scale hr]
  rw [mul_left_comm]
  congr 2
  apply setIntegral_congr_fun (measurableSet_coordBall n 1)
  intro y _
  dsimp only
  rw [chord_pos_scale hr, insertNth_smul_boundary, ← mul_neg, insertNth_smul_boundary]

end MahlerStokes

end

end OAI
