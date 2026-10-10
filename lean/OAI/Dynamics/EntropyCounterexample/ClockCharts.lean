import OAI.Dynamics.EntropyCounterexample.Definitions

namespace OAI

noncomputable section
open scoped ContDiff

namespace Problem340

def complexClockLinearIsometry : ℂ ≃ₗᵢ[ℝ] ClockAmbient :=
  Complex.orthonormalBasisOneI.repr

@[simp]
theorem complexClockLinearIsometry_apply (z : ℂ) :
    complexClockLinearIsometry z = ![z.re, z.im] := rfl

def circleClockHomeomorph : Circle ≃ₜ StandardClock :=
  complexClockLinearIsometry.toHomeomorph.subtype fun z => by
    change z ∈ Metric.sphere (0 : ℂ) 1 ↔
      complexClockLinearIsometry z ∈ Metric.sphere (0 : ClockAmbient) 1
    simp only [Metric.mem_sphere, dist_zero_right,
      complexClockLinearIsometry.norm_map]

@[simp]
theorem circleClockHomeomorph_coe (z : Circle) :
    (circleClockHomeomorph z).1 = complexClockLinearIsometry (z : ℂ) := rfl

def clockHomeomorph : AddCircle (100 : ℝ) ≃ₜ StandardClock :=
  (AddCircle.homeomorphCircle (by norm_num : (100 : ℝ) ≠ 0)).trans
    circleClockHomeomorph

@[simp]
theorem clockHomeomorph_apply (t : AddCircle (100 : ℝ)) :
    clockHomeomorph t = circleClockHomeomorph (AddCircle.toCircle t) := by
  simp only [clockHomeomorph, Homeomorph.trans_apply, AddCircle.homeomorphCircle_apply]

def clockParam (t : ℝ) : ClockAmbient :=
  complexClockLinearIsometry (Complex.exp ((2 * Real.pi / 100 * t : ℝ) * Complex.I))

@[simp]
theorem clockHomeomorph_coe (t : ℝ) :
    (clockHomeomorph (t : AddCircle (100 : ℝ))).1 = clockParam t := by
  simp only [clockHomeomorph_apply, circleClockHomeomorph_coe,
    AddCircle.toCircle_apply_mk, Circle.coe_exp, clockParam]

theorem contDiff_clockParam {n : ℕ∞ω} : ContDiff ℝ n clockParam := by
  unfold clockParam
  apply complexClockLinearIsometry.toContinuousLinearEquiv.contDiff.comp
  exact ((Complex.ofRealCLM.contDiff.comp (contDiff_const.mul contDiff_id)).mul
    contDiff_const).cexp

theorem clockParam_periodic : Function.Periodic clockParam 100 := by
  intro t
  rw [← clockHomeomorph_coe, ← clockHomeomorph_coe]
  congr 2
  exact AddCircle.coe_add_period 100 t

def ambientClockRotate (s : ℝ) (x : ClockAmbient) : ClockAmbient :=
  complexClockLinearIsometry
    (Complex.exp ((2 * Real.pi / 100 * s : ℝ) * Complex.I) *
      complexClockLinearIsometry.symm x)

theorem contDiff_ambientClockRotate {n : ℕ∞ω} :
    ContDiff ℝ n (fun p : ℝ × ClockAmbient => ambientClockRotate p.1 p.2) := by
  unfold ambientClockRotate
  apply complexClockLinearIsometry.toContinuousLinearEquiv.contDiff.comp
  apply ContDiff.mul
  · exact ((Complex.ofRealCLM.contDiff.comp (contDiff_const.mul contDiff_fst)).mul
      contDiff_const).cexp
  · exact complexClockLinearIsometry.symm.toContinuousLinearEquiv.contDiff.comp contDiff_snd

def clockRotate (s : ℝ) (x : StandardClock) : StandardClock :=
  ⟨ambientClockRotate s x.1, by
    apply mem_sphere_zero_iff_norm.mpr
    simp only [ambientClockRotate, complexClockLinearIsometry.norm_map, norm_mul,
      complexClockLinearIsometry.symm.norm_map]
    have hphase : ‖Complex.exp ((2 * Real.pi / 100 * s : ℝ) * Complex.I)‖ = 1 := by
      simp [Complex.norm_exp]
    rw [hphase, one_mul]
    exact mem_sphere_zero_iff_norm.mp x.2⟩

theorem clockHomeomorph_add (t : AddCircle (100 : ℝ)) (s : ℝ) :
    clockHomeomorph (t + (s : AddCircle (100 : ℝ))) =
      clockRotate s (clockHomeomorph t) := by
  apply Subtype.ext
  simp only [clockHomeomorph_apply, circleClockHomeomorph_coe,
    AddCircle.toCircle_add, Circle.coe_mul, AddCircle.toCircle_apply_mk,
    Circle.coe_exp, clockRotate, ambientClockRotate,
    LinearIsometryEquiv.symm_apply_apply]
  rw [mul_comm]

end Problem340

end

end OAI
