import OAI.MeasureTheory.Falconer.Geometry.InactiveBinGeometry

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff

theorem periodic_sourceAngle_value {E : Type*} {f : ℝ → E}
    (hf : Function.Periodic f (2*Real.pi)) (θ : ℝ) :
    f (sourceAngle (sourceUnitDirection θ)) = f θ := by
  rw [sourceAngle_sourceUnitDirection]
  have he := Complex.arg_cos_add_sin_mul_I_sub θ
  simp only [← Complex.ofReal_cos, ← Complex.ofReal_sin] at he
  rw [sub_eq_iff_eq_add] at he
  rw [he]
  have hp := hf.int_mul ⌊(Real.pi-θ)/(2*Real.pi)⌋
  simpa only [mul_comm, add_comm] using hp θ

noncomputable def sourceCircleRotate (axis : ℝ) (dir : UnitCircle) : UnitCircle :=
  sourceUnitDirection (sourceAngle dir + axis)

theorem sourceCircleRotate_comp (axis θ : ℝ) :
    sourceCircleRotate axis (sourceUnitDirection θ) = sourceUnitDirection (θ+axis) := by
  exact periodic_sourceAngle_value (f := fun t => sourceUnitDirection (t+axis))
    (fun t => by simpa only [add_right_comm] using sourceUnitDirection_periodic (t+axis)) θ

theorem sourceCircleRotate_dist (axis : ℝ) (dir eta : UnitCircle) :
    dist (sourceCircleRotate axis dir) (sourceCircleRotate axis eta) = dist dir eta := by
  rw [← sourceUnitDirection_sourceAngle dir, ← sourceUnitDirection_sourceAngle eta,
    sourceCircleRotate_comp, sourceCircleRotate_comp]
  have h₁ := sourceUnitDirection_dist_sq (sourceAngle dir+axis) (sourceAngle eta+axis)
  have h₂ := sourceUnitDirection_dist_sq (sourceAngle dir) (sourceAngle eta)
  rw [show sourceAngle dir+axis-(sourceAngle eta+axis) = sourceAngle dir-sourceAngle eta by ring] at h₁
  nlinarith [dist_nonneg (x := sourceUnitDirection (sourceAngle dir+axis))
    (y := sourceUnitDirection (sourceAngle eta+axis)),
    dist_nonneg (x := sourceUnitDirection (sourceAngle dir)) (y := sourceUnitDirection (sourceAngle eta))]

theorem sourceCircleRotate_isometry (axis : ℝ) : Isometry (sourceCircleRotate axis) :=
  Isometry.of_dist_eq (sourceCircleRotate_dist axis)

theorem sourceCircleRotate_add (a b : ℝ) (dir : UnitCircle) :
    sourceCircleRotate a (sourceCircleRotate b dir) = sourceCircleRotate (b+a) dir := by
  change sourceCircleRotate a (sourceUnitDirection (sourceAngle dir+b)) = _
  rw [sourceCircleRotate_comp]
  simp only [sourceCircleRotate, add_assoc]

@[simp] theorem sourceCircleRotate_zero (dir : UnitCircle) : sourceCircleRotate 0 dir = dir := by
  simp only [sourceCircleRotate, add_zero, sourceUnitDirection_sourceAngle]

noncomputable def sourceCircleRotation (axis : ℝ) : UnitCircle ≃ₜ UnitCircle where
  toFun := sourceCircleRotate axis
  invFun := sourceCircleRotate (-axis)
  left_inv dir := by rw [sourceCircleRotate_add, add_neg_cancel, sourceCircleRotate_zero]
  right_inv dir := by rw [sourceCircleRotate_add, neg_add_cancel, sourceCircleRotate_zero]
  continuous_toFun := (sourceCircleRotate_isometry axis).continuous
  continuous_invFun := (sourceCircleRotate_isometry (-axis)).continuous

theorem sourceCircleRotate_integral (axis : ℝ) {F : UnitCircle → ℂ} (hF : Measurable F) :
    (∫ dir, F (sourceCircleRotate axis dir) ∂sourceArcLength) = ∫ dir, F dir ∂sourceArcLength := by
  change (∫ dir, (F ∘ sourceCircleRotate axis) dir ∂sourceArcLength) = _
  rw [sourceArcLength_integral_period
    (hF.comp (sourceCircleRotate_isometry axis).continuous.measurable).aestronglyMeasurable,
    sourceArcLength_integral_period hF.aestronglyMeasurable]
  simp only [Function.comp_def, sourceCircleRotate_comp]
  rw [intervalIntegral.integral_comp_add_right (fun θ => F (sourceUnitDirection θ))]
  have hp : Function.Periodic (fun θ => F (sourceUnitDirection θ)) (2*Real.pi) :=
    fun θ => congrArg F (sourceUnitDirection_periodic θ)
  have hh := hp.intervalIntegral_add_eq (-Real.pi+axis) (-Real.pi)
  convert hh using 1 <;> congr 1 <;> ring

theorem sourceCircleRotate_deriv (axis : ℝ) (f : UnitCircle → ℂ) (j : ℕ) (θ : ℝ) :
    iteratedDeriv j (fun t => f (sourceCircleRotate axis (sourceUnitDirection t))) θ =
      iteratedDeriv j (fun t => f (sourceUnitDirection t)) (θ+axis) := by
  simp only [sourceCircleRotate_comp]
  exact congrFun (iteratedDeriv_comp_add_const j (fun t => f (sourceUnitDirection t)) axis) θ

theorem sourceCircleRotate_contDiff (axis : ℝ) {f : UnitCircle → ℂ}
    (hf : ContDiff ℝ ∞ (fun θ => f (sourceUnitDirection θ))) :
    ContDiff ℝ ∞ (fun θ => f (sourceCircleRotate axis (sourceUnitDirection θ))) := by
  simpa only [sourceCircleRotate_comp, Function.comp_def, id_eq] using hf.comp (contDiff_id.add contDiff_const)

theorem sourceCircleRotate_tsupport (axis : ℝ) (f : UnitCircle → ℂ) :
    tsupport (fun dir => f (sourceCircleRotate axis dir)) =
      sourceCircleRotate axis ⁻¹' tsupport f :=
  tsupport_comp_eq_preimage f (sourceCircleRotation axis)

end PlanarFalconer

end OAI
