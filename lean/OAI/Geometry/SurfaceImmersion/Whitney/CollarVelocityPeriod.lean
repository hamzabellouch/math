import OAI.Geometry.SurfaceImmersion.Whitney.CollarVelocityReparam
import OAI.Geometry.SurfaceImmersion.Correction.SmoothPeriodicCalculus

namespace OAI

/-! Convert the explicit collar arc to the unit period used by the corrector. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.CollarVelocity
open CovarianceCorrector SmoothPeriodicCalculus

def unitX (a t : ℝ) : ℝ := reparamX a (2 * Real.pi * t)
def unitY (a t : ℝ) : ℝ := reparamY a (2 * Real.pi * t)

lemma unitX_smooth : ContDiff ℝ ∞ (fun z : ℝ × ℝ => unitX z.1 z.2) :=
  reparamX_smooth.comp (contDiff_fst.prodMk (contDiff_const.mul contDiff_snd))

lemma unitY_smooth : ContDiff ℝ ∞ (fun z : ℝ × ℝ => unitY z.1 z.2) :=
  reparamY_smooth.comp (contDiff_fst.prodMk (contDiff_const.mul contDiff_snd))

lemma unitX_periodic (a : ℝ) : Function.Periodic (unitX a) 1 := by
  intro t
  unfold unitX
  rw [mul_add, mul_one]
  exact reparamX_periodic a _

lemma unitY_periodic (a : ℝ) : Function.Periodic (unitY a) 1 := by
  intro t
  unfold unitY
  rw [mul_add, mul_one]
  exact reparamY_periodic a _

def loopX (a : ℝ) : C(Period, ℝ) :=
  bundle (unitX a) (unitX_periodic a)
    ((unitX_smooth.comp (contDiff_const.prodMk contDiff_id)).continuous)

def loopY (a : ℝ) : C(Period, ℝ) :=
  bundle (unitY a) (unitY_periodic a)
    ((unitY_smooth.comp (contDiff_const.prodMk contDiff_id)).continuous)

@[simp] lemma loopX_apply (a t : ℝ) : loopX a (t : Period) = unitX a t := rfl
@[simp] lemma loopY_apply (a t : ℝ) : loopY a (t : Period) = unitY a t := rfl

lemma integral_rescale (f : ℝ → ℝ) :
    (∫ t in 0..1, f (2 * Real.pi * t)) = circleMean f := by
  rw [intervalIntegral.integral_comp_mul_left f (by positivity)]
  simp only [mul_zero, mul_one, smul_eq_mul, circleMean]

lemma average_loopX (a : ℝ) :
    average (loopX a) = (1 - a ^ 2 / 2) / (1 + a ^ 2 / 2) := by
  rw [average, ← PeriodicPrimitive.integral_lift_eq_haar]
  change (∫ t in 0..1, reparamX a (2 * Real.pi * t)) = _
  rw [integral_rescale, mean_reparamX]

lemma average_loopY (a : ℝ) : average (loopY a) = 0 := by
  rw [average, ← PeriodicPrimitive.integral_lift_eq_haar]
  change (∫ t in 0..1, reparamY a (2 * Real.pi * t)) = _
  rw [integral_rescale, mean_reparamY]

lemma average_calibrated_loopX {R v a : ℝ} (hR : 0 < R) (hv : 0 < v)
    (hquad : R ^ 2 = v ^ 2 + a ^ 2) :
    average (loopX (amplitude R v a)) = v / R := by
  rw [average_loopX, ← mean_density_arcX]
  exact calibrated_mean hR hv hquad

lemma loop_unit (a : ℝ) (t : Period) : loopX a t ^ 2 + loopY a t ^ 2 = 1 := by
  induction t using QuotientAddGroup.induction_on
  exact reparam_unit a _

@[simp] lemma loopX_zero (t : Period) : loopX 0 t = 1 := by
  induction t using QuotientAddGroup.induction_on
  exact reparamX_zero _

@[simp] lemma loopY_zero (t : Period) : loopY 0 t = 0 := by
  induction t using QuotientAddGroup.induction_on
  exact reparamY_zero _

end ClosedSurfaceR4.CollarVelocity

end

end OAI
