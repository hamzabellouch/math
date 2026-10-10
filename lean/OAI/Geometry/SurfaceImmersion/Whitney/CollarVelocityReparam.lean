import OAI.Geometry.SurfaceImmersion.Whitney.CollarVelocityInverse
import OAI.Geometry.SurfaceImmersion.Whitney.CollarVelocityCalibration

namespace OAI

/-! The collar velocity has the desired uniform mean after reparametrization. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.CollarVelocity

def reparamX (a θ : ℝ) : ℝ := arcX a (inverseClock a θ)
def reparamY (a θ : ℝ) : ℝ := arcY a (inverseClock a θ)

lemma reparamX_smooth : ContDiff ℝ ∞ (fun z : ℝ × ℝ => reparamX z.1 z.2) :=
  arcX_smooth.comp (contDiff_fst.prodMk inverseClock_smooth)

lemma reparamY_smooth : ContDiff ℝ ∞ (fun z : ℝ × ℝ => reparamY z.1 z.2) :=
  arcY_smooth.comp (contDiff_fst.prodMk inverseClock_smooth)

lemma reparam_unit (a θ : ℝ) : reparamX a θ ^ 2 + reparamY a θ ^ 2 = 1 :=
  arc_unit a (inverseClock a θ)

lemma reparamX_periodic (a : ℝ) : Function.Periodic (reparamX a) (2 * Real.pi) := by
  intro θ
  simp only [reparamX, inverseClock_period]
  exact arcX_periodic a _

lemma reparamY_periodic (a : ℝ) : Function.Periodic (reparamY a) (2 * Real.pi) := by
  intro θ
  simp only [reparamY, inverseClock_period]
  exact arcY_periodic a _

@[simp] lemma reparamX_zero (θ : ℝ) : reparamX 0 θ = 1 := arcX_zero _
@[simp] lemma reparamY_zero (θ : ℝ) : reparamY 0 θ = 0 := arcY_zero _

lemma mean_reparam (a : ℝ) {f : ℝ → ℝ} (hf : Continuous f) :
    circleMean (fun θ => f (inverseClock a θ)) =
      circleMean (fun t => density a t * f t) := by
  have hi : Continuous (inverseClock a) :=
    (inverseClock_smooth.comp (contDiff_const.prodMk contDiff_id)).continuous
  have hd : Continuous (density a) :=
    (density_smooth.comp (contDiff_const.prodMk contDiff_id)).continuous
  have hsub := intervalIntegral.integral_comp_mul_deriv
    (a := 0) (b := 2 * Real.pi) (f := clock a) (f' := density a)
    (g := fun θ => f (inverseClock a θ))
    (fun t _ => hasDerivAt_clock a t) hd.continuousOn (hf.comp hi)
  have hend : clock a (2 * Real.pi) = 2 * Real.pi := by
    simpa using clock_period a 0
  simp only [Function.comp_apply, inverseClock_clock, clock_zero, hend] at hsub
  unfold circleMean
  rw [← hsub]
  congr 1
  apply intervalIntegral.integral_congr
  intro t _
  exact mul_comm _ _

lemma mean_reparamX (a : ℝ) :
    circleMean (reparamX a) = (1 - a ^ 2 / 2) / (1 + a ^ 2 / 2) := by
  exact (mean_reparam a
    (arcX_smooth.comp (contDiff_const.prodMk contDiff_id)).continuous).trans (mean_density_arcX a)

lemma mean_reparamY (a : ℝ) : circleMean (reparamY a) = 0 := by
  exact (mean_reparam a
    (arcY_smooth.comp (contDiff_const.prodMk contDiff_id)).continuous).trans (mean_density_arcY a)

/-- The unweighted reparametrized velocity has exactly the required mean. -/
theorem reparametrized_velocity_means {R v a : ℝ} (hR : 0 < R) (hv : 0 < v)
    (hquad : R ^ 2 = v ^ 2 + a ^ 2) :
    circleMean (fun θ => R * reparamX (amplitude R v a) θ) = v ∧
    circleMean (fun θ => R * reparamY (amplitude R v a) θ) = 0 := by
  constructor
  · rw [circleMean_const_mul]
    have h := mean_reparam (amplitude R v a) (f := arcX (amplitude R v a))
      (arcX_smooth.comp (contDiff_const.prodMk contDiff_id)).continuous
    change circleMean (reparamX (amplitude R v a)) = _ at h
    rw [h, calibrated_mean hR hv hquad]
    field_simp
  · rw [circleMean_const_mul, mean_reparamY, mul_zero]

end ClosedSurfaceR4.CollarVelocity

end

end OAI
