import OAI.Geometry.RCD.Heat.KernelRowL2
import OAI.Geometry.RCD.Heat.GaussianUpperEnvelope

namespace OAI

/-! # Uniform bounds for the earlier row in a half-time heat decomposition -/

open Set MeasureTheory Metric
open scoped ENNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) [μ.Regular] (hQ : QuadraticCheegerEnergy μ)
  {ker : ℝ → X → X → ℝ}

/-- Gaussian decay may be dropped for the earlier row; a single volume
comparison transfers its normalization to the final heat scale. -/
theorem kernel_half_uniform_bound (hk : IsContinuousHeatKernel μ hQ ker)
    {C B : ℝ} (hC : 0 < C) (hB : 0 ≤ B)
    (hupper : ∀ t, 0 < t → ∀ x y, ker t x y ≤ C/μ.real (ball y (Real.sqrt t))*
      Real.exp (-dist x y^2/(5*t)+B*t))
    {t D : ℝ} (ht : 0 < t) (z : X)
    (hV : 0 < μ.real (ball z (Real.sqrt t)))
    (hVh : 0 < μ.real (ball z (Real.sqrt (t/2))))
    (hvol : μ.real (ball z (Real.sqrt t)) ≤ D*μ.real (ball z (Real.sqrt (t/2)))) :
    ∀ w, ker (t/2) z w ≤ C*D/μ.real (ball z (Real.sqrt t))*Real.exp (B*t) := by
  intro w
  rw [hk.symmetric (t/2) (half_pos ht) z w]
  apply (hupper (t/2) (half_pos ht) w z).trans
  have hcoef : C/μ.real (ball z (Real.sqrt (t/2))) ≤ C*D/μ.real (ball z (Real.sqrt t)) := by
    apply (div_le_div_iff₀ hVh hV).mpr
    nlinarith
  have he : -dist w z^2/(5*(t/2))+B*(t/2) ≤ B*t := by
    have hpos : 0 ≤ dist w z^2/(5*(t/2)) := div_nonneg (sq_nonneg _) (by positivity)
    have hb := mul_nonneg hB ht.le
    rw [neg_div]
    nlinarith
  exact mul_le_mul hcoef (Real.exp_le_exp.mpr he) (Real.exp_pos _).le (by
    have hzero : 0 ≤ C/μ.real (ball z (Real.sqrt (t/2))) := by positivity
    exact hzero.trans hcoef)

end RegularPointCoordinates

end

end OAI
