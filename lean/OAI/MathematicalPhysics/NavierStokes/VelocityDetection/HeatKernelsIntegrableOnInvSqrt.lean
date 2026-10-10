import Mathlib

namespace OAI

noncomputable section
namespace VelocityDetection.HeatKernels
open scoped BigOperators Topology ContDiff
open Set Function Filter
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ContDiff
open scoped Topology ContDiff BigOperators
open scoped Topology ContDiff ZeroAtInfty
open scoped Topology ContDiff ZeroAtInfty BigOperators
open scoped Topology

theorem integrableOn_inv_sqrt {T : ℝ} (hT : 0 ≤ T) :
    IntegrableOn (fun s : ℝ => (Real.sqrt s)⁻¹) (Ioc (0 : ℝ) T) := by
  have hi : IntegrableOn (fun s : ℝ => s ^ (-(1 / 2) : ℝ)) (Ioc (0 : ℝ) T) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).mp
      (intervalIntegral.intervalIntegrable_rpow' (by norm_num : (-1 : ℝ) < -(1 / 2)))
  apply hi.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
  rw [Real.rpow_neg hs.1.le, Real.sqrt_eq_rpow]

theorem integral_inv_sqrt {T : ℝ} (hT : 0 ≤ T) :
    (∫ s in Ioc (0 : ℝ) T, (Real.sqrt s)⁻¹) = 2 * Real.sqrt T := by
  calc
    (∫ s in Ioc (0 : ℝ) T, (Real.sqrt s)⁻¹) = ∫ s in Ioc (0 : ℝ) T, s ^ (-(1 / 2) : ℝ) := by
      apply setIntegral_congr_fun measurableSet_Ioc
      intro s hs
      change (Real.sqrt s)⁻¹ = s ^ (-(1 / 2) : ℝ)
      rw [Real.rpow_neg hs.1.le, Real.sqrt_eq_rpow]
    _ = ∫ s in (0 : ℝ)..T, s ^ (-(1 / 2) : ℝ) :=
      (intervalIntegral.integral_of_le hT).symm
    _ = 2 * Real.sqrt T := by
      rw [integral_rpow (Or.inl (by norm_num : (-1 : ℝ) < -(1 / 2)))]
      norm_num [show -(1 / 2 : ℝ) + 1 = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow]
      ring

end VelocityDetection.HeatKernels
end

end OAI
