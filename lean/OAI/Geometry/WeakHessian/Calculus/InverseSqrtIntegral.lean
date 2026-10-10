import Mathlib

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile145
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory
open scoped Topology

lemma inv_sqrt_eq_rpow {s : ℝ} (hs : 0 ≤ s) : (Real.sqrt s)⁻¹ = s ^ (-(1/2:ℝ)) := by
  rw [Real.rpow_neg hs,Real.sqrt_eq_rpow]

lemma integrableOn_inv_sqrt {b : ℝ} (hb : 0 ≤ b) :
    IntegrableOn (fun s : ℝ => (Real.sqrt s)⁻¹) (Ioc 0 b) volume := by
  have integrablePower := (intervalIntegrable_iff_integrableOn_Ioc_of_le hb).mp
    (intervalIntegral.intervalIntegrable_rpow' (show (-1:ℝ)< -(1/2:ℝ) by norm_num))
  apply integrablePower.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
  exact (inv_sqrt_eq_rpow hs.1.le).symm

lemma integral_inv_sqrt {b : ℝ} (hb : 0 ≤ b) :
    (∫ s in Ioc 0 b,(Real.sqrt s)⁻¹) = 2*Real.sqrt b := by
  calc
    _ = ∫ s in Ioc 0 b,s ^ (-(1/2:ℝ)) := by
      apply setIntegral_congr_fun measurableSet_Ioc
      intro s hs
      exact inv_sqrt_eq_rpow hs.1.le
    _ = ∫ s in (0:ℝ)..b,s ^ (-(1/2:ℝ)) := (intervalIntegral.integral_of_le hb).symm
    _ = _ := by
      rw [integral_rpow (Or.inl (by norm_num : (-1:ℝ)< -(1/2:ℝ)))]
      norm_num [Real.sqrt_eq_rpow]
      ring
end WeakHessian

end
end InlinedFile145

end OAI
