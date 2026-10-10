import OAI.NumberTheory.JointDickman.Analysis.LaplaceRemainder

namespace OAI

/-! # Integrability for the locally bounded Laplace remainders -/
namespace JointDickman
open MeasureTheory Set

 theorem laplace_weighted_integrable {z L C η : ℝ} (hz1 : z < 1) (hL : 0 < L)
    (k : ℕ) (f : ℝ → ℂ) (hf : AEStronglyMeasurable f (volume.restrict (Ioc 0 η)))
    (hbound : ∀ t ∈ Ioc 0 η, ‖f t‖ ≤ C*t^k) :
    IntegrableOn (fun t => (t^(-z)*Real.exp (-(L*t))) • f t) (Ioc 0 η) := by
  have hg : IntegrableOn (fun t : ℝ => C*(t^((k:ℝ)-z)*Real.exp (-(L*t)))) (Ioc 0 η) :=
    IntegrableOn.mono_set ((fractional_laplace_integrable hz1 hL k).const_mul C) Ioc_subset_Ioi_self
  have hw : Measurable (fun t : ℝ => t^(-z)*Real.exp (-(L*t))) := by fun_prop
  apply hg.mono' (hw.aestronglyMeasurable.smul hf)
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  have ht0 : 0 < t := ht.1
  change ‖(t^(-z)*Real.exp (-(L*t))) • f t‖ ≤ C*(t^((k:ℝ)-z)*Real.exp (-(L*t)))
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
  calc
    _ ≤ (t^(-z)*Real.exp (-(L*t)))*(C*t^k) :=
      mul_le_mul_of_nonneg_left (hbound t ht) (by positivity)
    _ = _ := by
      rw [← Real.rpow_natCast,show (k:ℝ)-z = -z+k by ring,Real.rpow_add ht0]
      ring

end JointDickman

end OAI
