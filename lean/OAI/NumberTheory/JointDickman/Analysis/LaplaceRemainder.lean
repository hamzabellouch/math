import OAI.NumberTheory.JointDickman.Counting.HankelGammaCoefficients

namespace OAI

/-! # A local Taylor error remains one order smaller after Laplace integration -/
namespace JointDickman
open MeasureTheory Set Filter

 theorem laplace_remainder_bound {z L C η : ℝ} (hz1 : z < 1) (hL : 0 < L)
    (hC : 0 ≤ C) (k : ℕ) (f : ℝ → ℂ)
    (hf : ∀ t ∈ Ioc 0 η, ‖f t‖ ≤ C*t^k) :
    ‖∫ t : ℝ in Ioc 0 η, (t^(-z)*Real.exp (-(L*t))) • f t‖ ≤
      C*L^(z-k-1)*Real.Gamma ((k:ℝ)+1-z) := by
  have hg := (fractional_laplace_integrable hz1 hL k).const_mul C
  have hnorm (t : ℝ) (ht : t ∈ Ioc 0 η) :
      ‖(t^(-z)*Real.exp (-(L*t))) • f t‖ ≤ C*(t^((k:ℝ)-z)*Real.exp (-(L*t))) := by
    have ht0 : 0 < t := ht.1
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
    calc
      _ ≤ (t^(-z)*Real.exp (-(L*t)))*(C*t^k) :=
        mul_le_mul_of_nonneg_left (hf t ht) (by positivity)
      _ = _ := by
        rw [← Real.rpow_natCast,show (k:ℝ)-z = -z+k by ring,Real.rpow_add ht0]
        ring
  calc
    _ ≤ ∫ t : ℝ in Ioc 0 η, C*(t^((k:ℝ)-z)*Real.exp (-(L*t))) := by
      apply norm_integral_le_of_norm_le (IntegrableOn.mono_set hg Ioc_subset_Ioi_self)
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      exact hnorm t ht
    _ ≤ ∫ t : ℝ in Ioi 0, C*(t^((k:ℝ)-z)*Real.exp (-(L*t))) := by
      apply setIntegral_mono_set hg
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        exact mul_nonneg hC (mul_nonneg (Real.rpow_nonneg ht.le _) (Real.exp_pos _).le)
      · exact Eventually.of_forall (fun _ ht => Ioc_subset_Ioi_self ht)
    _ = _ := by rw [integral_const_mul,fractional_laplace_gamma hz1 hL k]; ring

end JointDickman

end OAI
