import OAI.NumberTheory.JointDickman.Arithmetic.DickmanDistribution
import Mathlib.MeasureTheory.Function.JacobianOneDim

namespace OAI

/-! # The Dickman integral in reciprocal cutoff coordinates -/
namespace JointDickman
open MeasureTheory Set Erdos970.NumberTheoryLean

 theorem dickman_reciprocal_integral {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) :
    Dickman.rho (1/c) = 1 - ∫ s in c..1, Dickman.rho (1/s-1)/s := by
  have hu : 1 ≤ 1/c := (le_div_iff₀ hc).mpr (by simpa using hc1)
  rw [Dickman.rho_integral hu]
  congr 1
  rw [intervalIntegral.integral_of_le hu, intervalIntegral.integral_of_le hc1,
    ← integral_Icc_eq_integral_Ioc, ← integral_Icc_eq_integral_Ioc]
  have he : (fun s : ℝ => s⁻¹) '' Icc c 1 = Icc 1 (1/c) := by
    ext t
    constructor
    · rintro ⟨s, hs, rfl⟩
      have hs0 : 0 < s := hc.trans_le hs.1
      exact ⟨by simpa only [one_div, inv_one] using (one_div_le_one_div_of_le hs0 hs.2),
        by simpa only [one_div] using one_div_le_one_div_of_le hc hs.1⟩
    · intro ht
      have ht0 : 0 < t := zero_lt_one.trans_le ht.1
      refine ⟨t⁻¹, ⟨?_, ?_⟩, inv_inv t⟩
      · have := one_div_le_one_div_of_le ht0 ht.2
        simpa only [one_div, inv_inv] using this
      · simpa only [one_div, inv_one] using one_div_le_one_div_of_le zero_lt_one ht.1
  have hj := integral_image_eq_integral_abs_deriv_smul measurableSet_Icc
    (fun s (hs : s ∈ Icc c 1) => (hasDerivAt_inv (ne_of_gt (hc.trans_le hs.1))).hasDerivWithinAt)
    inv_injective.injOn (fun t => Dickman.rho (t-1)/t)
  rw [he] at hj
  rw [hj]
  apply setIntegral_congr_fun measurableSet_Icc
  intro s hs
  have hs0 : 0 < s := hc.trans_le hs.1
  simp only [abs_neg, abs_inv, abs_of_nonneg (sq_nonneg s), smul_eq_mul, one_div]
  field_simp

end JointDickman

end OAI
