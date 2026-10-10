import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.OscillationTests

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal NNReal

structure OriginalOscillationWitness {d : ℕ} (n : ℕ) (μ : Measure (Ambient d))
    (a : Ambient d) (r J v : ℝ) where
  direction : Ambient d
  test : Ambient d → ℝ
  lip : ℝ≥0
  direction_bound : ‖direction‖ ≤ 1
  lipschitz : LipschitzWith lip test
  lip_bound : (lip : ℝ) ≤ 1 / r
  support_subset : tsupport test ⊆ ball a (J * r)
  mean_zero : (∫ x, test x ∂μ) = 0
  large_pairing : v * r ^ n < |rieszScalarPairing n μ a (2 * (J * r)) direction test|

theorem exists_original_oscillation_witness {d : ℕ} (n : ℕ)
    (μ : Measure (Ambient d)) (a : Ambient d) (r J v : ℝ) (hr : 0 < r)
    (hfail : ¬ ScalarOscillationBound n μ a (J * r) (v * r ^ (n + 1))) :
    Nonempty (OriginalOscillationWitness n μ a r J v) := by
  classical
  unfold ScalarOscillationBound at hfail
  push Not at hfail
  obtain ⟨e, he, φ, hφ, hs, hz, hlarge⟩ := hfail
  refine ⟨{
    direction := e
    test := fun x => r⁻¹ * φ x
    lip := ‖r⁻¹‖₊
    direction_bound := he
    lipschitz := by simpa only [mul_one] using! lipschitz_const_mul_real hφ r⁻¹
    lip_bound := by simp only [coe_nnnorm, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr), one_div, le_refl]
    support_subset := tsupport_mul_subset_right.trans hs
    mean_zero := by rw [integral_const_mul, hz, mul_zero]
    large_pairing := ?_
  }⟩
  rw [rieszScalarPairing_const_mul, abs_mul, abs_of_pos (inv_pos.mpr hr)]
  have hm := mul_lt_mul_of_pos_left hlarge (inv_pos.mpr hr)
  have hid : r⁻¹ * (v * r ^ (n + 1)) = v * r ^ n := by
    rw [pow_succ]
    field_simp
  simpa only [hid] using! hm

def originalOscillationWitnessOfFailure {d : ℕ} (n : ℕ) (μ : Measure (Ambient d))
    (a : Ambient d) (r J v : ℝ) (hr : 0 < r)
    (hfail : ¬ ScalarOscillationBound n μ a (J * r) (v * r ^ (n + 1))) :
    OriginalOscillationWitness n μ a r J v :=
  Classical.choice (exists_original_oscillation_witness n μ a r J v hr hfail)

end

end RieszRectifiability

end OAI
