import OAI.Analysis.CircleDomains.Sobolev.L2ProductConvergence
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

namespace OAI

/-! Summable L² errors give summable weighted integrals by the fixed
L² gradient in scalar coarea. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem lintegral_norm_mul_le_L2
    {X : Type*} [MeasurableSpace X] {μ : Measure X} {f g : X → ℝ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    (∫⁻ p, ENNReal.ofReal ‖f p‖*ENNReal.ofReal ‖g p‖ ∂μ) ≤
      ENNReal.ofReal ((eLpNorm f 2 μ).toReal*(eLpNorm g 2 μ).toReal) := by
  simp_rw [← ENNReal.ofReal_mul (norm_nonneg _)]
  have hi := ofReal_integral_eq_lintegral_ofReal (hf.norm.integrable_mul hg.norm)
    (Eventually.of_forall (fun p => mul_nonneg (norm_nonneg (f p)) (norm_nonneg (g p))))
  simp only [Pi.mul_apply] at hi
  rw [← hi]
  apply ENNReal.ofReal_le_ofReal
  calc
    (∫ p, ‖f p‖*‖g p‖ ∂μ) ≤ |∫ p, ‖f p‖*‖g p‖ ∂μ| := le_abs_self _
    _ ≤ _ := by
      simpa only [eLpNorm_norm _ hf.aestronglyMeasurable,
        eLpNorm_norm _ hg.aestronglyMeasurable] using
        abs_integral_mul_le_eLpNorm_two hf.norm hg.norm

 theorem weighted_L2_errors_summable
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (f : ℕ → X → ℝ) {g : X → ℝ}
    (hf : ∀ n, MemLp (f n) 2 μ) (hg : MemLp g 2 μ)
    (hs : Summable (fun n => (eLpNorm (f n) 2 μ).toReal)) :
    (∑' n, ∫⁻ p, ENNReal.ofReal ‖f n p‖*ENNReal.ofReal ‖g p‖ ∂μ) < ∞ := by
  exact lt_of_le_of_lt (ENNReal.tsum_le_tsum (fun n => lintegral_norm_mul_le_L2 (hf n) hg))
    (hs.mul_right (eLpNorm g 2 μ).toReal).tsum_ofReal_lt_top

end CircleDomainRigidity

end

end OAI
