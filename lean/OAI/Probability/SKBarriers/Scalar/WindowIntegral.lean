import Mathlib
import OAI.Probability.SKBarriers.Gaussian.FiberLipschitzTent

namespace OAI

section

noncomputable section
open scoped NNReal Topology
open MeasureTheory Filter
namespace SK.Analytic

theorem scalarWindow_integral_tendsto {E : Type} [MeasurableSpace E]
    {μ : Measure E} {g : ℝ → ℝ} {M : ℝ≥0} (hg : LipschitzWith M g)
    (hb : ∀ y, |g y|≤1) {L : E → ℝ} (hL : Measurable L)
    {w : E → ℝ} (hw : Integrable w μ) :
    Tendsto (fun k : ℕ => ∫ z, w z*scalarWindow g (1/((k:ℝ)+1)) (L z) ∂μ)
      atTop (𝓝 (∫ z, w z*g (L z) ∂μ)) := by
  let h : ℕ → ℝ := fun k => 1/((k:ℝ)+1)
  have hh (k) : 0<h k := by dsimp [h]; positivity
  have ht : Tendsto h atTop (𝓝 0) := by simpa using tendsto_one_div_add_atTop_nhds_zero_nat
  have hlim (z) : Tendsto (fun k => scalarWindow g (h k) (L z)) atTop (𝓝 (g (L z))) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le
      (show Tendsto (fun k => g (L z)-(M:ℝ)*h k) atTop (𝓝 (g (L z))) by simpa using tendsto_const_nhds.sub (ht.const_mul (M:ℝ)))
      (show Tendsto (fun k => g (L z)+(M:ℝ)*h k) atTop (𝓝 (g (L z))) by simpa using tendsto_const_nhds.add (ht.const_mul (M:ℝ)))
    · intro k; have := (abs_le.mp (scalarWindow_approx hg (hh k) (L z))).1; linarith
    · intro k; have := (abs_le.mp (scalarWindow_approx hg (hh k) (L z))).2; linarith
  exact tendsto_integral_of_dominated_convergence (μ:=μ)
    (fun z => |w z|)
    (fun k => hw.aestronglyMeasurable.mul (((scalarWindow_contDiff hg.continuous (h k)).continuous.measurable.comp hL).aestronglyMeasurable))
    hw.abs (fun k => ae_of_all _ (fun z => by
      rw [Real.norm_eq_abs,abs_mul]
      exact (mul_le_mul_of_nonneg_left (scalarWindow_bound hg.continuous (B:=1) hb (hh k) (L z)) (abs_nonneg _)).trans_eq (mul_one _)))
    (ae_of_all _ (fun z => (hlim z).const_mul _))

end SK.Analytic

end
end

end OAI
