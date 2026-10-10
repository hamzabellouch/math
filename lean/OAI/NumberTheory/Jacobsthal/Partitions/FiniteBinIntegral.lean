import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Tactic

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.FiniteBinIntegral

open Set MeasureTheory
open scoped ENNReal

variable {α β : Type*} [MeasurableSpace α]

theorem integrate_bin_envelope (μ : Measure α) (I : Finset β) (B : β → Set α)
    (hB : ∀ k ∈ I,MeasurableSet (B k)) (C : β → ℝ) :
    (∫⁻ x,∑ k ∈ I, ENNReal.ofReal (C k)*((B k).indicator (fun _ => (1:ℝ≥0∞)) x) ∂μ) =
      ∑ k ∈ I,ENNReal.ofReal (C k)*μ (B k) := by
  rw [lintegral_finsetSum I (f := fun k x => ENNReal.ofReal (C k)*((B k).indicator (fun _ => (1:ℝ≥0∞)) x))
    (fun k hk => measurable_const.mul (measurable_const.indicator (hB k hk)))]
  apply Finset.sum_congr rfl
  intro k hk
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_indicator (hB k hk),setLIntegral_const,one_mul]

end NumberTheoryLean.FiniteBinIntegral

end

end Erdos970

end OAI
