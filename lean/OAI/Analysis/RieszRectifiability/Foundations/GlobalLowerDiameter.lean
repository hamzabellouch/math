import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.ADTruncations

namespace OAI

/-!
A nonzero measure finite on compact sets cannot have bounded support if a positive-dimensional
lower growth bound holds at every positive radius: bounded support would force finite total mass.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal

theorem global_lower_growth_support_ediam_top {d : ℕ} (n : ℕ) (hn : 1 ≤ n)
    (μ : Measure (Ambient d)) [IsFiniteMeasureOnCompacts μ] (hne : μ ≠ 0)
    (C : ℝ) (hC : 0 < C)
    (hlower : ∀ x ∈ μ.support, ∀ r : ℝ, 0 < r →
      ENNReal.ofReal (r ^ n / C) ≤ μ (ball x r)) : ediam μ.support = ∞ := by
  by_contra hdiam
  let : IsFiniteMeasure μ := finiteMeasure_of_bounded_support μ hdiam
  obtain ⟨a, ha⟩ := μ.nonempty_support hne
  let R : ℝ := C * μ.real univ + 1
  have hR1 : 1 ≤ R := by
    dsimp only [R]
    have hm : 0 ≤ μ.real univ := ENNReal.toReal_nonneg
    nlinarith
  have hR : 0 < R := lt_of_lt_of_le zero_lt_one hR1
  have hp : R ≤ R ^ n := le_self_pow₀ hR1 (by omega)
  have hl := (hlower a ha R hR).trans (measure_mono (subset_univ _))
  have hreal := ENNReal.toReal_mono (measure_ne_top μ univ) hl
  rw [ENNReal.toReal_ofReal (by positivity : 0 ≤ R ^ n / C)] at hreal
  have hpow : R ^ n ≤ μ.real univ * C := (div_le_iff₀ hC).mp hreal
  dsimp only [R] at hp
  nlinarith

end

end RieszRectifiability

end OAI
