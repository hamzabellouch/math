import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.KernelBasic

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

theorem dyadic_admissibleRadius_of_horizon {d : ℕ} (μ : Measure (Ambient d))
    (T : ℕ) (hT : AdmissibleRadius μ ((2 : ℝ) ^ T)) (l : ℕ) (hl : l ≤ T) :
    AdmissibleRadius μ ((2 : ℝ) ^ l) := by
  refine ⟨by positivity, ?_⟩
  exact (ENNReal.ofReal_le_ofReal (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hl)).trans hT.2

theorem dyadic_lower_real_mass_of_admissible_horizon {d : ℕ} (n : ℕ) (C G : ℝ)
    (μ : Measure (Ambient d)) (hC : 0 < C) (hg : GlobalUpperGrowth n G μ)
    (hlower : ∀ r : ℝ, AdmissibleRadius μ r →
      ENNReal.ofReal (r ^ n / C) ≤ μ (ball 0 r))
    (T : ℕ) (hT : AdmissibleRadius μ ((2 : ℝ) ^ T)) (l : ℕ) (hl : l ≤ T) :
    C⁻¹ * ((2 : ℝ) ^ l) ^ n ≤ μ.real (ball 0 ((2 : ℝ) ^ l)) := by
  have hpos : 0 < (2 : ℝ) ^ l := by positivity
  have hfin : μ (ball 0 ((2 : ℝ) ^ l)) ≠ ∞ := ne_of_lt
    ((hg.2 0 ((2 : ℝ) ^ l) hpos).trans_lt ENNReal.ofReal_lt_top)
  have h := (ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top hfin).mpr
    (hlower _ (dyadic_admissibleRadius_of_horizon μ T hT l hl))
  have hn : 0 ≤ ((2 : ℝ) ^ l) ^ n / C := by positivity
  rw [ENNReal.toReal_ofReal hn] at h
  simpa only [Measure.real, div_eq_mul_inv, mul_comm] using! h

theorem support_diameters_grow_of_admissible_dyadic_horizon {d : ℕ}
    (μ : ℕ → Measure (Ambient d)) (T : ℕ → ℕ) (hT : Tendsto T atTop atTop)
    (horizon : ∀ j, AdmissibleRadius (μ j) ((2 : ℝ) ^ T j)) :
    ∀ r : ℝ, 0 < r → ∀ᶠ j in atTop, ENNReal.ofReal r ≤ ediam (μ j).support := by
  have hp : Tendsto (fun j => (2 : ℝ) ^ T j) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).comp hT
  intro r _hr
  filter_upwards [hp.eventually (eventually_ge_atTop r)] with j hj
  exact (ENNReal.ofReal_le_ofReal hj).trans (horizon j).2

end

end RieszRectifiability

end OAI
