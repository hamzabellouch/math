import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.KernelTails

namespace OAI

/-!
# Integrability of hard Riesz truncations

Global upper growth makes the Riesz kernel square-integrable outside each positive-radius
ball. Pairing this exterior estimate with an L² input proves integrability of the hard
truncation. For finite measures, integrability instead follows from the bounded exterior
kernel and the inclusion of L² in L¹.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal

theorem kernel_sq_norm_le_tail_weight {d : ℕ} (n : ℕ) (hn : 1 ≤ n)
    (x y : Ambient d) (ε : ℝ) (hε : 0 < ε) (hy : ε ≤ dist x y) :
    ‖kernel n x y‖ ^ 2 ≤ (ε ^ (n - 1))⁻¹ * inverseDistancePow (n + 1) x y := by
  have hd : 0 < dist x y := lt_of_lt_of_le hε hy
  rw [kernel_norm_of_ne n x y (dist_pos.mp hd), inv_pow, ← pow_mul,
    show n * 2 = (n - 1) + (n + 1) by omega, pow_add, mul_inv]
  apply mul_le_mul_of_nonneg_right
  · simpa only [one_div] using! one_div_le_one_div_of_le
      (pow_pos hε (n - 1)) (pow_le_pow_left₀ hε.le hy (n - 1))
  · positivity

theorem kernel_memLp_two_on_exterior {d : ℕ} (n : ℕ) (hn : 1 ≤ n) (C : ℝ)
    (μ : Measure (Ambient d)) (hg : GlobalUpperGrowth n C μ)
    (x : Ambient d) (ε : ℝ) (hε : 0 < ε) :
    MemLp (kernel n x) 2 (μ.restrict {y | ε < dist x y}) := by
  have hmeas : AEStronglyMeasurable (kernel n x) (μ.restrict {y | ε < dist x y}) :=
    (kernel_measurable_right n x).aestronglyMeasurable
  apply (memLp_two_iff_integrable_sq_norm hmeas).2
  have hi := (inverseDistancePow_integrableOn_exterior n C μ hg x ε hε).const_mul
    ((ε ^ (n - 1))⁻¹)
  apply hi.mono' ((kernel_measurable_right n x).norm.pow_const 2).aestronglyMeasurable
  filter_upwards [ae_restrict_mem
    (measurableSet_lt measurable_const (continuous_const.dist continuous_id).measurable)] with y hy
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  exact kernel_sq_norm_le_tail_weight n hn x y ε hε hy.le

theorem truncation_integrable_of_globalGrowth {d : ℕ} (n : ℕ) (hn : 1 ≤ n) (C : ℝ)
    (μ : Measure (Ambient d)) (hg : GlobalUpperGrowth n C μ)
    (f : Ambient d → ℝ) (hf : MemLp f 2 μ)
    (x : Ambient d) (ε : ℝ) (hε : 0 < ε) :
    IntegrableOn (fun y => f y • kernel n x y) {y | ε < dist x y} μ := by
  apply memLp_one_iff_integrable.mp
  exact (hf.restrict _).smul (kernel_memLp_two_on_exterior n hn C μ hg x ε hε)

theorem truncation_integrable_of_finiteMeasure {d : ℕ} (n : ℕ)
    (μ : Measure (Ambient d)) [IsFiniteMeasure μ]
    (f : Ambient d → ℝ) (hf : MemLp f 2 μ)
    (x : Ambient d) (ε : ℝ) (hε : 0 < ε) :
    IntegrableOn (fun y => f y • kernel n x y) {y | ε < dist x y} μ := by
  apply (hf.integrable (by norm_num)).restrict.smul_bdd ((ε ^ n)⁻¹)
    (kernel_measurable_right n x).aestronglyMeasurable
  filter_upwards [ae_restrict_mem
    (measurableSet_lt measurable_const (continuous_const.dist continuous_id).measurable)] with y hy
  exact kernel_norm_le_truncation n x y ε hε hy.le

end

end RieszRectifiability

end OAI
