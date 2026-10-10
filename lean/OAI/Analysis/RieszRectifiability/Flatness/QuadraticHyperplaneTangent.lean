import Mathlib
import OAI.Analysis.RieszRectifiability.Flatness.NormalHyperplaneTangent
import OAI.Analysis.RieszRectifiability.Foundations.QuadraticNormalPotential
import OAI.Analysis.RieszRectifiability.Flatness.IntrinsicHyperplaneNull

namespace OAI

/-!
# Hyperplane tangents from a quadratic support constraint

Blowups turn the quadratic constraint into a halfspace condition, while vanishing
positive normal moments force the limiting support into its boundary hyperplane.
Intrinsic growth then rules out the resulting nonzero tangent measure.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

theorem blowup_support_quadratic_constraint {d : ℕ} (n : ℕ) (μ : Measure (Ambient d))
    (e : Ambient d) (hquad : ∀ x ∈ μ.support, 0 ≤ 2 * inner ℝ e x + ‖x‖ ^ 2)
    (r : ℝ) (hr : 0 < r) :
    ∀ x ∈ (blowupMeasure n μ 0 r).support, 0 ≤ 2 * inner ℝ e x + r * ‖x‖ ^ 2 := by
  intro x hx
  have hsource : r • x ∈ μ.support := by
    simpa only [zero_add] using! (blowupMeasure_support_iff n μ 0 x r hr).mp hx
  have h := hquad (r • x) hsource
  rw [inner_smul_right, norm_smul, Real.norm_of_nonneg hr.le] at h
  have hp : 0 ≤ r * (2 * inner ℝ e x + r * ‖x‖ ^ 2) := by nlinarith
  exact nonneg_of_mul_nonneg_right hp hr

theorem quadratic_blowup_limit_support_in_normal_hyperplane {d : ℕ}
    (n : ℕ) (hn : 0 < n) (μ ν : Measure (Ambient d))
    [IsFiniteMeasureOnCompacts μ] [IsFiniteMeasureOnCompacts ν]
    (G : ℝ) (hg : GlobalUpperGrowth n G μ) (e : Ambient d)
    (hquad : ∀ x ∈ μ.support, 0 ≤ 2 * inner ℝ e x + ‖x‖ ^ 2)
    (R₀ : ℝ) (hR₀ : 0 < R₀)
    (hi : IntegrableOn (positiveNormalPotential n e) (ball (0 : Ambient d) R₀) μ)
    (r : ℕ → ℝ) (hr : ∀ j, 0 < r j) (hr0 : Tendsto r atTop (𝓝 0))
    (hlocal : CompactTestConvergence (fun j => blowupMeasure n μ 0 (r j)) ν) :
    ∀ x ∈ ν.support, inner ℝ e x = 0 := by
  let : ∀ j, IsFiniteMeasureOnCompacts (blowupMeasure n μ 0 (r j)) :=
    fun j => globalGrowth_finite_on_compacts G _ (blowupMeasure_growth n μ 0 (r j) G (hr j) hg)
  have hpositive := compactTestConvergence_support_zero_of_first_moments
    (fun j => blowupMeasure n μ 0 (r j)) ν hlocal (positiveNormalHeight e)
    (positiveNormalHeight_continuous e) (positiveNormalHeight_nonneg e)
    (blowup_positiveNormalHeight_moments_tendsto_zero n hn μ G hg e R₀ hR₀ hi r hr hr0)
  have hnonneg := compactTestConvergence_halfspace_of_quadratic_constraint
    (fun j => blowupMeasure n μ 0 (r j)) ν hlocal e r (fun j => (hr j).le) hr0
    (fun j => blowup_support_quadratic_constraint n μ e hquad (r j) (hr j))
  intro x hx
  have h := le_max_right (0 : ℝ) (inner ℝ e x)
  change inner ℝ e x ≤ positiveNormalHeight e x at h
  rw [hpositive x hx] at h
  exact le_antisymm h (hnonneg x hx)

theorem intrinsic_quadratic_annular_bound_impossible (p : ℕ)
    (μ : Measure (Ambient (p + 1))) (C G : ℝ) (hC : 0 < C)
    (hg : GlobalUpperGrowth (p + 1) G μ)
    (hlower : ∀ x ∈ μ.support, ∀ R : ℝ, 0 < R →
      ENNReal.ofReal (R ^ (p + 1) / C) ≤ μ (ball x R))
    (hzero : (0 : Ambient (p + 1)) ∈ μ.support)
    (e : Ambient (p + 1)) (he : e ≠ 0)
    (hquad : ∀ x ∈ μ.support, 0 ≤ 2 * inner ℝ e x + ‖x‖ ^ 2)
    (R B : ℝ) (hR : 0 < R)
    (hB : ∀ ε : ℝ, 0 < ε →
      ‖∫ x in ball (0 : Ambient (p + 1)) R ∩ {x | ε < ‖x‖}, kernel (p + 1) x 0 ∂μ‖ ≤ B) : False := by
  let : IsFiniteMeasureOnCompacts μ := globalGrowth_finite_on_compacts G μ hg
  have hi := positiveNormalPotential_integrable_of_quadratic_annuli p μ G hg e hquad R B hR hB
  obtain ⟨ρ, hρ, ν, hfinite, hne, hlocal, hgν, _hzeroν, _hlowerν⟩ :=
    exists_blowup_measure_limit (p + 1) μ C G hC hg hlower 0 hzero
      (fun j : ℕ => (1 / 2 : ℝ) ^ j) (fun _ => by positivity)
  let := hfinite
  have hplane := quadratic_blowup_limit_support_in_normal_hyperplane (p + 1) (by omega)
    μ ν G hg e hquad R hR hi (fun j => (1 / 2 : ℝ) ^ ρ j) (fun _ => by positivity)
    ((tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : 0 ≤ (1 / 2 : ℝ))
      (by norm_num : (1 / 2 : ℝ) < 1)).comp hρ.tendsto_atTop) hlocal
  exact intrinsic_growth_not_supported_in_hyperplane (p + 1) ν (G * 2 ^ (p + 1)) hgν hne e he hplane

end

end RieszRectifiability

end OAI
