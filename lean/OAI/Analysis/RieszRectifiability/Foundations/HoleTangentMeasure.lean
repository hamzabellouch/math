import Mathlib
import OAI.Analysis.RieszRectifiability.Foundations.BlowupMeasure
import OAI.Analysis.RieszRectifiability.Limits.GlobalLowerMeasureLimit
import OAI.Analysis.RieszRectifiability.Foundations.EmptyBallHalfspace

namespace OAI

/-!
# Tangent measures at a nearest point to a hole

Uniform growth bounds yield a nonzero subsequential blowup limit with inherited
two-sided growth. At a point nearest to a hole, the rescaled quadratic constraint
converges to a half-space constraint on the tangent measure's support.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

theorem exists_blowup_measure_limit {d : ℕ} (n : ℕ) (μ : Measure (Ambient d))
    (C G : ℝ) (hC : 0 < C) (hg : GlobalUpperGrowth n G μ)
    (hlower : ∀ x ∈ μ.support, ∀ R : ℝ, 0 < R →
      ENNReal.ofReal (R ^ n / C) ≤ μ (ball x R))
    (a : Ambient d) (ha : a ∈ μ.support) (r : ℕ → ℝ) (hr : ∀ j, 0 < r j) :
    ∃ ρ : ℕ → ℕ, StrictMono ρ ∧ ∃ ν : Measure (Ambient d),
      IsFiniteMeasureOnCompacts ν ∧ ν ≠ 0 ∧
      CompactTestConvergence (fun j => blowupMeasure n μ a (r (ρ j))) ν ∧
      GlobalUpperGrowth n (G * 2 ^ n) ν ∧ (0 : Ambient d) ∈ ν.support ∧
      ∀ x ∈ ν.support, ∀ R : ℝ, 0 < R →
        ENNReal.ofReal (R ^ n / (C * 4 ^ n)) ≤ ν (ball x R) := by
  have hg' : ∀ j, GlobalUpperGrowth n G (blowupMeasure n μ a (r j)) :=
    fun j => blowupMeasure_growth n μ a (r j) G (hr j) hg
  let : ∀ j, IsFiniteMeasureOnCompacts (blowupMeasure n μ a (r j)) :=
    fun j => globalGrowth_finite_on_compacts G _ (hg' j)
  exact exists_global_growth_measure_limit n (fun j => blowupMeasure n μ a (r j)) C G hC hg'
    (fun j => blowupMeasure_lower_global n μ a (r j) C (hr j) hlower)
    (fun j => blowupMeasure_origin_mem_support n μ a (r j) (hr j) ha)

theorem exists_nonzero_halfspace_tangent_of_hole {d : ℕ}
    (n : ℕ) (μ : Measure (Ambient d)) (hne : μ ≠ 0)
    (C G : ℝ) (hC : 0 < C) (hg : GlobalUpperGrowth n G μ)
    (hlower : ∀ x ∈ μ.support, ∀ R : ℝ, 0 < R →
      ENNReal.ofReal (R ^ n / C) ≤ μ (ball x R))
    (c : Ambient d) (hc : c ∉ μ.support)
    (r : ℕ → ℝ) (hr : ∀ j, 0 < r j) (hr0 : Tendsto r atTop (𝓝 0)) :
    ∃ a ∈ μ.support, a ≠ c ∧ ∃ ρ : ℕ → ℕ, StrictMono ρ ∧
      ∃ ν : Measure (Ambient d), IsFiniteMeasureOnCompacts ν ∧ ν ≠ 0 ∧
        CompactTestConvergence (fun j => blowupMeasure n μ a (r (ρ j))) ν ∧
        GlobalUpperGrowth n (G * 2 ^ n) ν ∧ (0 : Ambient d) ∈ ν.support ∧
        (∀ x ∈ ν.support, ∀ R : ℝ, 0 < R →
          ENNReal.ofReal (R ^ n / (C * 4 ^ n)) ≤ ν (ball x R)) ∧
        ∀ x ∈ ν.support, 0 ≤ inner ℝ (a - c) x := by
  obtain ⟨a, ha, hac, hmin⟩ := exists_nearest_point_to_hole μ.support μ.isClosed_support
    (μ.nonempty_support hne) c hc
  obtain ⟨ρ, hρ, ν, hfinite, hneν, hlocal, hgν, hzero, hlowerν⟩ :=
    exists_blowup_measure_limit n μ C G hC hg hlower a ha r hr
  let := hfinite
  let : ∀ j, IsFiniteMeasureOnCompacts (blowupMeasure n μ a (r (ρ j))) :=
    fun j => globalGrowth_finite_on_compacts G _
      (blowupMeasure_growth n μ a (r (ρ j)) G (hr (ρ j)) hg)
  refine ⟨a, ha, hac, ρ, hρ, ν, hfinite, hneν, hlocal, hgν, hzero, hlowerν, ?_⟩
  apply compactTestConvergence_halfspace_of_quadratic_constraint
    (fun j => blowupMeasure n μ a (r (ρ j))) ν hlocal (a - c)
    (fun j => r (ρ j)) (fun j => (hr (ρ j)).le) (hr0.comp hρ.tendsto_atTop)
  intro j x hx
  apply nearest_point_rescaled_constraint a c x (r (ρ j)) (hr (ρ j))
  exact hmin (a + r (ρ j) • x)
    ((blowupMeasure_support_iff n μ a x (r (ρ j)) (hr (ρ j))).mp hx)

end

end RieszRectifiability

end OAI
