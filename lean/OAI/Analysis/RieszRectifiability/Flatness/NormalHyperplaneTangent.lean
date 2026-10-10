import Mathlib
import OAI.Analysis.RieszRectifiability.Foundations.HoleTangentMeasure
import OAI.Analysis.RieszRectifiability.Kernel.BlowupNormalMomentDecay
import OAI.Analysis.RieszRectifiability.Limits.CompactLimitZeroMoments

namespace OAI

/-!
# Tangent measures supported on a normal hyperplane

Half-space support is preserved by centered blowups. Decay of positive normal moments
forces the limiting support onto the boundary hyperplane; growth compactness then
produces a nonzero tangent measure with this constraint and two-sided growth bounds.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

theorem blowup_support_in_halfspace {d : ℕ} (n : ℕ) (μ : Measure (Ambient d))
    (e : Ambient d) (hside : ∀ x ∈ μ.support, 0 ≤ inner ℝ e x)
    (r : ℝ) (hr : 0 < r) :
    ∀ x ∈ (blowupMeasure n μ 0 r).support, 0 ≤ inner ℝ e x := by
  intro x hx
  have hsource : r • x ∈ μ.support := by
    simpa only [zero_add] using! (blowupMeasure_support_iff n μ 0 x r hr).mp hx
  have h := hside (r • x) hsource
  rw [inner_smul_right] at h
  exact nonneg_of_mul_nonneg_right h hr

theorem blowup_limit_support_in_normal_hyperplane {d : ℕ} (n : ℕ) (hn : 0 < n)
    (μ ν : Measure (Ambient d)) [IsFiniteMeasureOnCompacts μ] [IsFiniteMeasureOnCompacts ν]
    (G : ℝ) (hg : GlobalUpperGrowth n G μ) (e : Ambient d)
    (hside : ∀ x ∈ μ.support, 0 ≤ inner ℝ e x)
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
  have hnegative : ∀ x ∈ ν.support, positiveNormalHeight (-e) x = 0 := by
    apply compactTestConvergence_support_zero_of_first_moments
      (fun j => blowupMeasure n μ 0 (r j)) ν hlocal (positiveNormalHeight (-e))
      (positiveNormalHeight_continuous (-e)) (positiveNormalHeight_nonneg (-e))
    intro R _hR
    have hzero : ∀ j, (∫ x in ball (0 : Ambient d) R,
        positiveNormalHeight (-e) x ∂blowupMeasure n μ 0 (r j)) = 0 := by
      intro j
      apply integral_eq_zero_of_ae
      filter_upwards [ae_restrict_of_ae (blowupMeasure n μ 0 (r j)).support_mem_ae] with x hx
      have h := blowup_support_in_halfspace n μ e hside (r j) (hr j) x hx
      simp only [positiveNormalHeight, inner_neg_left, max_eq_left (neg_nonpos.mpr h), Pi.zero_apply]
    simpa only [hzero] using! (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  intro x hx
  have hp := le_max_right (0 : ℝ) (inner ℝ e x)
  have hm := le_max_right (0 : ℝ) (inner ℝ (-e) x)
  change inner ℝ e x ≤ positiveNormalHeight e x at hp
  change inner ℝ (-e) x ≤ positiveNormalHeight (-e) x at hm
  rw [hpositive x hx] at hp
  rw [hnegative x hx, inner_neg_left] at hm
  linarith

theorem exists_nonzero_normal_hyperplane_tangent {d : ℕ} (n : ℕ) (hn : 0 < n)
    (μ : Measure (Ambient d)) (C G : ℝ) (hC : 0 < C) (hg : GlobalUpperGrowth n G μ)
    (hlower : ∀ x ∈ μ.support, ∀ R : ℝ, 0 < R →
      ENNReal.ofReal (R ^ n / C) ≤ μ (ball x R))
    (hzero : (0 : Ambient d) ∈ μ.support)
    (e : Ambient d) (hside : ∀ x ∈ μ.support, 0 ≤ inner ℝ e x)
    (R₀ B : ℝ) (hR₀ : 0 < R₀)
    (hB : ∀ ε : ℝ, 0 < ε →
      (∫ x in ball (0 : Ambient d) R₀ ∩ {x | ε < ‖x‖}, positiveNormalPotential n e x ∂μ) ≤ B)
    (r : ℕ → ℝ) (hr : ∀ j, 0 < r j) (hr0 : Tendsto r atTop (𝓝 0)) :
    ∃ ρ : ℕ → ℕ, StrictMono ρ ∧ ∃ ν : Measure (Ambient d),
      IsFiniteMeasureOnCompacts ν ∧ ν ≠ 0 ∧
      CompactTestConvergence (fun j => blowupMeasure n μ 0 (r (ρ j))) ν ∧
      GlobalUpperGrowth n (G * 2 ^ n) ν ∧ (0 : Ambient d) ∈ ν.support ∧
      (∀ x ∈ ν.support, ∀ R : ℝ, 0 < R →
        ENNReal.ofReal (R ^ n / (C * 4 ^ n)) ≤ ν (ball x R)) ∧
      ∀ x ∈ ν.support, inner ℝ e x = 0 := by
  let : IsFiniteMeasureOnCompacts μ := globalGrowth_finite_on_compacts G μ hg
  have hi := (positiveNormalPotential_integrable_of_truncated_bounds n μ e R₀ B hB).1
  obtain ⟨ρ, hρ, ν, hfinite, hne, hlocal, hgν, hzeroν, hlowerν⟩ :=
    exists_blowup_measure_limit n μ C G hC hg hlower 0 hzero r hr
  let := hfinite
  exact ⟨ρ, hρ, ν, hfinite, hne, hlocal, hgν, hzeroν, hlowerν,
    blowup_limit_support_in_normal_hyperplane n hn μ ν G hg e hside R₀ hR₀ hi
      (fun j => r (ρ j)) (fun j => hr (ρ j)) (hr0.comp hρ.tendsto_atTop) hlocal⟩

end

end RieszRectifiability

end OAI
