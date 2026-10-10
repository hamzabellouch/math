import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.TruncationIntegrability

namespace OAI

/-!
# Hard truncations for AD-regular measures

For support of infinite diameter, AD regularity yields global upper growth. For bounded
support, the measure is finite. These two cases establish integrability of every positive
hard truncation against an L² input without imposing boundedness on the support.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal

theorem adRegular_globalGrowth_of_ediam_top {d : ℕ} (n : ℕ)
    (μ : Measure (Ambient d)) (hAD : ADRegular n μ)
    (hdiam : Metric.ediam μ.support = ∞) :
    ∃ C : ℝ, GlobalUpperGrowth n C μ := by
  obtain ⟨C, hC, hb⟩ := hAD
  refine ⟨C * 2 ^ n, ?_, ?_⟩
  · have : 0 ≤ C := le_trans zero_le_one hC
    positivity
  · intro x r hr
    by_cases hz : μ (ball x r) = 0
    · simp only [hz, zero_le]
    have hpos : 0 < μ (ball x r) := pos_iff_ne_zero.mpr hz
    obtain ⟨z, hzball, hzsupport⟩ := μ.nonempty_inter_support_of_pos hpos
    have hsub : ball x r ⊆ ball z (2 * r) := by
      intro y hy
      change dist y z < 2 * r
      calc
        _ ≤ dist y x + dist x z := dist_triangle y x z
        _ < r + r := add_lt_add hy (by simpa only [mem_ball, dist_comm] using! hzball)
        _ = _ := by ring
    calc
      _ ≤ μ (ball z (2 * r)) := measure_mono hsub
      _ ≤ ENNReal.ofReal (C * (2 * r) ^ n) :=
        (hb z hzsupport (2 * r) ⟨by positivity, by rw [hdiam]; exact le_top⟩).2
      _ = _ := by congr 1; rw [mul_pow]; ring

theorem finiteMeasure_of_bounded_support {d : ℕ} (μ : Measure (Ambient d))
    [IsFiniteMeasureOnCompacts μ] (hdiam : Metric.ediam μ.support ≠ ∞) :
    IsFiniteMeasure μ := by
  have hc : IsCompact μ.support :=
    isCompact_iff_isClosed_bounded.mpr
      ⟨μ.isClosed_support, Metric.isBounded_iff_ediam_ne_top.mpr hdiam⟩
  constructor
  have heq : μ μ.support = μ univ := by
    simpa only [univ_inter] using!
      (measure_inter_conull (μ := μ) (s := univ) μ.measure_compl_support)
  rw [← heq]
  exact hc.measure_lt_top

theorem truncation_integrable_of_ADRegular {d : ℕ} (n : ℕ) (hn : 1 ≤ n)
    (μ : Measure (Ambient d)) [IsFiniteMeasureOnCompacts μ] (hAD : ADRegular n μ)
    (f : Ambient d → ℝ) (hf : MemLp f 2 μ)
    (x : Ambient d) (ε : ℝ) (hε : 0 < ε) :
    IntegrableOn (fun y => f y • kernel n x y) {y | ε < dist x y} μ := by
  by_cases hd : Metric.ediam μ.support = ∞
  · obtain ⟨C, hg⟩ := adRegular_globalGrowth_of_ediam_top n μ hAD hd
    exact truncation_integrable_of_globalGrowth n hn C μ hg f hf x ε hε
  · let := finiteMeasure_of_bounded_support μ hd
    exact truncation_integrable_of_finiteMeasure n μ f hf x ε hε

end

end RieszRectifiability

end OAI
