import OAI.NumberTheory.TwoPointCorrelations.ModFiveCenterBounds
import StrongPNT.Erdos970.PNT2_LogDerivative

namespace OAI

/-! Fixed-radius logarithmic-derivative expansion for the three modulus-five
functions. The analytic disk theorem applies with explicit analyticity,
finite-zero, normalization and growth hypotheses.
-/

namespace TwoPointCorrelations

open Complex Filter
open scoped BigOperators Classical Topology

noncomputable def modFiveNormalizedZeros (χ : DirichletCharacter ℂ 5) (t : ℝ) : Set ℂ :=
  Erdos970.zerosetKfR (7 / 8) (by norm_num) (modFiveNormalizedLFunction χ t)

lemma modFiveNormalizedZeros_finite (χ : DirichletCharacter ℂ 5)
    (hχ : χ ≠ 1) (t : ℝ) : (modFiveNormalizedZeros χ t).Finite := by
  apply Erdos970.lem_Contra_finiteKR (7 / 8) (by norm_num) (by norm_num)
    (modFiveNormalizedLFunction χ t)
  · intro z _
    exact (modFiveNormalizedLFunction_differentiable χ hχ t).analyticAt z
  · refine ⟨0, by simp, ?_⟩
    rw [modFiveNormalizedLFunction_zero]
    exact one_ne_zero

noncomputable def modFiveLogDerivativeConstant : ℝ :=
  16 * (4 / 5 : ℝ) ^ 2 / ((4 / 5 : ℝ) - 3 / 4) ^ 3 +
    1 / (((15 / 16 : ℝ) ^ 2 / (7 / 8) - 7 / 8) * Real.log ((15 / 16 : ℝ) / (7 / 8)))

/-- Exact finite zero-sum approximation on the inner disk. -/
theorem modFiveNormalized_logderiv (χ : DirichletCharacter ℂ 5)
    (hχ : χ ≠ 1) (t : ℝ) {z : ℂ} (hz : ‖z‖ ≤ 3 / 4)
    (hn : modFiveNormalizedLFunction χ t z ≠ 0) :
    ‖deriv (modFiveNormalizedLFunction χ t) z / modFiveNormalizedLFunction χ t z -
      ∑ ρ ∈ (modFiveNormalizedZeros_finite χ hχ t).toFinset,
        (analyticOrderAt (modFiveNormalizedLFunction χ t) ρ).toNat / (z - ρ)‖ ≤
      modFiveLogDerivativeConstant *
        Real.log (8 * modFiveInverseConstant * (|t| + 4)) := by
  let f := modFiveNormalizedLFunction χ t
  have hf : ∀ w ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f w := by
    intro w _
    exact (modFiveNormalizedLFunction_differentiable χ hχ t).analyticAt w
  have hf0 : f 0 = 1 := modFiveNormalizedLFunction_zero χ t
  have hfin : (Erdos970.zerosetKfR (7 / 8) (by norm_num) f).Finite :=
    modFiveNormalizedZeros_finite χ hχ t
  have hfactor : ∀ ρ : ℂ, ∃ g : ℂ → ℂ, AnalyticAt ℂ g ρ ∧ g ρ ≠ 0 ∧
      (ρ ∈ Erdos970.zerosetKfR (7 / 8) (by norm_num) f →
        ∀ᶠ w in 𝓝 ρ, f w = (w - ρ) ^ (analyticOrderAt f ρ).toNat * g w) := by
    intro ρ
    by_cases hρ : ρ ∈ Erdos970.zerosetKfR (7 / 8) (by norm_num) f
    · obtain ⟨g, hg, hgne, heq⟩ := Erdos970.lem_analytic_zero_factor
        (15 / 16) (7 / 8) (by norm_num) (by norm_num) (by norm_num) f hf
        (by rw [hf0]; exact one_ne_zero) ρ hρ
      exact ⟨g, hg, hgne, fun _ => heq⟩
    · exact ⟨fun _ => 1, analyticAt_const, one_ne_zero, fun h => (hρ h).elim⟩
  let g : ℂ → ℂ → ℂ := fun ρ => Classical.choose (hfactor ρ)
  have hg : ∀ ρ ∈ Erdos970.zerosetKfR (7 / 8) (by norm_num) f,
      AnalyticAt ℂ (g ρ) ρ ∧ g ρ ρ ≠ 0 ∧
        ∀ᶠ w in 𝓝 ρ, f w = (w - ρ) ^ (analyticOrderAt f ρ).toNat * g ρ w := by
    intro ρ hρ
    exact ⟨(Classical.choose_spec (hfactor ρ)).1,
      (Classical.choose_spec (hfactor ρ)).2.1,
      (Classical.choose_spec (hfactor ρ)).2.2 hρ⟩
  have hK : 1 ≤ modFiveInverseConstant := by
    unfold modFiveInverseConstant
    have hsum : 0 ≤ ∑' n : ℕ, ‖LSeries.term (1 : ℕ → ℂ) (2 : ℂ) n‖ :=
      tsum_nonneg fun _ => norm_nonneg _
    linarith
  have hB : 1 < 8 * modFiveInverseConstant * (|t| + 4) := by
    nlinarith [abs_nonneg t]
  have hbound : ∀ w ∈ Metric.closedBall (0 : ℂ) (15 / 16 : ℝ),
      ‖f w‖ ≤ 8 * modFiveInverseConstant * (|t| + 4) := by
    intro w hw
    apply modFiveNormalizedLFunction_norm χ hχ t
    have hw' : ‖w‖ ≤ 15 / 16 := by simpa using hw
    linarith
  have hz' : z ∈ Metric.closedBall (0 : ℂ) (3 / 4 : ℝ) \
      Erdos970.zerosetKfR (7 / 8) (by norm_num) f := by
    refine ⟨by simpa using hz, ?_⟩
    intro h
    exact hn h.2
  exact Erdos970.final_ineq1 (8 * modFiveInverseConstant * (|t| + 4)) hB
    (3 / 4) (4 / 5) (15 / 16) (7 / 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    f hf hf0 hfin hg hbound z hz'

end TwoPointCorrelations

end OAI
