import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTCharacterCenterBounds
import StrongPNT.Erdos970.PNT2_LogDerivative

namespace OAI

/-! Fixed-radius logarithmic-derivative expansion for every nonprincipal
Dirichlet L-function. The exact finite zero sum is retained and the
growth cost is logarithmic in q * (abs(t)+4). -/

namespace TwoPointCorrelations

open Complex Filter
open scoped BigOperators Classical Topology

variable {q : ℕ} [NeZero q]

noncomputable def mrtCharacterNormalizedZeros (χ : DirichletCharacter ℂ q) (t : ℝ) : Set ℂ :=
  Erdos970.zerosetKfR (7 / 8) (by norm_num) (mrtCharacterNormalizedLFunction χ t)

lemma mrtCharacterNormalizedZeros_finite (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) (t : ℝ) : (mrtCharacterNormalizedZeros χ t).Finite := by
  apply Erdos970.lem_Contra_finiteKR (7 / 8) (by norm_num) (by norm_num)
    (mrtCharacterNormalizedLFunction χ t)
  · intro z _
    exact (mrtCharacterNormalizedLFunction_differentiable χ hχ t).analyticAt z
  · refine ⟨0, by simp, ?_⟩
    rw [mrtCharacterNormalizedLFunction_zero]
    exact one_ne_zero

noncomputable def mrtCharacterLogDerivativeConstant : ℝ :=
  16 * (4 / 5 : ℝ) ^ 2 / ((4 / 5 : ℝ) - 3 / 4) ^ 3 +
    1 / (((15 / 16 : ℝ) ^ 2 / (7 / 8) - 7 / 8) * Real.log ((15 / 16 : ℝ) / (7 / 8)))

/-- Exact finite zero-sum approximation on the inner disk. -/
theorem mrtCharacterNormalized_logderiv (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) (t : ℝ) {z : ℂ} (hz : ‖z‖ ≤ 3 / 4)
    (hn : mrtCharacterNormalizedLFunction χ t z ≠ 0) :
    ‖deriv (mrtCharacterNormalizedLFunction χ t) z / mrtCharacterNormalizedLFunction χ t z -
      ∑ ρ ∈ (mrtCharacterNormalizedZeros_finite χ hχ t).toFinset,
        (analyticOrderAt (mrtCharacterNormalizedLFunction χ t) ρ).toNat / (z - ρ)‖ ≤
      mrtCharacterLogDerivativeConstant *
        Real.log ((2 * q : ℝ) * mrtCharacterInverseConstant * (|t| + 4)) := by
  let f := mrtCharacterNormalizedLFunction χ t
  have hf : ∀ w ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f w := by
    intro w _
    exact (mrtCharacterNormalizedLFunction_differentiable χ hχ t).analyticAt w
  have hf0 : f 0 = 1 := mrtCharacterNormalizedLFunction_zero χ t
  have hfin : (Erdos970.zerosetKfR (7 / 8) (by norm_num) f).Finite :=
    mrtCharacterNormalizedZeros_finite χ hχ t
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
  have hK : 1 ≤ mrtCharacterInverseConstant := by
    unfold mrtCharacterInverseConstant
    have hsum : 0 ≤ ∑' n : ℕ, ‖LSeries.term (1 : ℕ → ℂ) (2 : ℂ) n‖ :=
      tsum_nonneg fun _ => norm_nonneg _
    linarith
  have hB : 1 < (2 * q : ℝ) * mrtCharacterInverseConstant * (|t| + 4) := by
    have hq : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.pos q
    have hscale : 1 ≤ (2 * q : ℝ) * mrtCharacterInverseConstant := by nlinarith
    have hm := le_mul_of_one_le_left (show 0 ≤ |t|+4 by positivity) hscale
    linarith [abs_nonneg t]
  have hbound : ∀ w ∈ Metric.closedBall (0 : ℂ) (15 / 16 : ℝ),
      ‖f w‖ ≤ (2 * q : ℝ) * mrtCharacterInverseConstant * (|t| + 4) := by
    intro w hw
    apply mrtCharacterNormalizedLFunction_norm χ hχ t
    have hw' : ‖w‖ ≤ 15 / 16 := by simpa using hw
    linarith
  have hz' : z ∈ Metric.closedBall (0 : ℂ) (3 / 4 : ℝ) \
      Erdos970.zerosetKfR (7 / 8) (by norm_num) f := by
    refine ⟨by simpa using hz, ?_⟩
    intro h
    exact hn h.2
  exact Erdos970.final_ineq1 ((2 * q : ℝ) * mrtCharacterInverseConstant * (|t| + 4)) hB
    (3 / 4) (4 / 5) (15 / 16) (7 / 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    f hf hf0 hfin hg hbound z hz'

end TwoPointCorrelations

end OAI
