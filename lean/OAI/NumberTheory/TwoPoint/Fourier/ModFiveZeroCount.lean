import OAI.NumberTheory.TwoPoint.Fourier.ModFiveLogGrowth

namespace OAI

/-! Jensen's bound for the total multiplicity in the fixed normalized disk.
This counts actual zeros, with their analytic multiplicities, and will control
the entire logarithmic derivative once a zero-free strip supplies distance. -/

namespace TwoPointCorrelations

open Complex Filter
open scoped BigOperators Classical Topology

theorem modFive_normalized_zero_count (χ : DirichletCharacter ℂ 5)
    (hχ : χ ≠ 1) (t : ℝ) :
    (∑ ρ ∈ (modFiveNormalizedZeros_finite χ hχ t).toFinset,
      ((analyticOrderAt (modFiveNormalizedLFunction χ t) ρ).toNat : ℝ)) ≤
        (1 / Real.log ((15 / 16 : ℝ) / (7 / 8))) *
          Real.log (8 * modFiveInverseConstant * (|t| + 4)) := by
  let f := modFiveNormalizedLFunction χ t
  have hf : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z := by
    intro z _
    exact (modFiveNormalizedLFunction_differentiable χ hχ t).analyticAt z
  have hf0 : f 0 = 1 := modFiveNormalizedLFunction_zero χ t
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
    exact le_add_of_nonneg_right (tsum_nonneg fun _ => norm_nonneg _)
  have hB : 1 < 8 * modFiveInverseConstant * (|t| + 4) := by
    nlinarith [abs_nonneg t]
  exact Erdos970.lem_sum_m_rho_bound
    (8 * modFiveInverseConstant * (|t| + 4)) (15 / 16) (7 / 8) hB
    (by norm_num) (by norm_num) (by norm_num) f hf
    (by rw [hf0]; exact one_ne_zero) hf0 (modFiveNormalizedZeros_finite χ hχ t) g
    (fun z hz => modFiveNormalizedLFunction_norm χ hχ t (hz.trans (by norm_num))) hg

/-- A distance lower bound controls every pole term at once. -/
theorem modFive_normalized_logderiv_norm (χ : DirichletCharacter ℂ 5)
    (hχ : χ ≠ 1) (t : ℝ) {z : ℂ} (hz : ‖z‖ ≤ 3 / 4)
    (hn : modFiveNormalizedLFunction χ t z ≠ 0) {η : ℝ} (hη : 0 < η)
    (hd : ∀ ρ ∈ modFiveNormalizedZeros χ t, η ≤ ‖z - ρ‖) :
    ‖deriv (modFiveNormalizedLFunction χ t) z / modFiveNormalizedLFunction χ t z‖ ≤
      (modFiveLogDerivativeConstant +
        (1 / Real.log ((15 / 16 : ℝ) / (7 / 8))) / η) *
          Real.log (8 * modFiveInverseConstant * (|t| + 4)) := by
  let S := (modFiveNormalizedZeros_finite χ hχ t).toFinset
  let m : ℂ → ℕ := fun ρ => (analyticOrderAt (modFiveNormalizedLFunction χ t) ρ).toNat
  have hsum : ‖∑ ρ ∈ S, (m ρ : ℂ) / (z - ρ)‖ ≤ (∑ ρ ∈ S, (m ρ : ℝ)) / η := by
    calc
      _ ≤ ∑ ρ ∈ S, ‖(m ρ : ℂ) / (z - ρ)‖ := norm_sum_le _ _
      _ ≤ ∑ ρ ∈ S, (m ρ : ℝ) / η := by
        apply Finset.sum_le_sum
        intro ρ hρ
        rw [norm_div, Complex.norm_natCast]
        exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) hη
          (hd ρ ((modFiveNormalizedZeros_finite χ hχ t).mem_toFinset.mp hρ))
      _ = _ := by rw [Finset.sum_div]
  have hcount := div_le_div_of_nonneg_right (modFive_normalized_zero_count χ hχ t) hη.le
  have herr := modFiveNormalized_logderiv χ hχ t hz hn
  have htri := norm_add_le
    (deriv (modFiveNormalizedLFunction χ t) z / modFiveNormalizedLFunction χ t z -
      ∑ ρ ∈ S, (m ρ : ℂ) / (z - ρ))
    (∑ ρ ∈ S, (m ρ : ℂ) / (z - ρ))
  rw [sub_add_cancel] at htri
  calc
    _ ≤ modFiveLogDerivativeConstant *
        Real.log (8 * modFiveInverseConstant * (|t| + 4)) +
          ((1 / Real.log ((15 / 16 : ℝ) / (7 / 8))) *
            Real.log (8 * modFiveInverseConstant * (|t| + 4))) / η := by
      exact htri.trans (add_le_add herr (hsum.trans hcount))
    _ = _ := by ring

end TwoPointCorrelations

end OAI
