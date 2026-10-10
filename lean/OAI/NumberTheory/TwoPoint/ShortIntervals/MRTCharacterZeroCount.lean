import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTCharacterLogGrowth

namespace OAI

/-! Jensen's bound for the total multiplicity in the fixed normalized disk.
This counts actual zeros, with their analytic multiplicities, and will control
the entire logarithmic derivative once a zero-free strip supplies distance. -/

namespace TwoPointCorrelations

open Complex Filter
open scoped BigOperators Classical Topology

variable {q : ℕ} [NeZero q]

theorem mrt_character_normalized_zero_count (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) (t : ℝ) :
    (∑ ρ ∈ (mrtCharacterNormalizedZeros_finite χ hχ t).toFinset,
      ((analyticOrderAt (mrtCharacterNormalizedLFunction χ t) ρ).toNat : ℝ)) ≤
        (1 / Real.log ((15 / 16 : ℝ) / (7 / 8))) *
          Real.log ((2 * q : ℝ) * mrtCharacterInverseConstant * (|t| + 4)) := by
  let f := mrtCharacterNormalizedLFunction χ t
  have hf : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z := by
    intro z _
    exact (mrtCharacterNormalizedLFunction_differentiable χ hχ t).analyticAt z
  have hf0 : f 0 = 1 := mrtCharacterNormalizedLFunction_zero χ t
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
    exact le_add_of_nonneg_right (tsum_nonneg fun _ => norm_nonneg _)
  have hB : 1 < (2 * q : ℝ) * mrtCharacterInverseConstant * (|t| + 4) := by
    have hq : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.pos q
    have hscale : 1 ≤ (2 * q : ℝ) * mrtCharacterInverseConstant := by nlinarith
    have hm := le_mul_of_one_le_left (show 0 ≤ |t|+4 by positivity) hscale
    linarith [abs_nonneg t]
  exact Erdos970.lem_sum_m_rho_bound
    ((2 * q : ℝ) * mrtCharacterInverseConstant * (|t| + 4)) (15 / 16) (7 / 8) hB
    (by norm_num) (by norm_num) (by norm_num) f hf
    (by rw [hf0]; exact one_ne_zero) hf0 (mrtCharacterNormalizedZeros_finite χ hχ t) g
    (fun z hz => mrtCharacterNormalizedLFunction_norm χ hχ t (hz.trans (by norm_num))) hg

/-- A distance lower bound controls every pole term at once. -/
theorem mrt_character_normalized_logderiv_norm (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) (t : ℝ) {z : ℂ} (hz : ‖z‖ ≤ 3 / 4)
    (hn : mrtCharacterNormalizedLFunction χ t z ≠ 0) {η : ℝ} (hη : 0 < η)
    (hd : ∀ ρ ∈ mrtCharacterNormalizedZeros χ t, η ≤ ‖z - ρ‖) :
    ‖deriv (mrtCharacterNormalizedLFunction χ t) z / mrtCharacterNormalizedLFunction χ t z‖ ≤
      (mrtCharacterLogDerivativeConstant +
        (1 / Real.log ((15 / 16 : ℝ) / (7 / 8))) / η) *
          Real.log ((2 * q : ℝ) * mrtCharacterInverseConstant * (|t| + 4)) := by
  let S := (mrtCharacterNormalizedZeros_finite χ hχ t).toFinset
  let m : ℂ → ℕ := fun ρ => (analyticOrderAt (mrtCharacterNormalizedLFunction χ t) ρ).toNat
  have hsum : ‖∑ ρ ∈ S, (m ρ : ℂ) / (z - ρ)‖ ≤ (∑ ρ ∈ S, (m ρ : ℝ)) / η := by
    calc
      _ ≤ ∑ ρ ∈ S, ‖(m ρ : ℂ) / (z - ρ)‖ := norm_sum_le _ _
      _ ≤ ∑ ρ ∈ S, (m ρ : ℝ) / η := by
        apply Finset.sum_le_sum
        intro ρ hρ
        rw [norm_div, Complex.norm_natCast]
        exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) hη
          (hd ρ ((mrtCharacterNormalizedZeros_finite χ hχ t).mem_toFinset.mp hρ))
      _ = _ := by rw [Finset.sum_div]
  have hcount := div_le_div_of_nonneg_right (mrt_character_normalized_zero_count χ hχ t) hη.le
  have herr := mrtCharacterNormalized_logderiv χ hχ t hz hn
  have htri := norm_add_le
    (deriv (mrtCharacterNormalizedLFunction χ t) z / mrtCharacterNormalizedLFunction χ t z -
      ∑ ρ ∈ S, (m ρ : ℂ) / (z - ρ))
    (∑ ρ ∈ S, (m ρ : ℂ) / (z - ρ))
  rw [sub_add_cancel] at htri
  calc
    _ ≤ mrtCharacterLogDerivativeConstant *
        Real.log ((2 * q : ℝ) * mrtCharacterInverseConstant * (|t| + 4)) +
          ((1 / Real.log ((15 / 16 : ℝ) / (7 / 8))) *
            Real.log ((2 * q : ℝ) * mrtCharacterInverseConstant * (|t| + 4))) / η := by
      exact htri.trans (add_le_add herr (hsum.trans hcount))
    _ = _ := by ring

end TwoPointCorrelations

end OAI
