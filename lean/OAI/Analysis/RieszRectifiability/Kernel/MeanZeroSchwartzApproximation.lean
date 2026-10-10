import Mathlib
import OAI.Analysis.RieszRectifiability.Limits.CompactSchwartzApproximation
import OAI.Analysis.RieszRectifiability.Rigidity.FourierMeanZeroTests

namespace OAI

namespace RieszRectifiability

noncomputable section

open SchwartzMap MeasureTheory Metric Filter Topology
open scoped ContDiff FourierTransform

theorem unitSmoothCutoff_integral_pos (d : ℕ) :
    0 < ∫ x : Ambient d, unitSmoothCutoff d x := by
  have hc := ((unitSmoothCutoff d).contDiff (n := ⊤)).continuous
  have hi : Integrable (unitSmoothCutoff d) (volume : Measure (Ambient d)) :=
    hc.integrable_of_hasCompactSupport (unitSmoothCutoff d).hasCompactSupport
  apply integral_pos_of_integrable_nonneg_nonzero hc hi
    (fun x => (unitSmoothCutoff d).nonneg' x)
  have h : unitSmoothCutoff d (0 : Ambient d) = 1 :=
    (unitSmoothCutoff d).one_of_mem_closedBall (by simp [unitSmoothCutoff])
  exact h.trans_ne one_ne_zero

theorem exists_compact_complex_schwartz_unit_integral (d : ℕ) :
    ∃ η : 𝓢(Ambient d, ℂ), HasCompactSupport η ∧ (∫ x, η x) = 1 := by
  let b : Ambient d → ℂ := fun x => (unitSmoothCutoff d x : ℂ)
  have hb : HasCompactSupport b := (unitSmoothCutoff d).hasCompactSupport.comp_left
    (g := fun r : ℝ => (r : ℂ)) Complex.ofReal_zero
  have hs : ContDiff ℝ ∞ b := Complex.ofRealCLM.contDiff.comp
    ((unitSmoothCutoff d).contDiff (n := ⊤))
  let B : 𝓢(Ambient d, ℂ) := hb.toSchwartzMap hs
  have hc : HasCompactSupport B := hb
  have hI : (∫ x, B x) ≠ 0 := by
    change (∫ x : Ambient d, (unitSmoothCutoff d x : ℂ)) ≠ 0
    rw [integral_complex_ofReal]
    exact_mod_cast ne_of_gt (unitSmoothCutoff_integral_pos d)
  refine ⟨(∫ x, B x)⁻¹ • B, ?_, ?_⟩
  · exact hc.smul_left
  · change (∫ x, (∫ y, B y)⁻¹ • B x) = 1
    rw [integral_smul, smul_eq_mul, inv_mul_cancel₀ hI]

theorem exists_compact_mean_zero_schwartz_approximation {d : ℕ}
    (g : 𝓢(Ambient d, ℂ)) (hg : (∫ x, g x) = 0) :
    ∃ G : ℕ → 𝓢(Ambient d, ℂ),
      (∀ j, HasCompactSupport (G j) ∧ (∫ x, G j x) = 0) ∧ Tendsto G atTop (𝓝 g) := by
  obtain ⟨G, hc, ht⟩ := exists_compact_schwartz_approximation g
  obtain ⟨η, hcη, hη⟩ := exists_compact_complex_schwartz_unit_integral d
  let I : 𝓢(Ambient d, ℂ) →L[ℂ] ℂ := integralCLM ℂ volume
  let H : ℕ → 𝓢(Ambient d, ℂ) := fun j => G j - I (G j) • η
  have hIη : I η = 1 := hη
  have hIg : I g = 0 := hg
  refine ⟨H, ?_, ?_⟩
  · intro j
    refine ⟨(hc j).sub hcη.smul_left, ?_⟩
    change I (G j - I (G j) • η) = 0
    rw [map_sub, map_smul, hIη, smul_eq_mul, mul_one, sub_self]
  · have hi : Tendsto (fun j => I (G j)) atTop (𝓝 0) := by
      simpa only [hIg] using! I.continuous.tendsto g |>.comp ht
    have hs := hi.smul (tendsto_const_nhds (x := η))
    simpa only [zero_smul, sub_zero] using! ht.sub hs

theorem inverse_fourier_has_compact_mean_zero_approximants {d : ℕ}
    (g : 𝓢(Ambient d, ℂ)) (hg : (0 : Ambient d) ∉ tsupport g) :
    ∃ G : ℕ → 𝓢(Ambient d, ℂ),
      (∀ j, HasCompactSupport (G j) ∧ (∫ x, G j x) = 0) ∧ Tendsto G atTop (𝓝 (𝓕⁻ g)) :=
  exists_compact_mean_zero_schwartz_approximation (𝓕⁻ g)
    (inverse_fourier_mean_zero_of_support_away_origin g hg)

theorem tempered_distribution_zero_on_mean_zero_tests {d : ℕ}
    (T : 𝓢'(Ambient d, ℂ))
    (hT : ∀ g : 𝓢(Ambient d, ℂ), HasCompactSupport g → (∫ x, g x) = 0 → T g = 0)
    (g : 𝓢(Ambient d, ℂ)) (hg : (∫ x, g x) = 0) : T g = 0 := by
  obtain ⟨G, hG, ht⟩ := exists_compact_mean_zero_schwartz_approximation g hg
  have hlim := T.continuous.tendsto g |>.comp ht
  have hz : (fun j => T (G j)) = fun _ : ℕ => (0 : ℂ) :=
    funext fun j => hT (G j) (hG j).1 (hG j).2
  change Tendsto (fun j => T (G j)) atTop (𝓝 (T g)) at hlim
  rw [hz] at hlim
  exact tendsto_nhds_unique hlim tendsto_const_nhds

end

end RieszRectifiability

end OAI
