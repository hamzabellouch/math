import OAI.NumberTheory.JointDickman.Analysis.MellinWeightedEnergy

namespace OAI

/-! # Scaled transfer of Dirichlet mean-square estimates to short windows -/
namespace JointDickman
open Finset MeasureTheory
open scoped SchwartzMap FourierTransform

theorem continuous_mellinPolynomial (S : Finset ℕ) (a : ℕ → ℂ) :
    Continuous (mellinPolynomial S a) := by
  apply continuous_finsetSum
  intro n _
  exact continuous_const.mul
    (continuous_additivePhase.comp (continuous_id.neg.mul_const _))

/-- A Dirichlet energy bound `A+B*T` gives the expected short-window cost
`A+B/δ`, with a constant depending only on the smoothing profile. -/
theorem mellinPacket_energy_of_spectral_bound (w : 𝓢(ℝ, ℂ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : Finset ℕ) (a : ℕ → ℂ)
      (δ : ℝ) (hδ : 0 < δ), δ ≤ 1 → ∀ A B : ℝ, 0 ≤ A → 0 ≤ B →
      (∀ T : ℝ, 1 ≤ T →
        (∫ t in -T..T, ‖mellinPolynomial S a t‖ ^ 2) ≤ A + B * T) →
      (∫ v : ℝ, ‖mellinPacket S a (normalizedSchwartzScale w δ hδ) v‖ ^ 2) ≤
        C * (A + B / δ) := by
  obtain ⟨C, hC, hCbound⟩ := schwartz_weighted_energy_bound (𝓕 w : 𝓢(ℝ, ℂ))
  refine ⟨C, hC, ?_⟩
  intro S a δ hδ hδ1 A B hA hB henergy
  let D := mellinPolynomial S a
  let F : ℝ → ℂ := fun u => D (u / δ)
  let G : ℝ → ℝ := fun t => ‖(𝓕 w : 𝓢(ℝ, ℂ)) (δ * t)‖ ^ 2 * ‖D t‖ ^ 2
  let p := mellinPacket S a (normalizedSchwartzScale w δ hδ)
  have hF : Continuous F := (continuous_mellinPolynomial S a).comp (continuous_id.div_const δ)
  have hi : Integrable G := by
    have hp := ((𝓕 p : 𝓢(ℝ, ℂ)).memLp 2).integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
    apply hp.congr
    filter_upwards [] with t
    dsimp only [G, p, D]
    rw [mellinPacket_fourier, normalizedSchwartzScale_fourier, norm_mul, mul_pow]
  have hscaledI : Integrable (fun u : ℝ =>
      ‖(𝓕 w : 𝓢(ℝ, ℂ)) u‖ ^ 2 * ‖F u‖ ^ 2) := by
    apply (hi.comp_div hδ.ne').congr
    filter_upwards [] with u
    dsimp only [G, F]
    rw [mul_div_cancel₀ u hδ.ne']
  have hscaled : ∀ T : ℝ, 1 ≤ T →
      (∫ u in -T..T, ‖F u‖ ^ 2) ≤ δ * A + B * T := by
    intro T hT
    have hTδ : 1 ≤ T / δ := (le_div_iff₀ hδ).mpr (by linarith)
    change (∫ u in -T..T, ‖D (u / δ)‖ ^ 2) ≤ _
    rw [intervalIntegral.integral_comp_div (fun u => ‖D u‖ ^ 2) hδ.ne']
    simp only [smul_eq_mul, neg_div]
    calc
      _ ≤ δ * (A + B * (T / δ)) := mul_le_mul_of_nonneg_left (henergy _ hTδ) hδ.le
      _ = _ := by field_simp
  have hb := hCbound F hF (δ * A) B (mul_nonneg hδ.le hA) hB hscaledI hscaled
  have hchange : (∫ u : ℝ, ‖(𝓕 w : 𝓢(ℝ, ℂ)) u‖ ^ 2 * ‖F u‖ ^ 2) =
      δ * ∫ t : ℝ, G t := by
    have hh := Measure.integral_comp_div G δ
    simpa only [G, F, mul_div_cancel₀ _ hδ.ne', abs_of_pos hδ, smul_eq_mul] using hh
  rw [scaled_mellinPacket_energy]
  change (∫ t : ℝ, G t) ≤ _
  calc
    _ = (∫ u : ℝ, ‖(𝓕 w : 𝓢(ℝ, ℂ)) u‖ ^ 2 * ‖F u‖ ^ 2) / δ := by
      rw [hchange, mul_div_cancel_left₀ _ hδ.ne']
    _ ≤ (C * (δ * A + B)) / δ := div_le_div_of_nonneg_right hb hδ.le
    _ = _ := by field_simp

end JointDickman

end OAI
