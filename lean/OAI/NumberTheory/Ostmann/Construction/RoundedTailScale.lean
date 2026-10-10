import OAI.NumberTheory.Ostmann.Characters.CharacterRoundedEndpoint

namespace OAI

/-! # Integer endpoints for a whole harmonic prime band at every real scale -/
namespace Ostmann
open Filter

/-- Choose a literal integer endpoint above the band, while retaining a
linear bound on the logarithm of its logarithm. -/
theorem eventual_rounded_tail_scale (β : ℝ) (hβ : 0 < β) (T₀ : ℝ) :
    ∀ᶠ L : ℝ in atTop, ∃ (X : ℕ) (T : ℝ), T₀ ≤ T ∧
      (X : ℝ) = Real.exp T ∧
      Real.log T ≤ (β + 1) * L + Real.log 1000 ∧
      Real.exp (β * L) ≤ T / 4 := by
  have hg := Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop (by linarith only [hβ] : 0 < β + 1))
  filter_upwards [hg.eventually (eventually_ge_atTop T₀), eventually_ge_atTop (4 : ℝ)]
    with L hlarge hL
  let v := (β + 1) * L
  have hv : 2 ≤ v := by dsimp [v]; nlinarith only [hL, hβ]
  obtain ⟨hX1, hX, _, hτlo, _, _, _, hlog⟩ :=
    character_rounded_endpoint_bounds 0 v 0 hv (by linarith only [hv])
  let X := characterRoundedEndpoint 0 v
  let T := characterEndpointFactor 0 * characterRoundedTau 0 v
  have hf : characterEndpointFactor 0 = 1000 := by norm_num [characterEndpointFactor]
  have hT : Real.exp v ≤ T := by
    dsimp only [T]
    rw [hf]
    nlinarith only [hτlo, Real.exp_pos v]
  refine ⟨X, T, hlarge.trans hT, hX, ?_, ?_⟩
  · rw [hX, Real.log_exp, hf] at hlog
    simpa only [T, hf] using hlog
  · have he : 4 ≤ Real.exp L := by linarith only [Real.add_one_le_exp L, hL]
    have hh := mul_le_mul_of_nonneg_left he (Real.exp_nonneg (β * L))
    have heq : Real.exp (β * L) * Real.exp L = Real.exp v := by
      rw [← Real.exp_add]
      congr 1
      dsimp [v]
      ring
    rw [heq] at hh
    linarith only [hh, hT]

end Ostmann

end OAI
