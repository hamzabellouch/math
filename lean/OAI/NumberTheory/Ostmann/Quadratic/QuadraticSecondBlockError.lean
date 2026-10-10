import OAI.NumberTheory.Ostmann.Quadratic.QuadraticBlockError

namespace OAI

/-! # The literal second-Poisson remainder summed over a coefficient block -/

namespace Ostmann

open scoped SchwartzMap

theorem quadratic_second_block_error (ρ : 𝓢(ℝ, ℂ)) (a : ℝ)
    (ha : 1 ≤ |a|) (hρ : ∀ t < 1 / 2, ρ t = 0) (A : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ M B J : ℝ,
      0 < M → 0 < B → 1 ≤ J → ∀ N e b : ℕ,
      2 ≤ N → 0 < e → B ≤ b → (b : ℝ) ≤ 2 * B → ∀ m : ℤ, ∀ v : ℕ → ℂ,
      ‖quadraticBlockError N m v (fun q =>
        ((M / ((e : ℝ) * Real.sqrt q) : ℝ) : ℂ) *
          quadraticSecondDyadicError ρ a ha M B N J e q b)‖ ≤
        (C * Real.sqrt M / (Real.sqrt e * Real.sqrt B) / J ^ A) *
          (2 * N) * quadraticSieveEnergy (2 * N) v := by
  obtain ⟨C, hC, hc⟩ := quadratic_second_error_normalized ρ a ha hρ A
  refine ⟨C, hC, ?_⟩
  intro M B J hM hB hJ N e b hN he hb hb' m v
  have hNR : 0 < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  apply quadratic_block_error_bound hN m v _ _ (by positivity)
  intro q hlo hhi hq
  apply hc M B N J hM hB hNR hJ e q b he hq hb hb'
  · exact_mod_cast hlo
  · exact_mod_cast hhi

end Ostmann

end OAI
