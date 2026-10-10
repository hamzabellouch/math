import OAI.NumberTheory.Ostmann.Quadratic.QuadraticErrorPower

namespace OAI

/-! # Arbitrary power saving for the complete second-Poisson truncation error -/

namespace Ostmann

open scoped SchwartzMap

theorem quadratic_second_error_arbitrary_power (ρ : 𝓢(ℝ, ℂ)) (a : ℝ)
    (ha : 1 ≤ |a|) (hρ : ∀ t < 1 / 2, ρ t = 0) {δ : ℝ} (hδ : 0 < δ) (P : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ M B : ℝ,
      1 ≤ M → 1 ≤ B → ∀ N e b : ℕ,
      2 ≤ N → 0 < e → B ≤ b → (b : ℝ) ≤ 2 * B → ∀ m : ℤ, ∀ v : ℕ → ℂ,
      ‖quadraticBlockError N m v (fun q =>
        ((M / ((e : ℝ) * Real.sqrt q) : ℝ) : ℂ) *
          quadraticSecondDyadicError ρ a ha M B N ((M * N) ^ δ) e q b)‖ ≤
        C / (M * N) ^ P * quadraticSieveEnergy (2 * N) v := by
  obtain ⟨A, hA⟩ := quadratic_error_power_choice hδ P
  obtain ⟨C, hC, hc⟩ := quadratic_second_block_error ρ a ha hρ A
  refine ⟨2 * C, by positivity, ?_⟩
  intro M B hM hB N e b hN he hb hb' m v
  have hNR : 1 ≤ (N : ℝ) := by exact_mod_cast (by omega : 1 ≤ N)
  have hMN : 1 ≤ M * N := one_le_mul_of_one_le_of_one_le hM hNR
  have hJ : 1 ≤ (M * N) ^ δ := Real.one_le_rpow hMN hδ.le
  have hM₀ : 0 < M := zero_lt_one.trans_le hM
  have hB₀ : 0 < B := zero_lt_one.trans_le hB
  have heR : 1 ≤ (e : ℝ) := by exact_mod_cast he
  have hden : 1 ≤ Real.sqrt e * Real.sqrt B :=
    one_le_mul_of_one_le_of_one_le (Real.one_le_sqrt.mpr heR) (Real.one_le_sqrt.mpr hB)
  have hroot : Real.sqrt M / (Real.sqrt e * Real.sqrt B) ≤ Real.sqrt M :=
    div_le_self (Real.sqrt_nonneg _) hden
  have henergy : 0 ≤ quadraticSieveEnergy (2 * N) v :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hp := hA M N hM hNR
  calc
    _ ≤ (C * Real.sqrt M / (Real.sqrt e * Real.sqrt B) / ((M * N) ^ δ) ^ A) *
        (2 * N) * quadraticSieveEnergy (2 * N) v :=
      hc M B ((M * N) ^ δ) hM₀ hB₀ hJ N e b hN he hb hb' m v
    _ = (C * (Real.sqrt M / (Real.sqrt e * Real.sqrt B))) *
        ((2 * N) / ((M * N) ^ δ) ^ A) * quadraticSieveEnergy (2 * N) v := by ring
    _ ≤ (C * Real.sqrt M) * ((2 * N) / ((M * N) ^ δ) ^ A) *
        quadraticSieveEnergy (2 * N) v := by gcongr
    _ = C * (Real.sqrt M * (2 * N) / ((M * N) ^ δ) ^ A) *
        quadraticSieveEnergy (2 * N) v := by ring
    _ ≤ C * (2 / (M * N) ^ P) * quadraticSieveEnergy (2 * N) v := by gcongr
    _ = _ := by ring

end Ostmann

end OAI
