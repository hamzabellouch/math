import OAI.NumberTheory.Ostmann.Quadratic.QuadraticSecondMain

namespace OAI

/-! # The second-transform error after the original Gauss normalization -/

namespace Ostmann

open scoped Classical BigOperators SchwartzMap FourierTransform

noncomputable def quadraticSecondDyadicError (ρ : 𝓢(ℝ, ℂ)) (a : ℝ) (ha : 1 ≤ |a|)
    (M B N J : ℝ) (e q b : ℕ) : ℂ :=
  (∑' c : ℕ+, (1 : DirichletCharacter ℂ q) (c : ZMod q) *
    𝓕 ρ (a * b * (c : ℝ) ^ 2 / ((e : ℝ) * q / M))) -
      quadraticSecondDyadicCore ρ a ha M B N J e q b

theorem quadratic_second_error_normalized (ρ : 𝓢(ℝ, ℂ)) (a : ℝ)
    (ha : 1 ≤ |a|) (hρ : ∀ t < 1 / 2, ρ t = 0) (A : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ M B N J : ℝ,
      0 < M → 0 < B → 0 < N → 1 ≤ J →
      ∀ e q b : ℕ, 0 < e → q ≠ 1 → B ≤ b → (b : ℝ) ≤ 2 * B →
      N ^ 2 ≤ q → (q : ℝ) ≤ 4 * N ^ 2 →
      ‖((M / ((e : ℝ) * Real.sqrt q) : ℝ) : ℂ) *
        quadraticSecondDyadicError ρ a ha M B N J e q b‖ ≤
          C * Real.sqrt M / (Real.sqrt e * Real.sqrt B) / J ^ A := by
  obtain ⟨C, hC, hc⟩ := quadratic_second_dyadic ρ a ha hρ A
  refine ⟨C, hC, ?_⟩
  intro M B N J hM hB hN hJ e q b he hq1 hb hb' hq hq'
  have hqR : 0 < (q : ℝ) := (sq_pos_of_pos hN).trans_le hq
  have hq₀ : 0 < q := by exact_mod_cast hqR
  have hb₀ : 0 < b := by exact_mod_cast (hB.trans_le hb)
  have heR : 0 < (e : ℝ) := by exact_mod_cast he
  have hJ₀ : 0 < J := lt_of_lt_of_le zero_lt_one hJ
  have hm : 0 < M / ((e : ℝ) * Real.sqrt q) := by positivity
  have hh := hc M B N J hM hB hN hJ e q b he hq1 hb hb' hq hq'
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hm]
  calc
    _ ≤ (M / ((e : ℝ) * Real.sqrt q)) *
        (C * quadraticSecondScale M e q b / J ^ A) :=
      mul_le_mul_of_nonneg_left hh hm.le
    _ = C * (M / ((e : ℝ) * Real.sqrt q) * quadraticSecondScale M e q b) / J ^ A := by ring
    _ = C * Real.sqrt M / (Real.sqrt e * Real.sqrt b) / J ^ A := by
      rw [quadratic_second_main_normalizer hM he hq₀ hb₀]
      ring
    _ ≤ _ := by
      gcongr

end Ostmann

end OAI
