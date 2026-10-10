import OAI.NumberTheory.Ostmann.Quadratic.QuadraticSecondCutoffs

namespace OAI

/-! # The second Poisson estimate with the literal dyadic square argument -/

namespace Ostmann

open scoped Classical BigOperators SchwartzMap FourierTransform

noncomputable def quadraticSecondDyadicCore (ρ : 𝓢(ℝ, ℂ)) (a : ℝ) (ha : 1 ≤ |a|)
    (M B N J : ℝ) (e q b : ℕ) : ℂ :=
  let X₀ := Real.sqrt ((e : ℝ) * N ^ 2 / (M * B))
  quadraticSecondPoissonCore q ρ a ha (quadraticSecondScale M e q b)
    (quadraticSecondLower X₀ J) (quadraticSecondUpper X₀ J) (quadraticSecondWindow J)

theorem quadratic_second_dyadic (ρ : 𝓢(ℝ, ℂ)) (a : ℝ)
    (ha : 1 ≤ |a|) (hρ : ∀ t < 1 / 2, ρ t = 0) (A : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ M B N J : ℝ,
      0 < M → 0 < B → 0 < N → 1 ≤ J →
      ∀ e q b : ℕ, 0 < e → q ≠ 1 → B ≤ b → (b : ℝ) ≤ 2 * B →
      N ^ 2 ≤ q → (q : ℝ) ≤ 4 * N ^ 2 →
      ‖(∑' c : ℕ+, (1 : DirichletCharacter ℂ q) (c : ZMod q) *
        𝓕 ρ (a * b * (c : ℝ) ^ 2 / ((e : ℝ) * q / M))) -
          quadraticSecondDyadicCore ρ a ha M B N J e q b‖ ≤
        C * quadraticSecondScale M e q b / J ^ A := by
  obtain ⟨C, hC, hc⟩ := quadratic_second_poisson ρ a ha hρ A
  refine ⟨C, hC, ?_⟩
  intro M B N J hM hB hN hJ e q b he hq1 hb hb' hq hq'
  have hbR : 0 < (b : ℝ) := hB.trans_le hb
  have hqR : 0 < (q : ℝ) := (sq_pos_of_pos hN).trans_le hq
  have hb₀ : 0 < b := by exact_mod_cast hbR
  have hq₀ : 0 < q := by exact_mod_cast hqR
  let : NeZero q := ⟨hq₀.ne'⟩
  let X₀ := Real.sqrt ((e : ℝ) * N ^ 2 / (M * B))
  have hX₀ : 0 < X₀ := Real.sqrt_pos.mpr (by positivity)
  have hX := quadraticSecondScale_pos hM he hq₀ hb₀
  obtain ⟨hlo, hhi⟩ := quadraticSecondScale_dyadic hM hB hN he hb hb' hq hq'
  obtain ⟨hU, hV, hUX, hXV, hL⟩ := quadratic_second_cutoffs hX₀ hJ hlo hhi
  have hh := hc q hq1 (quadraticSecondScale M e q b)
    (quadraticSecondLower X₀ J) (quadraticSecondUpper X₀ J) J
    hX hU hV hJ hUX hXV (quadraticSecondWindow J) hL
  simpa only [quadraticSecondScale_argument hM he hq₀ hb₀,
    quadraticSecondDyadicCore, X₀] using hh

end Ostmann

end OAI
