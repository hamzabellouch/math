import OAI.NumberTheory.Ostmann.Quadratic.QuadraticDilationPowerCost

namespace OAI

/-! # Prime dilation improves the exponent on every dyadic row interval -/

namespace Ostmann

open scoped Classical BigOperators

theorem quadratic_dyadic_improvement {ξ : ℝ} (h : QuadraticSieveGrowth ξ)
    (hξ : 1 ≤ ξ) (hξ' : ξ ≤ 2) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ M N : ℕ, 0 < M → 0 < N →
      QuadraticRowBound ((oddSquarefreeRange (2 * M)).filter (M ≤ ·)) N
        (C * ((M : ℝ) * N) ^ ε * ((M : ℝ) + (N : ℝ) ^ quadraticImprovedExponent ξ)) := by
  let δ := min (ε / 2) 1
  let a := ε / 8
  have hδ : 0 < δ := lt_min (by positivity) (by norm_num)
  have hδ₁ : δ ≤ 1 := min_le_right _ _
  have ha : 0 < a := by dsimp [a]; positivity
  have hexp : 4 * a + δ ≤ ε := by
    have hd := min_le_left (ε / 2) (1 : ℝ)
    dsimp [a, δ]
    linarith
  obtain ⟨C₀, hC₀, hdilate⟩ := quadratic_dyadic_dilation δ hδ
  obtain ⟨B, hB, hwide⟩ := quadratic_wide_rows_growth h hξ hξ' a ha
  let D := C₀ + 1
  let F := 3 * D * (4 * D) ^ a
  have hD : 1 ≤ D := by dsimp [D]; linarith
  have hF : 0 < F := by dsimp [F]; positivity
  refine ⟨4 * B * F, by positivity, ?_⟩
  intro M N hM hN
  let Q := quadraticDilationCutoff C₀ δ (quadraticImprovedExponent ξ) M N
  let L := Q * M
  have hM₁ : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hN₁ : (1 : ℝ) ≤ N := by exact_mod_cast hN
  obtain ⟨hQ, hL, hLu⟩ := quadratic_dilation_cutoff_bounds (by linarith : 1 ≤ C₀) hδ.le hM hN
    (p := quadraticImprovedExponent ξ)
  have hLp : (0 : ℝ) < L := lt_of_lt_of_le (by positivity) hL
  have hLn : 0 < L := by exact_mod_cast hLp
  have hcost := quadratic_dilation_power_cost hξ hδ.le hδ₁ ha.le hD hM₁ hN₁ hL hLu
  have hX : 1 ≤ (M : ℝ) * N := one_le_mul_of_one_le_of_one_le hM₁ hN₁
  have hp : ((M : ℝ) * N) ^ (4 * a + δ) ≤ ((M : ℝ) * N) ^ ε :=
    Real.rpow_le_rpow_of_exponent_le hX hexp
  let U := B * (((L : ℝ) * N) ^ a) *
    ((L : ℝ) + (L : ℝ) ^ (1 - ξ) * (N : ℝ) ^ (2 * ξ - 1))
  have hU : 0 ≤ U := by dsimp [U]; positivity
  have hb := hdilate M N Q hM hN hQ U hU (hwide L N hLn hN)
  apply hb.mono_constant
  have hscale : 0 ≤ (M : ℝ) + (N : ℝ) ^ quadraticImprovedExponent ξ := by positivity
  calc
    4 * U = (4 * B) * ((((L : ℝ) * N) ^ a) *
        ((L : ℝ) + (L : ℝ) ^ (1 - ξ) * (N : ℝ) ^ (2 * ξ - 1))) := by dsimp [U]; ring
    _ ≤ (4 * B) * (F * ((M : ℝ) * N) ^ (4 * a + δ) *
        ((M : ℝ) + (N : ℝ) ^ quadraticImprovedExponent ξ)) :=
      mul_le_mul_of_nonneg_left hcost (by positivity)
    _ ≤ (4 * B) * (F * ((M : ℝ) * N) ^ ε *
        ((M : ℝ) + (N : ℝ) ^ quadraticImprovedExponent ξ)) := by gcongr
    _ = _ := by ring

end Ostmann

end OAI
