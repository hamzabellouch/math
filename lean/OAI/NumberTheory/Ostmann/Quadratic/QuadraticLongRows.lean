import OAI.NumberTheory.Ostmann.Quadratic.QuadraticBalancedScale

namespace OAI

/-! # The improved bound in the long-row range -/

namespace Ostmann

open scoped Classical BigOperators

theorem quadratic_long_rows {ξ : ℝ} (h : QuadraticSieveGrowth ξ)
    (hξ : 1 / 2 ≤ ξ) (hξ' : ξ ≤ 2) (ε : ℝ) (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ η ≤ ε / 4 ∧ ∃ C : ℝ, 0 < C ∧ ∀ M N : ℕ,
      0 < M → 0 < N → 4 * (N : ℝ) * (((M : ℝ) * N) ^ η) ≤ M →
      ∀ v : ℕ → ℂ,
        (∑ m ∈ (oddSquarefreeRange (2 * M)).filter (M ≤ ·),
          ‖quadraticTransposeSum N v m‖ ^ 2) ≤
          C * ((M : ℝ) * N) ^ ε *
            ((M : ℝ) + (M : ℝ) ^ (1 - ξ) * (N : ℝ) ^ (2 * ξ - 1)) *
              quadraticSieveEnergy N v := by
  obtain ⟨η, hη, hηε, C, hC, hc⟩ := quadratic_rough_power_growth h hξ hξ'
    (ε / 4) (by positivity)
  refine ⟨η, hη, hηε, 300 * C, by positivity, ?_⟩
  intro M N hM hN hsep v
  let K := quadraticBalancedKernel η M N
  obtain ⟨hK, hKM, _, _⟩ := quadratic_balanced_kernel_bounds hη.le hM hN hsep
  have hcut := quadratic_balanced_kernel_cutoff hη.le hM hN hsep
  have hb := hc M N K hM hN hK hKM.le hcut v
  have hs := quadratic_balanced_scale hξ hξ' hη.le hM hN hsep
  have hX : 1 ≤ (M : ℝ) * N := one_le_mul_of_one_le_of_one_le
    (by exact_mod_cast hM) (by exact_mod_cast hN)
  have hXp : 0 < (M : ℝ) * N := lt_of_lt_of_le zero_lt_one hX
  have hpow : (((M : ℝ) * N) ^ (ε / 4)) * ((((M : ℝ) * N) ^ η) ^ 2) ≤
      ((M : ℝ) * N) ^ ε := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hXp.le, ← Real.rpow_add hXp]
    exact Real.rpow_le_rpow_of_exponent_le hX (by linarith)
  have hE : 0 ≤ quadraticSieveEnergy N v := Finset.sum_nonneg fun _ _ => sq_nonneg _
  apply (quadratic_rough_dyadic_domination hM hKM v).trans (hb.trans ?_)
  calc
    _ ≤ C * ((M : ℝ) * N) ^ (ε / 4) *
        (300 * ((((M : ℝ) * N) ^ η) ^ 2) *
          ((M : ℝ) + (M : ℝ) ^ (1 - ξ) * (N : ℝ) ^ (2 * ξ - 1))) *
            quadraticSieveEnergy N v := by gcongr
    _ = (300 * C) * (((M : ℝ) * N) ^ (ε / 4) * ((((M : ℝ) * N) ^ η) ^ 2)) *
        ((M : ℝ) + (M : ℝ) ^ (1 - ξ) * (N : ℝ) ^ (2 * ξ - 1)) *
          quadraticSieveEnergy N v := by ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ hE
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_left hpow (by positivity)

end Ostmann

end OAI
