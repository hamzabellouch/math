import OAI.NumberTheory.Ostmann.Quadratic.QuadraticShortRowsScale

namespace OAI

/-! # The improved dyadic-row bound at the current induction exponent -/

namespace Ostmann

open scoped Classical BigOperators

theorem quadratic_dyadic_growth {ξ : ℝ} (h : QuadraticSieveGrowth ξ)
    (hξ : 1 ≤ ξ) (hξ' : ξ ≤ 2) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ M N : ℕ, 0 < M → 0 < N → ∀ v : ℕ → ℂ,
      (∑ m ∈ (oddSquarefreeRange (2 * M)).filter (M ≤ ·),
        ‖quadraticTransposeSum N v m‖ ^ 2) ≤
        C * ((M : ℝ) * N) ^ ε *
          ((M : ℝ) + (M : ℝ) ^ (1 - ξ) * (N : ℝ) ^ (2 * ξ - 1)) *
            quadraticSieveEnergy N v := by
  obtain ⟨η, hη, hηε, A, hA, ha⟩ := quadratic_long_rows h (by linarith) hξ' ε hε
  obtain ⟨B, hB, hb⟩ := h (ε / 4) (by positivity)
  let D := 8 * B * 2 ^ (ε / 4)
  refine ⟨A + D, by dsimp [D]; positivity, ?_⟩
  intro M N hM hN v
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hX : 1 ≤ (M : ℝ) * N := one_le_mul_of_one_le_of_one_le
    (by exact_mod_cast hM) (by exact_mod_cast hN)
  have hXp : 0 < (M : ℝ) * N := lt_of_lt_of_le zero_lt_one hX
  have hE : 0 ≤ quadraticSieveEnergy N v := Finset.sum_nonneg fun _ _ => sq_nonneg _
  by_cases hsep : 4 * (N : ℝ) * (((M : ℝ) * N) ^ η) ≤ M
  · apply (ha M N hM hN hsep v).trans
    have hD : 0 < D := by dsimp [D]; positivity
    gcongr
    linarith
  · have hY : 1 ≤ ((M : ℝ) * N) ^ η := Real.one_le_rpow hX hη.le
    have hs := quadratic_short_rows_scale hξ hξ' hMR hNR hY (le_of_lt (lt_of_not_ge hsep))
    have ht := quadraticTranspose_of_bound (hb (2 * M) N (by omega) hN) v
    have hsmall : 2 * (M : ℝ) + (N : ℝ) ^ ξ ≤
        4 * (((M : ℝ) * N) ^ η) *
          ((M : ℝ) + (M : ℝ) ^ (1 - ξ) * (N : ℝ) ^ (2 * ξ - 1)) := by
      have hm := mul_le_mul_of_nonneg_right hY hMR.le
      nlinarith only [hs, hm, hMR]
    have hpow : ((M : ℝ) * N) ^ (ε / 4) * ((M : ℝ) * N) ^ η ≤
        ((M : ℝ) * N) ^ ε := by
      rw [← Real.rpow_add hXp]
      exact Real.rpow_le_rpow_of_exponent_le hX (by linarith)
    have hprod : (((2 * M : ℕ) : ℝ) * N) ^ (ε / 4) =
        2 ^ (ε / 4) * ((M : ℝ) * N) ^ (ε / 4) := by
      simp only [Nat.cast_mul, Nat.cast_ofNat]
      rw [mul_assoc, Real.mul_rpow (by norm_num) hXp.le]
    apply (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun _ _ _ => sq_nonneg _)).trans (ht.trans ?_)
    simp only [Nat.cast_mul, Nat.cast_ofNat] at ht ⊢
    rw [show (2 * (M : ℝ) * N) ^ (ε / 4) =
      2 ^ (ε / 4) * ((M : ℝ) * N) ^ (ε / 4) by
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using hprod]
    calc
      _ ≤ 2 * (B * (2 ^ (ε / 4) * ((M : ℝ) * N) ^ (ε / 4)) *
          (4 * (((M : ℝ) * N) ^ η) *
            ((M : ℝ) + (M : ℝ) ^ (1 - ξ) * (N : ℝ) ^ (2 * ξ - 1)))) *
              quadraticSieveEnergy N v := by gcongr
      _ = D * (((M : ℝ) * N) ^ (ε / 4) * ((M : ℝ) * N) ^ η) *
          ((M : ℝ) + (M : ℝ) ^ (1 - ξ) * (N : ℝ) ^ (2 * ξ - 1)) *
            quadraticSieveEnergy N v := by dsimp [D]; ring
      _ ≤ (A + D) * ((M : ℝ) * N) ^ ε *
          ((M : ℝ) + (M : ℝ) ^ (1 - ξ) * (N : ℝ) ^ (2 * ξ - 1)) *
            quadraticSieveEnergy N v := by
        apply mul_le_mul_of_nonneg_right _ hE
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact mul_le_mul (by linarith) hpow (by positivity) (by dsimp [D]; positivity)

end Ostmann

end OAI
