import OAI.NumberTheory.Ostmann.Quadratic.QuadraticSmallGcdGrowth
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticSmallGcdPowerSaving

namespace OAI

/-! # Uniform summation of the bounded common divisors -/

namespace Ostmann

open scoped Classical BigOperators

noncomputable def quadraticDescentScale (ξ : ℝ) (M N K : ℕ) : ℝ :=
  (M : ℝ) + N + Real.sqrt M * (K : ℝ) ^ (ξ - 1 / 2) +
    Real.sqrt M * N / Real.sqrt K

theorem quadraticDescentScale_nonneg (ξ : ℝ) (M N K : ℕ) :
    0 ≤ quadraticDescentScale ξ M N K := by
  unfold quadraticDescentScale
  positivity

theorem quadraticDescentScale_mono {ξ : ℝ} {M N R K : ℕ} (h : R ≤ N) :
    quadraticDescentScale ξ M R K ≤ quadraticDescentScale ξ M N K := by
  unfold quadraticDescentScale
  gcongr

theorem quadratic_small_gcd_sum_growth {ξ η : ℝ} (h : QuadraticSieveGrowth ξ)
    (hξ : 1 / 2 ≤ ξ) (hξ' : ξ ≤ 2) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ M N R K D₀ : ℕ,
      0 < M → 0 < R → R ≤ N → 0 < D₀ → D₀ < R → 0 < K → K ≤ M →
      2 * (2 * (N : ℝ)) ^ 2 * (((M : ℝ) * N) ^ η) ≤ (M : ℝ) * ((K : ℝ) + 1) →
      ∀ v : ℕ → ℂ, (∀ n < R, v n = 0) →
        (∑ D ∈ (Finset.Icc 1 (2 * R)).filter (fun D => D ≤ D₀),
          ‖quadraticRoughGcdMoment M (2 * R) K D v‖) ≤
          C * ((M : ℝ) * N) ^ (36 * η) * (D₀ : ℝ) ^ 5 *
            quadraticDescentScale ξ M N K * quadraticSieveEnergy (2 * R) v := by
  obtain ⟨C, hC, hc⟩ := quadratic_small_gcd_growth h hξ hξ' hη
  refine ⟨C, hC, ?_⟩
  intro M N R K D₀ hM hR hRN hD₀ hDR hK hKM hcut v hv
  have hMR : 1 ≤ (M : ℝ) * R := one_le_mul_of_one_le_of_one_le
    (by exact_mod_cast hM) (by exact_mod_cast hR)
  have hMX : (M : ℝ) ≤ (M : ℝ) * R := by
    nlinarith [show (1 : ℝ) ≤ R by exact_mod_cast hR]
  have hKX : (K : ℝ) ≤ ((M : ℝ) * R) ^ 3 :=
    (show (K : ℝ) ≤ M by exact_mod_cast hKM).trans
      (hMX.trans (le_self_pow₀ hMR (by norm_num)))
  have hNR : (R : ℝ) ≤ N := by exact_mod_cast hRN
  have hpow : ((M : ℝ) * R) ^ (36 * η) ≤ ((M : ℝ) * N) ^ (36 * η) := by
    apply Real.rpow_le_rpow (by positivity) _ (by positivity)
    exact mul_le_mul_of_nonneg_left hNR (Nat.cast_nonneg M)
  have hcutR : 2 * (2 * (R : ℝ)) ^ 2 * (((M : ℝ) * R) ^ η) ≤
      (M : ℝ) * ((K : ℝ) + 1) := by
    apply le_trans _ hcut
    gcongr
  let A := C * ((M : ℝ) * N) ^ (36 * η) * (D₀ : ℝ) ^ 4 *
    quadraticDescentScale ξ M N K * quadraticSieveEnergy (2 * R) v
  have hA : 0 ≤ A := by
    dsimp [A]
    exact mul_nonneg (mul_nonneg (by positivity) (quadraticDescentScale_nonneg _ _ _ _))
      (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  have hs : (Finset.Icc 1 (2 * R)).filter (fun D => D ≤ D₀) ⊆ Finset.Icc 1 D₀ := by
    intro D hD
    exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp (Finset.mem_filter.mp hD).1).1,
      (Finset.mem_filter.mp hD).2⟩
  calc
    _ ≤ ∑ _D ∈ (Finset.Icc 1 (2 * R)).filter (fun D => D ≤ D₀), A := by
      apply Finset.sum_le_sum
      intro D hmem
      have hDle := (Finset.mem_filter.mp hmem).2
      by_cases hD : Squarefree D
      · by_cases ho : Odd D
        · apply (hc M R D K hM hR hD ho (hDle.trans_lt hDR) hK hKX hcutR v hv).trans
          change C * ((M : ℝ) * R) ^ (36 * η) * (D : ℝ) ^ 4 *
            quadraticDescentScale ξ M R K * quadraticSieveEnergy (2 * R) v ≤ A
          dsimp only [A]
          apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
          exact mul_le_mul
            (mul_le_mul (mul_le_mul_of_nonneg_left hpow hC.le)
              (pow_le_pow_left₀ (Nat.cast_nonneg D) (by exact_mod_cast hDle) 4)
              (by positivity) (by positivity))
            (quadraticDescentScale_mono hRN) (quadraticDescentScale_nonneg _ _ _ _)
            (by positivity)
        · rw [quadratic_rough_gcd_moment_zero (quadraticGcdPairs_empty_of_not_odd (2 * R) D ho),
            norm_zero]
          exact hA
      · rw [quadratic_rough_gcd_moment_zero (quadraticGcdPairs_empty_of_not_squarefree (2 * R) D hD),
          norm_zero]
        exact hA
    _ ≤ ∑ _D ∈ Finset.Icc 1 D₀, A :=
      Finset.sum_le_sum_of_subset_of_nonneg hs (fun _ _ _ => hA)
    _ = _ := by simp [A]; ring

end Ostmann

end OAI
