import OAI.NumberTheory.Ostmann.Quadratic.QuadraticSmallEnvelope
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticSmallTotalIdentity
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticGcdTwistMoment
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticGrowthDivisorBudget

namespace OAI

/-! # Original small-kernel corrections bounded by the original coefficient energy -/

namespace Ostmann

open scoped Classical BigOperators

theorem quadratic_small_total_growth {ξ ε δ : ℝ} (h : QuadraticSieveGrowth ξ)
    (hξ : 1 / 2 ≤ ξ) (hξ' : ξ ≤ 2) (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ A : ℝ, 0 < A ∧ ∀ M J : ℝ, 0 < M → 1 ≤ J →
      ∀ R D K : ℕ, 0 < R → Squarefree D → Odd D → 0 < K → ∀ v : ℕ → ℂ,
        ‖quadraticGcdSmallTotal M J R D K v v‖ ≤
          A * (2 * D : ℝ) * quadraticSmallCorrectionScalar 1 ε ξ M J (2 * D)
            (quadraticGcdBlockSize R D) ((2 * quadraticGcdBlockSize R D) ^ 2) K
              (quadraticSecondWindow J) * (2 * (R : ℝ)) ^ δ * quadraticSieveEnergy (2 * R) v := by
  obtain ⟨A₀, hA₀, hc⟩ := quadratic_small_combination_growth
  obtain ⟨C, hC, hmat⟩ := quadratic_growth_cutoff_bounds h hε
  obtain ⟨A₁, hA₁, hmom⟩ := quadratic_gcd_block_divisor_moment δ hδ
  refine ⟨A₀ * C * A₁, by positivity, ?_⟩
  intro M J hM hJ R D K hR hD ho hK v
  have hD₀ : 0 < D := Nat.pos_of_ne_zero hD.ne_zero
  let N := quadraticGcdBlockSize R D
  let v' := quadraticGcdBlockCoeff R D v
  have hN : 0 < N := quadraticGcdBlockSize_pos hR hD₀
  have hQ : 1 ≤ (2 * N) ^ 2 := by nlinarith
  let S := quadraticSmallCorrectionScalar C ε ξ M J (2 * D) N ((2 * N) ^ 2) K (quadraticSecondWindow J)
  have hS : 0 ≤ S := quadraticSmallCorrectionScalar_nonneg hC.le hM.le (by linarith) _ _ _ _ _
  let T := A₀ * S * (A₁ * (2 * (R : ℝ)) ^ δ * quadraticSieveEnergy (2 * R) v)
  have hv : 0 ≤ quadraticSieveEnergy (2 * R) v := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hT : 0 ≤ T := by
    dsimp [T]
    exact mul_nonneg (mul_nonneg hA₀.le hS)
      (mul_nonneg (mul_nonneg hA₁.le (Real.rpow_nonneg (by positivity) _)) hv)
  rw [quadratic_gcd_small_total_split hM J hD ho]
  calc
    _ ≤ ∑ e ∈ (2 * D).divisors, T := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro e he
      have he₀ := Nat.pos_of_mem_divisors he
      have heD := Nat.le_of_dvd (by omega : 0 < 2 * D) (Nat.dvd_of_mem_divisors he)
      have hb := hc C ε ξ M J hC.le hε.le hξ hξ' e N ((2 * N) ^ 2) K (quadraticSecondWindow J)
        hM he₀ hN hQ hK hJ (fun _ b => D.Coprime b) v'
        (fun B hB _ => hmat (2 * B) (2 * N) (by omega) (by omega))
      apply hb.trans
      apply mul_le_mul
      · apply mul_le_mul_of_nonneg_left _ hA₀.le
        exact quadraticSmallCorrectionScalar_mono hC.le (by linarith) heD
      · exact hmom R D hD ho v
      · exact Finset.sum_nonneg (fun _ _ => by positivity)
      · exact mul_nonneg hA₀.le hS
    _ = ((2 * D).divisors.card : ℝ) * T := by simp
    _ ≤ (2 * D : ℝ) * T := by
      apply mul_le_mul_of_nonneg_right _ hT
      exact_mod_cast Nat.card_divisors_le_self (2 * D)
    _ = _ := by
      dsimp only [T, S, N]
      rw [quadraticSmallCorrectionScalar_scale]
      ring

end Ostmann

end OAI
