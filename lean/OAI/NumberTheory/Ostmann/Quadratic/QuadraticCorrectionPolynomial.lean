import OAI.NumberTheory.Ostmann.Quadratic.QuadraticGcdCorrectionsGrowth
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticDyadicCount

namespace OAI

/-! # Polynomial and logarithmic costs of the original correction parameters -/

namespace Ostmann

noncomputable def quadraticCorrectionLogFactor (ε : ℝ) (N Q K L : ℕ) : ℝ :=
  (2 * L + 1) * ((Nat.log 2 K + 1 : ℕ) : ℝ) * ((Nat.log 2 Q + 2 : ℕ) : ℝ) *
    ((Nat.log 2 (2 * N) + 1 : ℕ) : ℝ) ^ 2 * (4 * (K : ℝ) * N) ^ ε

theorem quadraticCorrectionLogFactor_nonneg (ε : ℝ) (N Q K L : ℕ) :
    0 ≤ quadraticCorrectionLogFactor ε N Q K L := by
  unfold quadraticCorrectionLogFactor
  positivity

theorem quadratic_correction_scalar_sum {M J ε ξ : ℝ} (hM : 0 ≤ M) (hJ : 1 ≤ J)
    {R D N Q K L : ℕ} (hD : 1 ≤ D) (hNR : N ≤ R) :
    (2 * D : ℝ) * (quadraticCorrectionScalar 1 ε ξ M J N Q K L +
      quadraticSmallCorrectionScalar 1 ε ξ M J (2 * D) N Q K L) ≤
      34 * (D : ℝ) ^ 2 * J * quadraticCorrectionLogFactor ε N Q K L *
        (M + R + Real.sqrt M * (K : ℝ) ^ (ξ - 1 / 2)) := by
  let x := Real.sqrt M * (K : ℝ) ^ (ξ - 1 / 2)
  let d := (D : ℝ) * J
  have hx : 0 ≤ x := by dsimp [x]; positivity
  have hd : 0 ≤ d := by dsimp [d]; positivity
  have hjd : J ≤ d := by
    dsimp [d]
    nlinarith [show (1 : ℝ) ≤ D by exact_mod_cast hD]
  have hnr : (N : ℝ) ≤ R := by exact_mod_cast hNR
  have h₁ := mul_le_mul_of_nonneg_right hjd hM
  have h₂ := mul_le_mul_of_nonneg_right (show J + 1 ≤ 2 * d by linarith) hx
  have h₃ := mul_le_mul_of_nonneg_left hnr (show 0 ≤ 16 * d by positivity)
  have hs : J * (M + x) + (x + 16 * d * N) ≤ 17 * d * (M + R + x) := by
    nlinarith only [h₁, h₂, h₃, mul_nonneg hd hM,
      mul_nonneg hd (Nat.cast_nonneg R), mul_nonneg hd hx]
  have hG := quadraticCorrectionLogFactor_nonneg ε N Q K L
  have hh := mul_le_mul_of_nonneg_left hs (mul_nonneg (show (0 : ℝ) ≤ 2 * D by positivity) hG)
  convert hh using 1 <;>
    dsimp [quadraticCorrectionScalar, quadraticSmallCorrectionScalar, quadraticCorrectionLogFactor, d, x] <;>
    push_cast <;> ring

theorem quadratic_second_window_upper {J : ℝ} (hJ : 1 ≤ J) :
    (quadraticSecondWindow J : ℝ) ≤ 17 * J ^ 2 ∧
      2 * (quadraticSecondWindow J : ℝ) + 1 ≤ 35 * J ^ 2 := by
  have hc := Nat.ceil_lt_add_one (show 0 ≤ 16 * J ^ 2 by positivity)
  change (quadraticSecondWindow J : ℝ) < 16 * J ^ 2 + 1 at hc
  have hj : 1 ≤ J ^ 2 := by nlinarith
  constructor <;> nlinarith

theorem quadratic_correction_logfactor_bound {ε η J : ℝ} (hη : 0 < η) (hJ : 1 ≤ J)
    {N R K : ℕ} (hN : 0 < N) (hNR : N ≤ R) (hK : 0 < K) :
    quadraticCorrectionLogFactor ε N ((2 * N) ^ 2) K (quadraticSecondWindow J) ≤
      70 * (1 + (η * Real.log 2)⁻¹) ^ 4 * J ^ 2 *
        (K : ℝ) ^ η * ((2 * (R : ℝ)) ^ 2) ^ η * ((2 * (R : ℝ)) ^ η) ^ 2 *
          (4 * (K : ℝ) * N) ^ ε := by
  let A := 1 + (η * Real.log 2)⁻¹
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hcountK := quadratic_dyadic_count_bound η hη K hK
  have hcountQ := quadratic_dyadic_count_bound η hη ((2 * N) ^ 2) (by nlinarith)
  have hcountN := quadratic_dyadic_count_bound η hη (2 * N) (by omega)
  have hNreal : (N : ℝ) ≤ R := by exact_mod_cast hNR
  have hpowN : (2 * (N : ℝ)) ^ η ≤ (2 * (R : ℝ)) ^ η :=
    Real.rpow_le_rpow (by positivity) (by linarith) hη.le
  have hpowQ : ((2 * (N : ℝ)) ^ 2) ^ η ≤ ((2 * (R : ℝ)) ^ 2) ^ η := by
    apply Real.rpow_le_rpow (by positivity) _ hη.le
    nlinarith [sq_nonneg ((R : ℝ) - N)]
  have hlogN : ((Nat.log 2 (2 * N) + 1 : ℕ) : ℝ) ≤ A * (2 * (R : ℝ)) ^ η := by
    apply hcountN.trans
    simp only [Nat.cast_mul, Nat.cast_ofNat]
    exact mul_le_mul_of_nonneg_left hpowN hA
  have hlogQ : ((Nat.log 2 ((2 * N) ^ 2) + 2 : ℕ) : ℝ) ≤
      2 * A * ((2 * (R : ℝ)) ^ 2) ^ η := by
    simp only [Nat.cast_pow, Nat.cast_mul, Nat.cast_ofNat] at hcountQ
    have hh := hcountQ.trans (mul_le_mul_of_nonneg_left hpowQ hA)
    have hbase : 1 ≤ ((Nat.log 2 ((2 * N) ^ 2) + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_left 1 _
    push_cast at hbase hh ⊢
    nlinarith
  have hwin := (quadratic_second_window_upper hJ).2
  unfold quadraticCorrectionLogFactor
  calc
    _ ≤ (35 * J ^ 2) * (A * (K : ℝ) ^ η) *
        (2 * A * ((2 * (R : ℝ)) ^ 2) ^ η) * (A * (2 * (R : ℝ)) ^ η) ^ 2 *
          (4 * (K : ℝ) * N) ^ ε := by gcongr
    _ = _ := by dsimp [A]; ring

end Ostmann

end OAI
