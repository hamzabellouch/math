import OAI.NumberTheory.Ostmann.Quadratic.QuadraticCorrectionPowerCost

namespace OAI

/-! # A small-power bound for the complete original gcd correction -/

namespace Ostmann

open scoped Classical BigOperators

theorem quadratic_gcd_corrections_power_bound {ξ η : ℝ} (h : QuadraticSieveGrowth ξ)
    (hξ : 1 / 2 ≤ ξ) (hξ' : ξ ≤ 2) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ M R D K : ℕ, 0 < M → 0 < R → Squarefree D → Odd D → D ≤ R → 0 < K →
      (K : ℝ) ≤ ((M : ℝ) * R) ^ 3 → ∀ v : ℕ → ℂ, (∀ n < R, v n = 0) →
        ‖quadraticGcdMomentCorrections M R K D (((M : ℝ) * R) ^ η) v‖ ≤
          C * (D : ℝ) ^ 2 * ((M : ℝ) * R) ^ (36 * η) *
            ((M : ℝ) + R + Real.sqrt M * (K : ℝ) ^ (ξ - 1 / 2)) * quadraticSieveEnergy (2 * R) v := by
  obtain ⟨A, hA, hc⟩ := quadratic_gcd_corrections_growth h hξ hξ' hη hη
  let B := 1 + (η * Real.log 2)⁻¹
  have hB : 0 < B := by dsimp [B]; positivity
  let C := 2380 * A * B ^ 4 * 4 ^ (9 * η)
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro M R D K hM hR hD ho hDR hK hKX v hv
  let X := (M : ℝ) * R
  let J := X ^ η
  let N := quadraticGcdBlockSize R D
  let Q := (2 * N) ^ 2
  let L := quadraticSecondWindow J
  let V := (M : ℝ) + R + Real.sqrt M * (K : ℝ) ^ (ξ - 1 / 2)
  let E := quadraticSieveEnergy (2 * R) v
  have hM₁ : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hR₁ : (1 : ℝ) ≤ R := by exact_mod_cast hR
  have hX : 1 ≤ X := one_le_mul_of_one_le_of_one_le hM₁ hR₁
  have hJ : 1 ≤ J := Real.one_le_rpow hX hη.le
  have hN : 0 < N := quadraticGcdBlockSize_pos hR (Nat.pos_of_ne_zero hD.ne_zero)
  have hNR : N ≤ R := quadraticGcdBlockSize_le (Nat.pos_of_ne_zero hD.ne_zero)
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hE : 0 ≤ E := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hb := hc M R D K hM hR hD ho hDR hK J hJ v hv
  have hscalar := quadratic_correction_scalar_sum (ε := η) (ξ := ξ)
    (show (0 : ℝ) ≤ M by positivity) hJ (show 1 ≤ D from Nat.pos_of_ne_zero hD.ne_zero) hNR
    (Q := Q) (K := K) (L := L)
  have hlog := quadratic_correction_logfactor_bound (ε := η) hη hJ hN hNR hK
  have hRX : (R : ℝ) ≤ X := by dsimp [X]; nlinarith
  have hpow := quadratic_original_power_cost hη.le hX (Nat.cast_nonneg R)
    (Nat.cast_nonneg N) (Nat.cast_nonneg K) hRX (by exact_mod_cast hNR) hKX
  calc
    _ ≤ A * (2 * D : ℝ) *
        (quadraticCorrectionScalar 1 η ξ M J N Q K L +
          quadraticSmallCorrectionScalar 1 η ξ M J (2 * D) N Q K L) * (2 * (R : ℝ)) ^ η * E := hb
    _ = A * ((2 * D : ℝ) *
        (quadraticCorrectionScalar 1 η ξ M J N Q K L +
          quadraticSmallCorrectionScalar 1 η ξ M J (2 * D) N Q K L)) * (2 * (R : ℝ)) ^ η * E := by ring
    _ ≤ A * (34 * (D : ℝ) ^ 2 * J * quadraticCorrectionLogFactor η N Q K L * V) *
        (2 * (R : ℝ)) ^ η * E := by gcongr
    _ ≤ A * (34 * (D : ℝ) ^ 2 * J *
        (70 * B ^ 4 * J ^ 2 * (K : ℝ) ^ η * ((2 * (R : ℝ)) ^ 2) ^ η *
          ((2 * (R : ℝ)) ^ η) ^ 2 * (4 * (K : ℝ) * N) ^ η) * V) *
        (2 * (R : ℝ)) ^ η * E := by gcongr
    _ = (2380 * A * B ^ 4 * (D : ℝ) ^ 2) *
        (J ^ 3 * (K : ℝ) ^ η * ((2 * (R : ℝ)) ^ 2) ^ η * ((2 * (R : ℝ)) ^ η) ^ 2 *
          (4 * (K : ℝ) * N) ^ η * (2 * (R : ℝ)) ^ η) * V * E := by ring
    _ ≤ (2380 * A * B ^ 4 * (D : ℝ) ^ 2) * (4 ^ (9 * η) * X ^ (36 * η)) * V * E := by gcongr
    _ = _ := by dsimp [C, X, V, E]; ring

end Ostmann

end OAI
