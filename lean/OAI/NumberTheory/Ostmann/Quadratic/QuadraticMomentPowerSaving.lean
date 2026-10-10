import OAI.NumberTheory.Ostmann.Quadratic.QuadraticFirstKernelError

namespace OAI

/-! # Arbitrary power saving for both whole-moment Poisson remainders -/

namespace Ostmann

theorem quadratic_moment_error_power_choice {δ : ℝ} (hδ : 0 < δ) (P : ℕ) :
    ∃ A : ℕ, ∀ X : ℝ, 1 ≤ X → X ^ 5 / (X ^ δ) ^ A ≤ 1 / X ^ P := by
  obtain ⟨A, hA⟩ := exists_nat_ge (((P : ℝ) + 5) / δ)
  refine ⟨A, ?_⟩
  intro X hX
  have hX₀ : 0 < X := zero_lt_one.trans_le hX
  have hexp : (P : ℝ) + 5 ≤ δ * A := by
    have hh := (div_le_iff₀ hδ).mp hA
    nlinarith
  have hp : X ^ (P + 5) ≤ (X ^ δ) ^ A := by
    calc
      _ = X ^ ((P : ℝ) + 5) := by rw [← Real.rpow_natCast]; norm_num
      _ ≤ X ^ (δ * A) := Real.rpow_le_rpow_of_exponent_le hX hexp
      _ = _ := by rw [Real.rpow_mul hX₀.le, Real.rpow_natCast]
  calc
    _ ≤ X ^ 5 / X ^ (P + 5) :=
      div_le_div_of_nonneg_left (by positivity) (pow_pos hX₀ _) hp
    _ = _ := by rw [pow_add]; field_simp

theorem quadratic_first_error_arbitrary_power {δ : ℝ} (hδ : 0 < δ) (P : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ M N K : ℕ, 1 ≤ M → 1 ≤ N →
      2 * (N : ℝ) ^ 2 * (((M : ℝ) * N) ^ δ) ≤ (M : ℝ) * ((K : ℝ) + 1) →
      ∀ v : ℕ → ℂ, ‖quadraticFirstOffDiagonalError M N K v‖ ≤
        C / (((M : ℝ) * N) ^ P) * quadraticSieveEnergy N v := by
  obtain ⟨A, hA⟩ := quadratic_moment_error_power_choice hδ P
  obtain ⟨C, hC, hc⟩ := quadratic_first_off_diagonal_error A
  refine ⟨C, hC, ?_⟩
  intro M N K hM hN hcut v
  have hMR : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hMN : 1 ≤ (M : ℝ) * N := one_le_mul_of_one_le_of_one_le hMR hNR
  have hJ : 1 ≤ ((M : ℝ) * N) ^ δ := Real.one_le_rpow hMN hδ.le
  have hcost : (N : ℝ) ^ 5 / M ≤ ((M : ℝ) * N) ^ 5 := by
    apply (div_le_self (by positivity) hMR).trans
    apply pow_le_pow_left₀ (by positivity)
    nlinarith [mul_nonneg (sub_nonneg.mpr hMR) (show (0 : ℝ) ≤ N by positivity)]
  have he := hA ((M : ℝ) * N) hMN
  have hEn : 0 ≤ quadraticSieveEnergy N v := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  calc
    _ ≤ C * (N : ℝ) ^ 5 / ((M : ℝ) * (((M : ℝ) * N) ^ δ) ^ A) *
        quadraticSieveEnergy N v := hc M N K (by omega) _ hJ hcut v
    _ = C * ((N : ℝ) ^ 5 / M / (((M : ℝ) * N) ^ δ) ^ A) * quadraticSieveEnergy N v := by ring
    _ ≤ C * (((M : ℝ) * N) ^ 5 / (((M : ℝ) * N) ^ δ) ^ A) * quadraticSieveEnergy N v := by gcongr
    _ ≤ C * (1 / (((M : ℝ) * N) ^ P)) * quadraticSieveEnergy N v := by gcongr
    _ = _ := by ring

theorem quadratic_small_error_arbitrary_power {δ : ℝ} (hδ : 0 < δ) (P : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ M N K : ℕ, 1 ≤ M → 1 ≤ N →
      (K : ℝ) ≤ ((M : ℝ) * N) ^ 3 → ∀ v : ℕ → ℂ,
      ‖(quadraticSmallEnergy M N K v : ℂ) -
        quadraticSmallMomentCore M N K (((M : ℝ) * N) ^ δ) v‖ ≤
        C / (((M : ℝ) * N) ^ P) * quadraticSieveEnergy N v := by
  obtain ⟨A, hA⟩ := quadratic_moment_error_power_choice hδ P
  obtain ⟨C, hC, hc⟩ := quadratic_small_moment_error A
  refine ⟨C, hC, ?_⟩
  intro M N K hM hN hK v
  have hMR : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hMN : 1 ≤ (M : ℝ) * N := one_le_mul_of_one_le_of_one_le hMR hNR
  have hJ : 1 ≤ ((M : ℝ) * N) ^ δ := Real.one_le_rpow hMN hδ.le
  have hcost : Real.sqrt M * K * N ≤ ((M : ℝ) * N) ^ 5 := by
    calc
      _ ≤ (M : ℝ) * (((M : ℝ) * N) ^ 3) * N := by
        gcongr
        exact Real.sqrt_le_self_iff.mpr (Or.inr hMR)
      _ = ((M : ℝ) * N) ^ 4 := by ring
      _ ≤ ((M : ℝ) * N) ^ 5 := pow_le_pow_right₀ hMN (by omega)
  have he := hA ((M : ℝ) * N) hMN
  have hEn : 0 ≤ quadraticSieveEnergy N v := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  calc
    _ ≤ (C * Real.sqrt M * K / (((M : ℝ) * N) ^ δ) ^ A) * N *
        quadraticSieveEnergy N v := hc M N K (by omega) _ hJ v
    _ = C * ((Real.sqrt M * K * N) / (((M : ℝ) * N) ^ δ) ^ A) * quadraticSieveEnergy N v := by ring
    _ ≤ C * (((M : ℝ) * N) ^ 5 / (((M : ℝ) * N) ^ δ) ^ A) * quadraticSieveEnergy N v := by gcongr
    _ ≤ C * (1 / (((M : ℝ) * N) ^ P)) * quadraticSieveEnergy N v := by gcongr
    _ = _ := by ring

end Ostmann

end OAI
