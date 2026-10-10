import OAI.NumberTheory.Ostmann.Quadratic.QuadraticOffDiagonalPairSums
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticMomentPowerSaving

namespace OAI

/-! # Both actual off-diagonal Poisson errors are uniformly negligible -/

namespace Ostmann

open scoped Classical BigOperators ComplexConjugate

theorem quadratic_small_pair_error (A : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ M K D q : ℕ, 0 < M → 0 < D → 0 < q →
      ∀ J : ℝ, 1 ≤ J →
      ‖quadraticSmallPairSum M K D q - quadraticSmallPairCore M K D q J‖ ≤
        C * Real.sqrt M * K / J ^ A := by
  obtain ⟨C, hC, hc⟩ := quadratic_small_dyadic_uniform A
  refine ⟨C, hC, ?_⟩
  intro M K D q hM hD hq J hJ
  have hmod : 0 < 2 * (q * D) := by positivity
  have : NeZero (2 * (q * D)) := ⟨hmod.ne'⟩
  have hmod₁ : 2 * (q * D) ≠ 1 := by omega
  let T : ℝ := C * Real.sqrt M / J ^ A
  have hT : 0 ≤ T := by dsimp [T]; positivity
  unfold quadraticSmallPairSum quadraticSmallPairCore
  rw [← Finset.sum_sub_distrib]
  have hp (b : ℕ) (hb : b ∈ (oddSquarefreeRange K).filter (D.Coprime ·)) :
      ‖(jacobiSym b q : ℂ) *
          (∑' c : ℕ+, (1 : DirichletCharacter ℂ (2 * (q * D)))
            (c : ZMod (2 * (q * D))) * quadraticSieveWeight ((c : ℝ) ^ 2 * b / M)) -
        (jacobiSym b q : ℂ) * quadraticSmallDyadicCore quadraticSieveWeight M b J (2 * (q * D)) b‖ ≤ T := by
    have hb₀ : 0 < b := (Finset.mem_Icc.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hb).1).1).1
    have hh := hc M J (by exact_mod_cast hM) hJ _ hmod₁ b hb₀
    have hJac : ‖(jacobiSym b q : ℂ)‖ ≤ 1 := by
      rcases jacobiSym.trichotomy (b : ℤ) q with h | h | h <;> rw [h] <;> norm_num
    rw [← mul_sub, norm_mul]
    exact (mul_le_mul hJac hh (norm_nonneg _) zero_le_one).trans_eq (one_mul T)
  calc
    _ ≤ ∑ b ∈ (oddSquarefreeRange K).filter (D.Coprime ·), T :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum hp)
    _ = (((oddSquarefreeRange K).filter (D.Coprime ·)).card : ℝ) * T := by simp
    _ ≤ (K : ℝ) * T := by
      apply mul_le_mul_of_nonneg_right _ hT
      exact_mod_cast (Finset.card_filter_le _ _).trans (oddSquarefreeRange_card_le K)
    _ = _ := by dsimp [T]; ring

noncomputable def quadraticSmallOffDiagonalError (M N K : ℕ) (J : ℝ) (v : ℕ → ℂ) : ℂ :=
  quadraticGcdRemainder N v (fun D z => if z.1 = z.2 then 0 else
    quadraticSmallPairSum M K D (quadraticPairKernel z.1 z.2) -
      quadraticSmallPairCore M K D (quadraticPairKernel z.1 z.2) J)

theorem quadratic_small_off_diagonal_error (A : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ M N K : ℕ, 0 < M → ∀ J : ℝ, 1 ≤ J → ∀ v : ℕ → ℂ,
      ‖quadraticSmallOffDiagonalError M N K J v‖ ≤
        (C * Real.sqrt M * K / J ^ A) * N * quadraticSieveEnergy N v := by
  obtain ⟨C, hC, hc⟩ := quadratic_small_pair_error A
  refine ⟨C, hC, ?_⟩
  intro M N K hM J hJ v
  apply quadratic_gcd_remainder_bound N v _ (by positivity)
  intro D hD z hz
  by_cases he : z.1 = z.2
  · rw [ite_eq_left he, norm_zero]
    positivity
  · rw [ite_eq_right he]
    have hz' := (Finset.mem_filter.mp hz).1
    obtain ⟨hs, ht⟩ := Finset.mem_product.mp hz'
    have hq : 0 < quadraticPairKernel z.1 z.2 :=
      Nat.pos_of_ne_zero (quadraticPairKernel_squarefree
        (Finset.mem_filter.mp hs).2.2 (Finset.mem_filter.mp ht).2.2).ne_zero
    exact hc M K D _ hM (Finset.mem_Icc.mp hD).1 hq J hJ

noncomputable def quadraticRoughOffDiagonalCore (M N K : ℕ) (J : ℝ) (v : ℕ → ℂ) : ℂ :=
  quadraticGcdRemainder N v (fun D z => if z.1 = z.2 then 0 else
    quadraticFirstKernelFinite M D (quadraticPairKernel z.1 z.2) K -
      quadraticSmallPairCore M K D (quadraticPairKernel z.1 z.2) J)

theorem quadratic_rough_off_diagonal_error_identity {M : ℕ} (hM : 0 < M)
    (N K : ℕ) (J : ℝ) (v : ℕ → ℂ) :
    quadraticRoughOffDiagonal M N K v - quadraticRoughOffDiagonalCore M N K J v =
      quadraticFirstOffDiagonalError M N K v - quadraticSmallOffDiagonalError M N K J v := by
  rw [quadratic_rough_off_diagonal_transform hM]
  unfold quadraticRoughOffDiagonalCore quadraticFirstOffDiagonalError
    quadraticSmallOffDiagonalError quadraticGcdRemainder
  simp only [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro D _
  apply Finset.sum_congr rfl
  intro z _
  by_cases hz : z.1 = z.2
  · simp only [hz, ite_true, mul_zero, sub_self]
  · simp only [hz, ite_false]
    ring

theorem quadratic_small_off_diagonal_arbitrary_power {δ : ℝ} (hδ : 0 < δ) (P : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ M N K : ℕ, 1 ≤ M → 1 ≤ N →
      (K : ℝ) ≤ ((M : ℝ) * N) ^ 3 → ∀ v : ℕ → ℂ,
      ‖quadraticSmallOffDiagonalError M N K (((M : ℝ) * N) ^ δ) v‖ ≤
        C / (((M : ℝ) * N) ^ P) * quadraticSieveEnergy N v := by
  obtain ⟨A, hA⟩ := quadratic_moment_error_power_choice hδ P
  obtain ⟨C, hC, hc⟩ := quadratic_small_off_diagonal_error A
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

theorem quadratic_rough_off_diagonal_arbitrary_power {δ : ℝ} (hδ : 0 < δ) (P : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ M N K : ℕ, 1 ≤ M → 1 ≤ N →
      (K : ℝ) ≤ ((M : ℝ) * N) ^ 3 →
      2 * (N : ℝ) ^ 2 * (((M : ℝ) * N) ^ δ) ≤ (M : ℝ) * ((K : ℝ) + 1) →
      ∀ v : ℕ → ℂ,
      ‖quadraticRoughOffDiagonal M N K v -
        quadraticRoughOffDiagonalCore M N K (((M : ℝ) * N) ^ δ) v‖ ≤
        C / (((M : ℝ) * N) ^ P) * quadraticSieveEnergy N v := by
  obtain ⟨C₁, hC₁, h₁⟩ := quadratic_first_error_arbitrary_power hδ P
  obtain ⟨C₂, hC₂, h₂⟩ := quadratic_small_off_diagonal_arbitrary_power hδ P
  refine ⟨C₁ + C₂, by positivity, ?_⟩
  intro M N K hM hN hK hcut v
  rw [quadratic_rough_off_diagonal_error_identity (by omega)]
  calc
    _ ≤ ‖quadraticFirstOffDiagonalError M N K v‖ +
        ‖quadraticSmallOffDiagonalError M N K (((M : ℝ) * N) ^ δ) v‖ := norm_sub_le _ _
    _ ≤ C₁ / (((M : ℝ) * N) ^ P) * quadraticSieveEnergy N v +
        C₂ / (((M : ℝ) * N) ^ P) * quadraticSieveEnergy N v :=
      add_le_add (h₁ M N K hM hN hcut v) (h₂ M N K hM hN hK v)
    _ = _ := by ring

end Ostmann

end OAI
