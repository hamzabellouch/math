import OAI.NumberTheory.Ostmann.Quadratic.QuadraticSecondSignedCore

namespace OAI

/-! # The original finite first transform after the complete second Poisson step -/

namespace Ostmann

open scoped Classical BigOperators SchwartzMap

noncomputable def quadraticFirstSecondKernel (M D q K : ℕ) (H J : ℝ) : ℂ :=
  quadraticGaussMultiplier q * ∑ e ∈ (2 * D).divisors,
    (ArithmeticFunction.moebius e : ℂ) *
      (((M : ℝ) / ((e : ℝ) * Real.sqrt q) : ℝ) : ℂ) *
        quadraticSignedSecondCore quadraticSieveWeight M H J e q K

theorem quadratic_first_second_kernel_error (A : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ M D q K : ℕ, 0 < M → Squarefree q → Odd q → q ≠ 1 →
      ∀ H J : ℝ, 0 < H → 1 ≤ J → H ^ 2 ≤ q → (q : ℝ) ≤ 4 * H ^ 2 →
      ‖quadraticFirstKernelFinite M D q K - quadraticFirstSecondKernel M D q K H J‖ ≤
        C * Real.sqrt M * D * K / J ^ A := by
  have hw : ∀ t < 1 / 2, quadraticSieveWeight t = 0 :=
    fun t ht => quadraticSieveWeight_eq_zero (Or.inl ht.le)
  obtain ⟨C, hC, hc⟩ := quadratic_signed_second_error quadraticSieveWeight hw A
  refine ⟨2 * C, by positivity, ?_⟩
  intro M D q K hM hsf ho hq H J hH hJ hlo hhi
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hid : quadraticFirstKernelFinite M D q K - quadraticFirstSecondKernel M D q K H J =
      quadraticGaussMultiplier q * ∑ e ∈ (2 * D).divisors,
        (ArithmeticFunction.moebius e : ℂ) *
          ((((M : ℝ) / ((e : ℝ) * Real.sqrt q) : ℝ) : ℂ) *
            (quadraticFirstFiniteFrequency quadraticSieveWeight M e q K -
              quadraticSignedSecondCore quadraticSieveWeight M H J e q K)) := by
    unfold quadraticFirstKernelFinite quadraticFirstSecondKernel
    rw [← mul_sub, ← Finset.sum_sub_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro e _
    ring
  rw [hid, norm_mul, quadraticGaussMultiplier_norm hsf ho, one_mul]
  have hp (e : ℕ) (he : e ∈ (2 * D).divisors) :
      ‖(ArithmeticFunction.moebius e : ℂ) *
          ((((M : ℝ) / ((e : ℝ) * Real.sqrt q) : ℝ) : ℂ) *
            (quadraticFirstFiniteFrequency quadraticSieveWeight M e q K -
              quadraticSignedSecondCore quadraticSieveWeight M H J e q K))‖ ≤
        C * Real.sqrt M * K / J ^ A := by
    have hμ : ‖(ArithmeticFunction.moebius e : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_intCast]
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := e)
    rw [norm_mul]
    exact (mul_le_mul hμ (hc M H J hMR hH hJ e q K
      (Nat.pos_of_mem_divisors he) hq hlo hhi) (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
  calc
    _ ≤ ∑ e ∈ (2 * D).divisors, C * Real.sqrt M * K / J ^ A :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum hp)
    _ = (((2 * D).divisors.card : ℕ) : ℝ) * (C * Real.sqrt M * K / J ^ A) := by simp
    _ ≤ (2 * D : ℝ) * (C * Real.sqrt M * K / J ^ A) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast Nat.card_divisors_le_self (2 * D)
    _ = _ := by ring

end Ostmann

end OAI
