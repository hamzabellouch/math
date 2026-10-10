import OAI.NumberTheory.Ostmann.Construction.OriginalFourierCoefficients

namespace OAI

/-! # Separating the principal small kernels in the original Fourier statistic -/

namespace Ostmann

open scoped BigOperators SchwartzMap Classical

noncomputable def smallSquarefreeKernels (L N : ℕ) : Finset ℕ :=
  (squarefreeKernelSupport L N).filter (fun s => s ≤ L ^ 4)

noncomputable def largeSquarefreeKernels (L N : ℕ) : Finset ℕ :=
  (squarefreeKernelSupport L N).filter (fun s => L ^ 4 < s)

theorem quadraticArrayStatistic_split (S : Finset ℕ) (M A : ℕ) (F : ℕ → ℂ) :
    quadraticArrayStatistic S M F =
      quadraticArrayStatistic (S.filter (fun s => s ≤ A)) M F +
      quadraticArrayStatistic (S.filter (fun s => A < s)) M F := by
  simp only [quadraticArrayStatistic_finset]
  simpa only [not_le] using
    (Finset.sum_filter_add_sum_filter_not S (fun s => s ≤ A)
      (fun s => (Real.sqrt (s : ℝ) : ℂ)⁻¹ * F s * (realJacobi s M : ℂ))).symm

noncomputable def principalSmallFourier (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
    (D : ∀ p : ℕ, Finset (ZMod p)) (M N h₀ : ℕ) (θ R : ℝ) (Φ : 𝓢(ℝ, ℂ)) : ℂ :=
  quadraticArrayStatistic (smallSquarefreeKernels Q.toList.prod N) M
    (arithmeticQuadraticCoefficient Q hQ D Φ R 1 M h₀ θ)

noncomputable def principalLargeFourier (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
    (D : ∀ p : ℕ, Finset (ZMod p)) (M N h₀ : ℕ) (θ R : ℝ) (Φ : 𝓢(ℝ, ℂ)) : ℂ :=
  quadraticArrayStatistic (largeSquarefreeKernels Q.toList.prod N) M
    (arithmeticQuadraticCoefficient Q hQ D Φ R 1 M h₀ θ)

noncomputable def outerFourierRemainder (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
    (D : ∀ p : ℕ, Finset (ZMod p)) (M N h₀ : ℕ) (θ R : ℝ) (Φ : 𝓢(ℝ, ℂ)) : ℂ :=
  ∑ P ∈ M.divisors.erase 1, (ArithmeticFunction.moebius P : ℂ) *
    quadraticArrayStatistic (squarefreeKernelSupport Q.toList.prod N) M
      (arithmeticQuadraticCoefficient Q hQ D Φ R P M h₀ θ)

theorem originalPositiveFourier_kernel_decomposition (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
    (D : ∀ p : ℕ, Finset (ZMod p)) (M N h₀ : ℕ) [NeZero M]
    (θ R H : ℝ) (Φ : 𝓢(ℝ, ℂ)) (hR : 0 < R) (hH : 0 ≤ H) (hN : 1 ≤ N)
    (hcut : H * R * Q.toList.prod ≤ N) (hΦ : ∀ x : ℝ, H < x → Φ x = 0) :
    originalPositiveFourier Q hQ D M N h₀ θ R Φ =
      principalSmallFourier Q hQ D M N h₀ θ R Φ +
      principalLargeFourier Q hQ D M N h₀ θ R Φ +
      outerFourierRemainder Q hQ D M N h₀ θ R Φ := by
  rw [originalPositiveFourier_expansion Q hQ D M N h₀ θ R H Φ hR hH hN hcut hΦ]
  have hone : 1 ∈ M.divisors := Nat.mem_divisors.mpr ⟨one_dvd _, NeZero.ne M⟩
  rw [← Finset.add_sum_erase _ _ hone]
  simp only [ArithmeticFunction.moebius_apply_one, Int.cast_one, one_mul]
  rw [quadraticArrayStatistic_split (squarefreeKernelSupport Q.toList.prod N) M
    (Q.toList.prod ^ 4)]
  rfl

theorem outerFourierRemainder_norm_le (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
    (D : ∀ p : ℕ, Finset (ZMod p)) (M N h₀ : ℕ)
    (θ R : ℝ) (Φ : 𝓢(ℝ, ℂ)) :
    ‖outerFourierRemainder Q hQ D M N h₀ θ R Φ‖ ≤
      ∑ P ∈ M.divisors.erase 1,
        ‖quadraticArrayStatistic (squarefreeKernelSupport Q.toList.prod N) M
          (arithmeticQuadraticCoefficient Q hQ D Φ R P M h₀ θ)‖ := by
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro P _
  rw [norm_mul]
  apply mul_le_of_le_one_left (norm_nonneg _)
  have hh := ArithmeticFunction.abs_moebius_le_one (n := P)
  rw [Complex.norm_intCast]
  exact_mod_cast hh

theorem originalPositiveFourier_norm_le_kernels (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
    (D : ∀ p : ℕ, Finset (ZMod p)) (M N h₀ : ℕ) [NeZero M]
    (θ R H : ℝ) (Φ : 𝓢(ℝ, ℂ)) (hR : 0 < R) (hH : 0 ≤ H) (hN : 1 ≤ N)
    (hcut : H * R * Q.toList.prod ≤ N) (hΦ : ∀ x : ℝ, H < x → Φ x = 0) :
    ‖originalPositiveFourier Q hQ D M N h₀ θ R Φ‖ ≤
      ‖principalSmallFourier Q hQ D M N h₀ θ R Φ‖ +
      ‖principalLargeFourier Q hQ D M N h₀ θ R Φ‖ +
      ∑ P ∈ M.divisors.erase 1,
        ‖quadraticArrayStatistic (squarefreeKernelSupport Q.toList.prod N) M
          (arithmeticQuadraticCoefficient Q hQ D Φ R P M h₀ θ)‖ := by
  rw [originalPositiveFourier_kernel_decomposition Q hQ D M N h₀ θ R H Φ hR hH hN hcut hΦ]
  exact (norm_add_le _ _).trans (add_le_add
    (norm_add_le _ _) (outerFourierRemainder_norm_le Q hQ D M N h₀ θ R Φ))

end Ostmann

end OAI
