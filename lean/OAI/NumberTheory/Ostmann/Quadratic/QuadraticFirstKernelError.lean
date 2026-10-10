import OAI.NumberTheory.Ostmann.Quadratic.QuadraticPairTailGeometry

namespace OAI

/-! # The whole first-transform tail, with the actual pair and divisor weights -/

namespace Ostmann

open scoped Classical BigOperators FourierTransform

noncomputable def quadraticFirstKernelFinite (M D q K : ℕ) : ℂ :=
  quadraticGaussMultiplier q * ∑ e ∈ (2 * D).divisors,
    (ArithmeticFunction.moebius e : ℂ) *
      (((M : ℝ) / ((e : ℝ) * Real.sqrt q) : ℝ) : ℂ) *
        quadraticFirstFiniteFrequency quadraticSieveWeight M e q K

theorem quadratic_first_kernel_error (A : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ M N D K : ℕ, 0 < M → ∀ J : ℝ, 1 ≤ J →
      2 * (N : ℝ) ^ 2 * J ≤ (M : ℝ) * ((K : ℝ) + 1) →
      ∀ z ∈ quadraticGcdPairs N D, z.1 ≠ z.2 →
      ‖quadraticFirstKernelTransform M D (quadraticPairKernel z.1 z.2) -
        quadraticFirstKernelFinite M D (quadraticPairKernel z.1 z.2) K‖ ≤
      4 * C * (N : ℝ) ^ 4 / ((M : ℝ) * J ^ A) := by
  obtain ⟨C, hC, hc⟩ := quadratic_first_tail_normalized quadraticSieveWeight A
  refine ⟨C, hC, ?_⟩
  intro M N D K hM J hJ hcut z hz hne
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  obtain ⟨hD, hDN, _⟩ := quadratic_pair_product_bound hz
  obtain ⟨hz', _⟩ := Finset.mem_filter.mp hz
  obtain ⟨hs, ht⟩ := Finset.mem_product.mp hz'
  have hsf := quadraticPairKernel_squarefree (Finset.mem_filter.mp hs).2.2
    (Finset.mem_filter.mp ht).2.2
  have ho := quadraticPairKernel_odd (Finset.mem_filter.mp hs).2.1 (Finset.mem_filter.mp ht).2.1
  have hq : 1 < quadraticPairKernel z.1 z.2 := by
    have hn := mt (quadraticPairKernel_eq_one_iff (Finset.mem_filter.mp hs).2.2
      (Finset.mem_filter.mp ht).2.2).mp hne
    have hp := Nat.pos_of_ne_zero hsf.ne_zero
    omega
  let q := quadraticPairKernel z.1 z.2
  let R (e : ℕ) : ℂ := (((M : ℝ) / ((e : ℝ) * Real.sqrt q) : ℝ) : ℂ) *
    ((∑' h : ℤ, (jacobiSym ((e : ℤ) * h) q : ℂ) *
      𝓕 quadraticSieveWeight ((h : ℝ) * M / ((e : ℝ) * q))) -
        quadraticFirstFiniteFrequency quadraticSieveWeight M e q K)
  have hid : quadraticFirstKernelTransform M D q - quadraticFirstKernelFinite M D q K =
      quadraticGaussMultiplier q * ∑ e ∈ (2 * D).divisors, (ArithmeticFunction.moebius e : ℂ) * R e := by
    unfold quadraticFirstKernelTransform quadraticFirstKernelFinite
    rw [← mul_sub, ← Finset.sum_sub_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro e _
    dsimp [R]
    ring
  have hT : 0 ≤ C * (2 * (N : ℝ) ^ 3 / M) / J ^ A := by positivity
  have hp (e : ℕ) (he : e ∈ (2 * D).divisors) :
      ‖(ArithmeticFunction.moebius e : ℂ) * R e‖ ≤ C * (2 * (N : ℝ) ^ 3 / M) / J ^ A := by
    have hepos := Nat.pos_of_mem_divisors he
    have hcc := quadratic_pair_first_cutoff hz he (by positivity : 0 ≤ J) hcut
    have hh := hc M J hMR hJ e q K hepos hq hcc
    have hn : ‖(ArithmeticFunction.moebius e : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_intCast]
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := e)
    rw [norm_mul]
    apply (mul_le_mul hn hh (norm_nonneg _) zero_le_one).trans
    simp only [one_mul]
    apply div_le_div_of_nonneg_right _ (by positivity)
    apply mul_le_mul_of_nonneg_left _ hC
    apply div_le_div_of_nonneg_right _ hMR.le
    exact quadratic_pair_normalized_tail_scale hz he
  change ‖quadraticFirstKernelTransform M D q - quadraticFirstKernelFinite M D q K‖ ≤ _
  rw [hid, norm_mul, quadraticGaussMultiplier_norm hsf ho, one_mul]
  calc
    _ ≤ ∑ e ∈ (2 * D).divisors, C * (2 * (N : ℝ) ^ 3 / M) / J ^ A :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum hp)
    _ = (((2 * D).divisors.card : ℕ) : ℝ) * (C * (2 * (N : ℝ) ^ 3 / M) / J ^ A) := by simp
    _ ≤ (2 * N : ℝ) * (C * (2 * (N : ℝ) ^ 3 / M) / J ^ A) := by
      apply mul_le_mul_of_nonneg_right _ hT
      exact_mod_cast (Nat.card_divisors_le_self (2 * D)).trans (Nat.mul_le_mul_left 2 hDN)
    _ = _ := by ring

noncomputable def quadraticFirstOffDiagonalError (M N K : ℕ) (v : ℕ → ℂ) : ℂ :=
  quadraticGcdRemainder N v (fun D z => if z.1 = z.2 then 0 else
    quadraticFirstKernelTransform M D (quadraticPairKernel z.1 z.2) -
      quadraticFirstKernelFinite M D (quadraticPairKernel z.1 z.2) K)

theorem quadratic_first_off_diagonal_error (A : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ M N K : ℕ, 0 < M → ∀ J : ℝ, 1 ≤ J →
      2 * (N : ℝ) ^ 2 * J ≤ (M : ℝ) * ((K : ℝ) + 1) → ∀ v : ℕ → ℂ,
      ‖quadraticFirstOffDiagonalError M N K v‖ ≤
        C * (N : ℝ) ^ 5 / ((M : ℝ) * J ^ A) * quadraticSieveEnergy N v := by
  obtain ⟨C, hC, hc⟩ := quadratic_first_kernel_error A
  refine ⟨4 * C, by positivity, ?_⟩
  intro M N K hM J hJ hcut v
  have hh := quadratic_gcd_remainder_bound N v
    (fun D z => if z.1 = z.2 then 0 else
      quadraticFirstKernelTransform M D (quadraticPairKernel z.1 z.2) -
        quadraticFirstKernelFinite M D (quadraticPairKernel z.1 z.2) K)
    (T := 4 * C * (N : ℝ) ^ 4 / ((M : ℝ) * J ^ A)) (by positivity) (by
      intro D hD z hz
      by_cases he : z.1 = z.2
      · rw [ite_eq_left he, norm_zero]
        positivity
      · rw [ite_eq_right he]
        exact hc M N D K hM J hJ hcut z hz he)
  change ‖quadraticFirstOffDiagonalError M N K v‖ ≤ _ at hh
  convert hh using 1
  ring

end Ostmann

end OAI
