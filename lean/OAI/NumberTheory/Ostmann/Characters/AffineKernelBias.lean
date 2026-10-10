import OAI.NumberTheory.Ostmann.Construction.FiniteBiasPopulation
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticKernelDecomposition

namespace OAI

/-! # Actual squarefree kernels retain the common-center character bias -/

namespace Ostmann

open scoped BigOperators Classical

theorem quadraticPrimeMean_zero (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (e : ℕ → ℂ) :
    quadraticPrimeMean P e 0 = 0 := by
  unfold quadraticPrimeMean
  have hz : (∑ p ∈ P, e p * (jacobiSym 0 p : ℂ)) = 0 := by
    apply Finset.sum_eq_zero
    intro p hp
    rw [jacobiSym.zero_left (hP p hp).one_lt, Int.cast_zero, mul_zero]
  rw [hz, zero_div]

theorem exists_affine_kernel_assignment (S : Finset ℤ) (m : ℕ) (h : ℤ)
    (hnon : ∀ x ∈ S, (m : ℤ) * x - h ≠ 0) :
    ∃ (kernel : ℤ → ℤ) (root : ℤ → ℕ), ∀ x ∈ S,
      kernel x ≠ 0 ∧ 0 < root x ∧ Squarefree (kernel x).natAbs ∧
      kernel x * (root x : ℤ) ^ 2 = (m : ℤ) * x - h := by
  have hex (x : ℤ) : ∃ (u : ℤ) (t : ℕ), x ∈ S →
      u ≠ 0 ∧ 0 < t ∧ Squarefree u.natAbs ∧ u * (t : ℤ) ^ 2 = (m : ℤ) * x - h := by
    by_cases hx : x ∈ S
    · obtain ⟨u, t, hu⟩ := exists_signed_squarefree_decomposition ((m : ℤ) * x - h) (hnon x hx)
      exact ⟨u, t, fun _ => hu⟩
    · exact ⟨0, 0, fun hh => (hx hh).elim⟩
  choose kernel root hh using hex
  exact ⟨kernel, root, hh⟩

theorem kernel_root_log_bound (u x : ℤ) (t : ℕ) (Y : ℝ)
    (hu : u ≠ 0) (ht : 0 < t) (heq : u * (t : ℤ) ^ 2 = x)
    (hx : |(x : ℝ)| ≤ Real.exp Y) : Real.log (t : ℝ) ≤ Y := by
  have hu1 : (1 : ℝ) ≤ |(u : ℝ)| := by exact_mod_cast Int.one_le_abs hu
  have ht1 : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have heqR : (u : ℝ) * (t : ℝ) ^ 2 = x := by exact_mod_cast heq
  have habs : |(u : ℝ)| * (t : ℝ) ^ 2 = |(x : ℝ)| := by
    rw [← heqR, abs_mul, abs_pow]
    simp only [abs_of_nonneg (Nat.cast_nonneg (α := ℝ) t)]
  have htA : (t : ℝ) ≤ |(x : ℝ)| := by nlinarith [sq_nonneg ((t : ℝ) - 1)]
  exact (Real.log_le_iff_le_exp (by exact_mod_cast ht)).mpr (htA.trans hx)

theorem kernel_prime_divisor_loss (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (t : ℕ) (ht : 0 < t) (T Y c : ℝ) (hT : 0 < T) (hcard : 0 < P.card)
    (hlogp : ∀ p ∈ P, T ≤ Real.log (p : ℝ)) (hlogt : Real.log (t : ℝ) ≤ Y)
    (hsize : 2 * Y ≤ c * P.card * T) :
    2 * ((P.filter fun p => p ∣ t).card : ℝ) / P.card ≤ c := by
  have hc : (0 : ℝ) < P.card := by exact_mod_cast hcard
  have hh := (prime_divisors_card_log_le P t ht hP T hlogp).trans hlogt
  apply (div_le_iff₀ hc).mpr
  apply (mul_le_mul_iff_left₀ hT).mp
  nlinarith only [hh, hsize]

/-- A single actual kernel assignment is shared by all later tests. -/
theorem exists_biased_affine_kernels (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (S : Finset ℤ) (m : ℕ) (h : ℤ) (e : ℕ → ℂ) (c T Y : ℝ)
    (hc : 0 < c) (hT : 0 < T) (hcard : 0 < P.card) (he : ∀ p ∈ P, ‖e p‖ ≤ 1)
    (hlogp : ∀ p ∈ P, T ≤ Real.log (p : ℝ))
    (hsize : 2 * Y ≤ (c / 2) * P.card * T)
    (hbound : ∀ x ∈ S, |(((m : ℤ) * x - h : ℤ) : ℝ)| ≤ Real.exp Y)
    (hbias : ∀ x ∈ S, c ≤ ‖quadraticPrimeMean P e ((m : ℤ) * x - h)‖) :
    ∃ (kernel : ℤ → ℤ) (root : ℤ → ℕ), ∀ x ∈ S,
      kernel x ≠ 0 ∧ 0 < root x ∧ Squarefree (kernel x).natAbs ∧
      kernel x * (root x : ℤ) ^ 2 = (m : ℤ) * x - h ∧
      c / 2 ≤ ‖quadraticPrimeMean P e (kernel x)‖ := by
  have hnon (x : ℤ) (hx : x ∈ S) : (m : ℤ) * x - h ≠ 0 := by
    intro hz
    have hh := hbias x hx
    rw [hz, quadraticPrimeMean_zero P hP e, norm_zero] at hh
    linarith
  obtain ⟨kernel, root, hkr⟩ := exists_affine_kernel_assignment S m h hnon
  refine ⟨kernel, root, ?_⟩
  intro x hx
  obtain ⟨hu, ht, hsf, hEq⟩ := hkr x hx
  refine ⟨hu, ht, hsf, hEq, ?_⟩
  apply quadratic_kernel_bias_lower P e hP he (kernel x) ((m : ℤ) * x - h) (root x) hEq
    (c / 2) (c / 2)
  · have hh := hbias x hx
    linarith
  · exact kernel_prime_divisor_loss P hP (root x) ht T Y (c / 2) hT hcard hlogp
      (kernel_root_log_bound _ _ _ Y hu ht hEq (hbound x hx)) hsize

end Ostmann

end OAI
