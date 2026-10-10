import OAI.NumberTheory.Ostmann.Arithmetic.SampledPrimeCoincidence

namespace OAI

/-! # Joint signed replacement with actual internal-prime coordinates

Different tests can use different sampled primes and can depend on the other
prime coordinates. Each test only excludes its own prime coordinate.
-/

namespace Ostmann

open scoped BigOperators Classical

theorem joint_sampled_polynomial_comparison_le {A I : Type*}
    [Fintype A] [Nonempty A] [Fintype I] {n : ℕ}
    (value : A → ℤ) (hinj : Function.Injective value)
    (prime : A → ℕ) (hpInj : Function.Injective prime) (hprime : ∀ a, (prime a).Prime)
    (F : I → MvPolynomial (Fin (n + 1)) ℤ) (coordinate : I → Fin (n + 1))
    (habsent : ∀ i, coordinate i ∉ (F i).vars)
    (μ : Fin (n + 1) → A → ℝ) (hμ : ∀ j a, 0 ≤ μ j a)
    (hmass : ∀ j, ∑ a, μ j a = 1)
    (α β V H : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β) (hV : 0 < V) (hH : 1 ≤ H)
    (hmax : ∀ j a, μ j a ≤ α) (hpmax : ∀ i a, μ (coordinate i) a ≤ β)
    (hsize : ∀ i a, μ (coordinate i) a ≠ 0 → V ≤ Real.log (prime a : ℝ))
    (hvalue : ∀ i x, |(integerTestValue value (F i) x : ℝ)| ≤ H)
    (Ψ : (Fin (n + 1) → A) → (I → Bool) → ℂ)
    (B : ℝ) (hB : 0 ≤ B) (hΨ : ∀ x flags, ‖Ψ x flags‖ ≤ B) :
    ‖∑ x, (productPrior μ x : ℂ) *
      (Ψ x (fun i => arithmeticTestFlag
        (prime (x (coordinate i)) ∣ (integerTestValue value (F i) x).natAbs)) -
       Ψ x (fun i => arithmeticTestFlag (F i = 0)))‖ ≤
      2 * B * ∑ i, (((F i).totalDegree : ℝ) * α + (Real.log H / V) * β) := by
  let bad := fun i x => F i ≠ 0 ∧ prime (x (coordinate i)) ∣ (integerTestValue value (F i) x).natAbs
  have hprob (i : I) : (∑ x, productPrior μ x * if bad i x then (1 : ℝ) else 0) ≤
      ((F i).totalDegree : ℝ) * α + (Real.log H / V) * β := by
    by_cases hi : F i = 0
    · simp only [bad, hi, ne_eq, not_true_eq_false, false_and, ite_false, mul_zero,
        Finset.sum_const_zero]
      exact add_nonneg (mul_nonneg (Nat.cast_nonneg _) hα)
        (mul_nonneg (div_nonneg (Real.log_nonneg hH) hV.le) hβ)
    · simp only [bad, hi, ne_eq, not_false_eq_true, true_and]
      exact sampled_coordinate_prime_coincidence_le value hinj prime hpInj hprime (F i) hi
        (coordinate i) (habsent i) μ hμ hmass α β V H hα hβ hV hH hmax (hpmax i) (hsize i) (hvalue i)
  have heq (x : Fin (n + 1) → A) (hx : ∀ i, ¬bad i x) :
      (fun i => arithmeticTestFlag
        (prime (x (coordinate i)) ∣ (integerTestValue value (F i) x).natAbs)) =
      (fun i => arithmeticTestFlag (F i = 0)) := by
    funext i
    by_cases hi : F i = 0
    · simp [hi, integerTestValue]
    · have hnd : ¬prime (x (coordinate i)) ∣ (integerTestValue value (F i) x).natAbs :=
        fun h => hx i ⟨hi, h⟩
      simp [hi, hnd]
  have h := @weighted_flag_comparison_le (Fin (n + 1) → A) I inferInstance inferInstance
    (productPrior μ) (productPrior_nonneg μ hμ)
    (fun x i => arithmeticTestFlag
      (prime (x (coordinate i)) ∣ (integerTestValue value (F i) x).natAbs))
    (fun _ i => arithmeticTestFlag (F i = 0)) bad (fun _ _ => inferInstance)
    heq Ψ B hB hΨ
  exact h.trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => hprob i) (by positivity))

end Ostmann

end OAI
