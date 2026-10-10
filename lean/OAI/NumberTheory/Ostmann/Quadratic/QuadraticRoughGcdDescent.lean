import OAI.NumberTheory.Ostmann.Quadratic.QuadraticRoughBound
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticDivisorMomentBound
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticMomentMainComparison

namespace OAI

/-! # Large common divisors descend to genuinely shorter rough moments -/

namespace Ostmann

open scoped Classical BigOperators

theorem quadratic_divisor_coefficient_weight {N D : ℕ}
    (hD : Squarefree D) (ho : Odd D) (v : ℕ → ℂ) :
    (∑ n ∈ oddSquarefreeRange (N / D), (n.divisors.card : ℝ) *
      ‖quadraticDivisibilityCoeff D v n‖ ^ 2) ≤ quadraticDivisorWeight N D v := by
  unfold quadraticDivisorWeight quadraticDivisibilityCoeff
  simp only [apply_ite, norm_zero, ite_pow, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow, mul_zero, ← Finset.sum_filter]
  rw [sum_oddSquarefree_multiples D N hD ho]
  apply Finset.sum_le_sum
  intro n hn
  have hn₀ : n ≠ 0 := (Finset.mem_filter.mp (Finset.mem_filter.mp hn).1).2.2.ne_zero
  have hmul₀ : D * n ≠ 0 := mul_ne_zero hD.ne_zero hn₀
  have hc : (n.divisors.card : ℝ) ≤ (D * n).divisors.card := by
    exact_mod_cast Finset.card_le_card (Nat.divisors_subset_of_dvd hmul₀ (dvd_mul_left n D))
  exact mul_le_mul_of_nonneg_right hc (sq_nonneg _)

theorem quadratic_rough_gcd_shorter {M N K D : ℕ} {T : ℝ}
    (hD : Squarefree D) (ho : Odd D) (hT : 0 ≤ T)
    (h : QuadraticRoughBound M (N / D) K T) (v : ℕ → ℂ) :
    ‖quadraticRoughGcdMoment M N K D v‖ ≤ T * quadraticDivisorWeight N D v := by
  apply (quadratic_rough_gcd_moment_divisors hD ho v).trans
  calc
    _ ≤ ∑ d ∈ Finset.Icc 1 (N / D), T * quadraticSieveEnergy (N / D)
        (fun n => if d ∣ n then quadraticDivisibilityCoeff D v n else 0) :=
      Finset.sum_le_sum (fun d _ => h _)
    _ = T * ∑ d ∈ Finset.Icc 1 (N / D), quadraticSieveEnergy (N / D)
        (fun n => if d ∣ n then quadraticDivisibilityCoeff D v n else 0) :=
      (Finset.mul_sum ..).symm
    _ ≤ T * ∑ n ∈ oddSquarefreeRange (N / D), (n.divisors.card : ℝ) *
        ‖quadraticDivisibilityCoeff D v n‖ ^ 2 :=
      mul_le_mul_of_nonneg_left (quadratic_divisibility_partial_energy _ _ _) hT
    _ ≤ _ := mul_le_mul_of_nonneg_left (quadratic_divisor_coefficient_weight hD ho v) hT

theorem quadratic_rough_energy_gcd (M N K : ℕ) (v : ℕ → ℂ) :
    (quadraticRoughEnergy M N K v : ℂ) =
      ∑ D ∈ Finset.Icc 1 N, quadraticRoughGcdMoment M N K D v := by
  unfold quadraticRoughEnergy quadraticRoughGcdMoment
  push_cast
  simp_rw [quadraticTranspose_norm_sq_gcd, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp only [quadraticSieveWeight_apply, mul_assoc]

theorem quadratic_rough_gcd_moment_zero {M N K D : ℕ}
    (he : quadraticGcdPairs N D = ∅) (v : ℕ → ℂ) :
    quadraticRoughGcdMoment M N K D v = 0 := by
  simp [quadraticRoughGcdMoment, quadraticGcdKernelSum, he]

/-- Heath-Brown's large-gcd descent, with the original small-gcd moments left
literal. The shorter range is the integer quotient N/D₀. -/
theorem quadratic_rough_gcd_descent {M N K D₀ : ℕ} {T : ℝ}
    (hD₀ : 0 < D₀) (hT : 0 ≤ T) (h : QuadraticRoughBound M (N / D₀) K T)
    (v : ℕ → ℂ) :
    quadraticRoughEnergy M N K v ≤
      (∑ D ∈ (Finset.Icc 1 N).filter (fun D => D ≤ D₀),
        ‖quadraticRoughGcdMoment M N K D v‖) + T * quadraticDivisorMoment N v := by
  have hn : quadraticRoughEnergy M N K v ≤
      ∑ D ∈ Finset.Icc 1 N, ‖quadraticRoughGcdMoment M N K D v‖ := by
    have he := congrArg Complex.re (quadratic_rough_energy_gcd M N K v)
    simp only [Complex.ofReal_re, Complex.re_sum] at he
    rw [he]
    exact Finset.sum_le_sum (fun D _ => Complex.re_le_norm _)
  have hs := Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 N)
    (fun D => D ≤ D₀) (fun D => ‖quadraticRoughGcdMoment M N K D v‖)
  rw [← hs] at hn
  apply hn.trans
  apply add_le_add le_rfl
  calc
    _ ≤ ∑ D ∈ (Finset.Icc 1 N).filter (fun D => ¬ D ≤ D₀),
        T * quadraticDivisorWeight N D v := by
      apply Finset.sum_le_sum
      intro D hmem
      have hle : D₀ ≤ D := le_of_lt (lt_of_not_ge (Finset.mem_filter.mp hmem).2)
      by_cases hsf : Squarefree D
      · by_cases ho : Odd D
        · exact quadratic_rough_gcd_shorter hsf ho hT
            (h.mono_second (Nat.div_le_div_left hle hD₀)) v
        · rw [quadratic_rough_gcd_moment_zero (quadraticGcdPairs_empty_of_not_odd N D ho), norm_zero]
          exact mul_nonneg hT (quadraticDivisorWeight_nonneg N D v)
      · rw [quadratic_rough_gcd_moment_zero (quadraticGcdPairs_empty_of_not_squarefree N D hsf), norm_zero]
        exact mul_nonneg hT (quadraticDivisorWeight_nonneg N D v)
    _ = T * ∑ D ∈ (Finset.Icc 1 N).filter (fun D => ¬ D ≤ D₀), quadraticDivisorWeight N D v :=
      (Finset.mul_sum ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left (quadratic_divisor_weight_sum N _ v) hT

end Ostmann

end OAI
