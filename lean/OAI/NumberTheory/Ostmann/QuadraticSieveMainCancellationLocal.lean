import OAI.NumberTheory.Ostmann.QuadraticSieveMainCancellationBasic

namespace OAI

namespace Ostmann.QuadraticSieve

open scoped ArithmeticFunction.Moebius

theorem arithmeticFunction_mul_prime_pow (f g : ArithmeticFunction ℤ) {p : ℕ}
    (hp : p.Prime) (k : ℕ) :
    (f * g) (p ^ k) = ∑ i ∈ Finset.range (k + 1), f (p ^ i) * g (p ^ (k - i)) := by
  rw [ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal (fun a b => f a * g b),
    Nat.sum_divisors_prime_pow hp]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Nat.pow_div (by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hi) hp.pos]

theorem divisorMoebius_prime_pow (Δ : ℕ) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    divisorMoebius Δ (p ^ k) = if k = 0 then 1 else if k = 1 ∧ p ∣ Δ then -1 else 0 := by
  by_cases hk0 : k = 0
  · simp [hk0]
  rw [divisorMoebius_apply, ArithmeticFunction.moebius_apply_prime_pow hp hk0]
  by_cases hk1 : k = 1 <;> simp [hk0, hk1]

theorem squarefreeIndicator_prime_pow {p : ℕ} (hp : p.Prime) (k : ℕ) :
    squarefreeIndicator (p ^ k) = if k = 0 ∨ k = 1 then 1 else 0 := by
  by_cases hk0 : k = 0
  · simp [hk0]
  change (μ (p ^ k)) * (μ (p ^ k)) = _
  rw [ArithmeticFunction.moebius_apply_prime_pow hp hk0]
  by_cases hk1 : k = 1 <;> simp [hk0, hk1]

theorem coprimeSquarefreeIndicator_prime_pow (Δ : ℕ) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    coprimeSquarefreeIndicator Δ (p ^ k) =
      if k = 0 then 1 else if k = 1 ∧ ¬ p ∣ Δ then 1 else 0 := by
  change (if (p ^ k).Coprime Δ then squarefreeIndicator (p ^ k) else 0) = _
  rw [squarefreeIndicator_prime_pow hp k]
  by_cases hk0 : k = 0
  · simp [hk0]
  by_cases hk1 : k = 1
  · simp [hk1, hp.coprime_iff_not_dvd]
  · simp [hk0, hk1]

theorem squareLift_divisorMoebius_prime_pow (Δ : ℕ) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    squareLift (divisorMoebius Δ) (p ^ k) =
      if k = 0 then 1 else if k = 2 ∧ p ∣ Δ then -1 else 0 := by
  by_cases hk0 : k = 0
  · simp [hk0, squareLift]
  by_cases hk2 : k = 2
  · rw [hk2, squareLift_apply_sq]
    simp [divisorMoebius_apply, ArithmeticFunction.moebius_apply_prime hp]
  simp only [hk0, hk2, false_and, ite_false]
  by_cases hs : IsSquare (p ^ k)
  · obtain ⟨r, hr⟩ := hs
    have hsq : r ^ 2 = p ^ k := by simpa only [sq] using hr.symm
    rw [← hsq, squareLift_apply_sq, divisorMoebius_apply]
    by_cases hsf : Squarefree r
    · have hrp : r ∣ p := (hsf.dvd_pow_iff_dvd hk0).mp
        (hsq ▸ (show r ∣ r ^ 2 from dvd_pow_self r (by decide)))
      rcases (Nat.dvd_prime hp).mp hrp with hr1 | hrp
      · have hp0 : p ^ k = p ^ 0 := by simpa [hr1] using hsq.symm
        exact (hk0 ((Nat.pow_right_inj hp.one_lt).mp hp0)).elim
      · have hp2 : p ^ k = p ^ 2 := by simpa [hrp] using hsq.symm
        exact (hk2 ((Nat.pow_right_inj hp.one_lt).mp hp2)).elim
    · simp [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsf]
  · exact squareLift_apply_of_not_square _ hs

noncomputable def mainAlphaFunction (Δ : ℕ) : ArithmeticFunction ℤ :=
  divisorMoebius Δ * squarefreeIndicator

noncomputable def mainBetaFunction (Δ : ℕ) : ArithmeticFunction ℤ :=
  squareLift (divisorMoebius Δ) * coprimeSquarefreeIndicator Δ

theorem mainAlphaFunction_isMultiplicative (Δ : ℕ) : (mainAlphaFunction Δ).IsMultiplicative :=
  (divisorMoebius_isMultiplicative Δ).mul squarefreeIndicator_isMultiplicative

theorem mainBetaFunction_isMultiplicative (Δ : ℕ) : (mainBetaFunction Δ).IsMultiplicative :=
  (squareLift_isMultiplicative (divisorMoebius_isMultiplicative Δ)).mul
    (coprimeSquarefreeIndicator_isMultiplicative Δ)

theorem mainAlphaFunction_eq_mainBetaFunction_prime_pow (Δ : ℕ) {p : ℕ}
    (hp : p.Prime) (k : ℕ) : mainAlphaFunction Δ (p ^ k) = mainBetaFunction Δ (p ^ k) := by
  simp only [mainAlphaFunction, mainBetaFunction, arithmeticFunction_mul_prime_pow _ _ hp,
    divisorMoebius_prime_pow Δ hp, squarefreeIndicator_prime_pow hp,
    squareLift_divisorMoebius_prime_pow Δ hp, coprimeSquarefreeIndicator_prime_pow Δ hp]
  rcases k with _ | _ | _ | k
  · norm_num
  · by_cases hd : p ∣ Δ <;> simp [Finset.sum_range_succ, hd]
  · by_cases hd : p ∣ Δ <;> simp [Finset.sum_range_succ, hd]
  · have hA : (∑ i ∈ Finset.range (k + 3 + 1),
        (if i = 0 then (1 : ℤ) else if i = 1 ∧ p ∣ Δ then -1 else 0) *
        (if k + 3 - i = 0 ∨ k + 3 - i = 1 then 1 else 0)) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      by_cases hi0 : i = 0
      · simp [hi0]
      by_cases hi1 : i = 1
      · simp [hi1]
      · simp [hi0, hi1]
    have hB : (∑ i ∈ Finset.range (k + 3 + 1),
        (if i = 0 then (1 : ℤ) else if i = 2 ∧ p ∣ Δ then -1 else 0) *
        (if k + 3 - i = 0 then 1 else if k + 3 - i = 1 ∧ ¬ p ∣ Δ then 1 else 0)) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      by_cases hi0 : i = 0
      · simp [hi0]
      by_cases hi2 : i = 2
      · by_cases hd : p ∣ Δ <;> simp [hi2, hd]
      · simp [hi0, hi2]
    exact hA.trans hB.symm

theorem mainAlphaFunction_eq_mainBetaFunction (Δ : ℕ) :
    mainAlphaFunction Δ = mainBetaFunction Δ := by
  apply (ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_prime_powers _
    (mainAlphaFunction_isMultiplicative Δ) _ (mainBetaFunction_isMultiplicative Δ)).mpr
  intro p k hp
  exact mainAlphaFunction_eq_mainBetaFunction_prime_pow Δ hp k

end Ostmann.QuadraticSieve

end OAI
