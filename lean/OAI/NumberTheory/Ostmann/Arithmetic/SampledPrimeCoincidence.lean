import OAI.NumberTheory.Ostmann.Tree.OmittedCoordinate

namespace OAI

/-! # Coincidence bounds when the prime is one of the sampled coordinates

The omitted-variable condition proves the required independence inside one
joint product prior. No separate independent-prime hypothesis is assumed.
-/

namespace Ostmann

open scoped BigOperators Classical

private theorem sampled_prime_divisibility_le {A : Type*} [Fintype A]
    (prime : A → ℕ) (hinj : Function.Injective prime) (hprime : ∀ a, (prime a).Prime)
    (ν : A → ℝ) (β V H : ℝ) (hβ : 0 ≤ β) (hV : 0 < V)
    (hν : ∀ a, ν a ≤ β) (hsize : ∀ a, ν a ≠ 0 → V ≤ Real.log (prime a : ℝ))
    (z : ℤ) (hz : z ≠ 0) (hvalue : |(z : ℝ)| ≤ H) :
    (∑ a, if prime a ∣ z.natAbs then ν a else 0) ≤ (Real.log H / V) * β := by
  let P : Finset ℕ := (Finset.univ.filter fun a => ν a ≠ 0).image prime
  let S : Finset A := Finset.univ.filter fun a => prime a ∣ z.natAbs ∧ ν a ≠ 0
  have hc : S.card ≤ (P.filter fun p => p ∣ z.natAbs).card := by
    apply Finset.card_le_card_of_injOn prime
    · intro a ha
      exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr
        ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp ha).2.2⟩, rfl⟩,
        (Finset.mem_filter.mp ha).2.1⟩
    · exact hinj.injOn
  have hc' := int_prime_divisor_card_le P z hz
    (fun p hp => by obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hp; exact hprime a)
    V H hV
    (fun p hp => by
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hp
      exact hsize a (Finset.mem_filter.mp ha).2) hvalue
  calc
    _ = ∑ a ∈ S, ν a := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro a _
      by_cases hd : prime a ∣ z.natAbs <;> by_cases hn : ν a = 0 <;> simp [hd, hn]
    _ ≤ ∑ _a ∈ S, β := Finset.sum_le_sum fun a _ => hν a
    _ = (S.card : ℝ) * β := by simp
    _ ≤ ((P.filter fun p => p ∣ z.natAbs).card : ℝ) * β :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hc) hβ
    _ ≤ _ := mul_le_mul_of_nonneg_right hc' hβ

theorem sampled_coordinate_prime_coincidence_le {A : Type*} [Fintype A] [Nonempty A]
    {n : ℕ} (value : A → ℤ) (hinj : Function.Injective value)
    (prime : A → ℕ) (hpInj : Function.Injective prime) (hprime : ∀ a, (prime a).Prime)
    (F : MvPolynomial (Fin (n + 1)) ℤ) (hF : F ≠ 0)
    (i : Fin (n + 1)) (hi : i ∉ F.vars)
    (μ : Fin (n + 1) → A → ℝ) (hμ : ∀ j a, 0 ≤ μ j a)
    (hmass : ∀ j, ∑ a, μ j a = 1)
    (α β V H : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β) (hV : 0 < V) (hH : 1 ≤ H)
    (hmax : ∀ j a, μ j a ≤ α) (hpmax : ∀ a, μ i a ≤ β)
    (hsize : ∀ a, μ i a ≠ 0 → V ≤ Real.log (prime a : ℝ))
    (hvalue : ∀ x, |(integerTestValue value F x : ℝ)| ≤ H) :
    (∑ x, productPrior μ x *
      if prime (x i) ∣ (integerTestValue value F x).natAbs then 1 else 0) ≤
      (F.totalDegree : ℝ) * α + (Real.log H / V) * β := by
  let a₀ : A := Classical.arbitrary A
  let z : (Fin n → A) → ℤ := fun x => integerTestValue value F (i.insertNth a₀ x)
  let W := productPrior (fun j => μ (i.succAbove j))
  have hz (x : Fin n → A) (a : A) : integerTestValue value F (i.insertNth a x) = z x :=
    integerTestValue_insertNth_independent value F i hi x a a₀
  have hinner (x : Fin n → A) :
      (∑ a, μ i a * if prime a ∣ (z x).natAbs then (1 : ℝ) else 0) ≤
        (if z x = 0 then 1 else 0) + (Real.log H / V) * β := by
    by_cases hx : z x = 0
    · simp only [hx, Int.natAbs_zero, dvd_zero, ite_true, mul_one, hmass]
      exact le_add_of_nonneg_right (mul_nonneg (div_nonneg (Real.log_nonneg hH) hV.le) hβ)
    · simp only [hx, ite_false, zero_add]
      have he : (∑ a, μ i a * if prime a ∣ (z x).natAbs then (1 : ℝ) else 0) =
          ∑ a, if prime a ∣ (z x).natAbs then μ i a else 0 := by
        apply Finset.sum_congr rfl
        intro a _
        split_ifs <;> simp
      rw [he]
      exact sampled_prime_divisibility_le prime hpInj hprime (μ i) β V H hβ hV hpmax hsize
        (z x) hx (hvalue (i.insertNth a₀ x))
  have hzero : (∑ x, productPrior μ x * if integerTestValue value F x = 0 then (1 : ℝ) else 0) =
      ∑ x, W x * if z x = 0 then 1 else 0 := by
    rw [sum_productPrior_insertNth μ i]
    simp only [hz, ← Finset.sum_mul, hmass, one_mul, W]
  have hbound : (∑ x, productPrior μ x *
      if prime (x i) ∣ (integerTestValue value F x).natAbs then 1 else 0) ≤
      (∑ x, W x * if z x = 0 then 1 else 0) + (Real.log H / V) * β := by
    rw [sum_productPrior_insertNth μ i]
    simp only [Fin.insertNth_apply_same, hz]
    calc
      _ ≤ ∑ x, W x * ((if z x = 0 then 1 else 0) + (Real.log H / V) * β) := by
        apply Finset.sum_le_sum
        intro x _
        exact mul_le_mul_of_nonneg_left (hinner x)
          (productPrior_nonneg _ (fun j a => hμ (i.succAbove j) a) x)
      _ = _ := by
        simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul]
        rw [show (∑ x, W x) = 1 from productPrior_mass _ (fun j => hmass (i.succAbove j)), one_mul]
  rw [← hzero] at hbound
  have hroot := weighted_polynomial_roots_le (fun a => (value a : ℚ))
    (Int.cast_injective.comp hinj) α hα (MvPolynomial.map (Int.castRingHom ℚ) F)
    (fun hz => hF ((integerPolynomial_rational_zero_iff F).mp hz)) μ hμ hmass hmax
  simp only [integerPolynomial_rational_eval, Int.cast_eq_zero, integerPolynomial_rational_degree] at hroot
  change (∑ x, productPrior μ x * if integerTestValue value F x = 0 then (1 : ℝ) else 0) ≤
    (F.totalDegree : ℝ) * α at hroot
  exact hbound.trans (by linarith [hroot])

end Ostmann

end OAI
