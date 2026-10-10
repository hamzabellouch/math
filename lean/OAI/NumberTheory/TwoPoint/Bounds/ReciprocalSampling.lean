import OAI.NumberTheory.TwoPoint.Bounds.ReciprocalProgressions
import OAI.NumberTheory.TwoPoint.Bounds.PrimeRelations

namespace OAI

/-! Reciprocal-weighted prime sampling and concrete triangular relation bounds. -/

namespace TwoPointCorrelations

open Finset

namespace FiniteLaw

variable {A : Type*} [Fintype A]

/-- A reciprocal atom majorant transfers the finite progression bound to
sampling probability. For the normalized law `1/(Vp)`, it suffices that
`V ≥ 1`, exactly as in the singleton argument. -/
theorem reciprocal_probability_bound (μ : FiniteLaw A) (value : A → ℕ)
    (hinj : Function.Injective value) (H N p : ℕ) (C D : ℤ)
    (hH : 0 < H) (hN : 1 ≤ N) (hp : p.Prime) (hC : ¬(p : ℤ) ∣ C)
    (hlo : ∀ a, H ≤ value a) (hhi : ∀ a, value a ≤ N)
    (hweight : ∀ a, μ.weight a ≤ (value a : ℝ)⁻¹)
    (E : A → Prop) (hE : ∀ a, E a → (p : ℤ) ∣ C * value a + D) :
    μ.probability E ≤ (H : ℝ)⁻¹ + (1 + Real.log N) / p := by
  classical
  let S : Finset A := univ.filter E
  let T : Finset ℕ := S.image value
  have hprob : μ.probability E = ∑ a ∈ S, μ.weight a := by
    simp only [probability, average, S, sum_filter, mul_ite, mul_one, mul_zero]
  have himage : (∑ a ∈ S, (value a : ℝ)⁻¹) = ∑ x ∈ T, (x : ℝ)⁻¹ := by
    dsimp [T]
    rw [sum_image (fun a _ b _ hab => hinj hab)]
  rw [hprob]
  apply (sum_le_sum (fun a _ => hweight a)).trans
  rw [himage]
  apply reciprocal_linear_congruence_sum T H N p C D hH hN hp hC
  · intro x hx
    obtain ⟨a, _, rfl⟩ := mem_image.mp hx
    exact hlo a
  · intro x hx
    obtain ⟨a, _, rfl⟩ := mem_image.mp hx
    exact hhi a
  · intro x hx
    obtain ⟨a, ha, rfl⟩ := mem_image.mp hx
    exact hE a (mem_filter.mp ha).2

/-- Retain the coefficient test during summation. A vanishing coefficient
makes the event empty and costs zero, so no case is lost by resampling. -/
theorem nondegenerate_reciprocal_probability_bound (μ : FiniteLaw A) (value : A → ℕ)
    (hinj : Function.Injective value) (H N p : ℕ) (C D : ℤ)
    (hH : 0 < H) (hN : 1 ≤ N) (hp : p.Prime)
    (hlo : ∀ a, H ≤ value a) (hhi : ∀ a, value a ≤ N)
    (hweight : ∀ a, μ.weight a ≤ (value a : ℝ)⁻¹) :
    μ.probability (fun a => (p : ℤ) ∣ C * value a + D ∧ ¬(p : ℤ) ∣ C) ≤
      (H : ℝ)⁻¹ + (1 + Real.log N) / p := by
  by_cases hC : (p : ℤ) ∣ C
  · have hzero : μ.probability (fun a => (p : ℤ) ∣ C * value a + D ∧ ¬(p : ℤ) ∣ C) = 0 := by
      simp [probability, average, hC]
    rw [hzero]
    have hlog : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hN)
    positivity
  · exact reciprocal_probability_bound μ value hinj H N p C D hH hN hp hC hlo hhi hweight
      _ (fun _ ha => ha.1)

end FiniteLaw

variable {ι A : Type*} [DecidableEq ι]

def integerPrimeAssignment (value : A → ℕ) (x : ι → A) : ι → ℤ := fun i => value (x i)

lemma integerPrimeAssignment_update (value : A → ℕ) (x : ι → A) (i : ι) (a : A) :
    integerPrimeAssignment value (Function.update x i a) =
      Function.update (integerPrimeAssignment value x) i (value a) := by
  funext j
  by_cases hji : j = i <;> simp [integerPrimeAssignment, hji]

/-- At a selected coordinate, the concrete monomial event is precisely a
single nondegenerate linear congruence with all remaining variables fixed. -/
lemma primeRelationEvent_update_selected {τ : Type*} [Fintype τ]
    (m : τ → PrimeMonomial ι) (selected control : ι) (hne : control ≠ selected)
    (value : A → ℕ) (x : ι → A) (a : A) :
    primeRelationEvent m selected control
        (integerPrimeAssignment value (Function.update x selected a)) ↔
      (value (x control) : ℤ) ∣
          primeRelationCoefficient m selected (integerPrimeAssignment value x) * value a +
          primeRelationConstant m selected (integerPrimeAssignment value x) ∧
        ¬(value (x control) : ℤ) ∣
          primeRelationCoefficient m selected (integerPrimeAssignment value x) := by
  rw [integerPrimeAssignment_update]
  unfold primeRelationEvent
  rw [Function.update_of_ne hne, primeRelation_update_affine,
    primeRelation_coefficient_update_self]
  simp only [integerPrimeAssignment]
  rw [mul_comm (value a : ℤ)]

/-- The pointwise support exclusion proved for the witness ordering is the
exact update invariance required by finite triangular elimination. -/
lemma primeRelationEvent_update_irrelevant {τ : Type*} [Fintype τ]
    (m : τ → PrimeMonomial ι) (selected control j : ι)
    (value : A → ℕ) (x : ι → A) (a : A)
    (hj : j ∉ primeRelationSupport m) (hjc : control ≠ j) :
    primeRelationEvent m selected control (integerPrimeAssignment value (Function.update x j a)) ↔
      primeRelationEvent m selected control (integerPrimeAssignment value x) := by
  rw [integerPrimeAssignment_update]
  exact primeRelationEvent_update m selected control j _ _ hj hjc

namespace FiniteLaw

/-- Fully finite singleton saving for an explicitly triangular family of
prime-monomial relations. Later variables occur neither in earlier
relations nor in their controlling primes. -/
theorem triangular_prime_relation_probability {τ : Type*} [Fintype τ]
    [Fintype ι] [LinearOrder ι] [Fintype A] [Nonempty A]
    (μ : ι → FiniteLaw A) (value : A → ℕ) (hinj : Function.Injective value)
    (H N : ℕ) (hH : 0 < H) (hN : 1 ≤ N)
    (hprime : ∀ a, (value a).Prime)
    (hlo : ∀ a, H ≤ value a) (hhi : ∀ a, value a ≤ N)
    (hweight : ∀ i a, (μ i).weight a ≤ (value a : ℝ)⁻¹)
    (m : ι → τ → PrimeMonomial ι) (control : ι → ι)
    (R : Finset ι)
    (hcontrol : ∀ i ∈ R, control i ≠ i)
    (htriangular : ∀ i ∈ R, ∀ j ∈ R, i < j →
      j ∉ primeRelationSupport (m i) ∧ control i ≠ j) :
    (independent μ).probability (fun x => ∀ i ∈ R,
      primeRelationEvent (m i) i (control i) (integerPrimeAssignment value x)) ≤
        ((H : ℝ)⁻¹ + (1 + Real.log N) / H) ^ R.card := by
  classical
  let E : ι → (ι → A) → Prop := fun i x =>
    primeRelationEvent (m i) i (control i) (integerPrimeAssignment value x)
  have hlog : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hN)
  apply triangular_probability_bound μ E _ (by positivity) R ?_ ?_
  · intro i hi j hj hij x a
    exact primeRelationEvent_update_irrelevant (m i) i (control i) j value x a
      (htriangular i hi j hj hij).1 (htriangular i hi j hj hij).2
  · intro i hi x
    have hlinear := nondegenerate_reciprocal_probability_bound (μ i) value hinj
      H N (value (x (control i)))
      (primeRelationCoefficient (m i) i (integerPrimeAssignment value x))
      (primeRelationConstant (m i) i (integerPrimeAssignment value x))
      hH hN (hprime _) hlo hhi (hweight i)
    have hevent : (fun a => E i (Function.update x i a)) =
        (fun a => (value (x (control i)) : ℤ) ∣
          primeRelationCoefficient (m i) i (integerPrimeAssignment value x) * value a +
          primeRelationConstant (m i) i (integerPrimeAssignment value x) ∧
          ¬(value (x (control i)) : ℤ) ∣
            primeRelationCoefficient (m i) i (integerPrimeAssignment value x)) := by
      funext a
      exact propext (primeRelationEvent_update_selected (m i) i (control i) (hcontrol i hi) value x a)
    rw [hevent]
    apply hlinear.trans
    apply add_le_add le_rfl
    exact div_le_div_of_nonneg_left (by linarith) (by exact_mod_cast hH)
      (by exact_mod_cast hlo (x (control i)))

end FiniteLaw

end TwoPointCorrelations

end OAI
