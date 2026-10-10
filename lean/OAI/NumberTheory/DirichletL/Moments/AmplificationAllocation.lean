import OAI.NumberTheory.DirichletL.Moments.AmplificationShortening

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentAmplificationAllocation
open CanonicalQuadraticSieve CanonicalRowCompletion ConcretePrimeRowBridge CompletedGauss
open CenteredMomentAmplificationGlobal CenteredMomentSupportedCorrelation
local notation "O" => ActualEisensteinCubic.O

theorem primaryGenerator_power (I : Ideal O) (n : ℕ) :
    primaryGenerator (I^n) = primaryGenerator I ^ n := map_pow primaryGeneratorHom I n

theorem primeRemainder_primary (p : O) (hp : Prime p) (hpp : goodLambda^2 ∣ p-1)
    (a : O) (ha : Supported (Ideal.span {a})) (hpa : goodLambda^2 ∣ a-1) :
    goodLambda^2 ∣ primeRemainder p hp a (supported_element_ne_zero a ha)-1 := by
  let r := primeRemainder p hp a (supported_element_ne_zero a ha)
  have hr := primeRemainder_supported p hp a ha
  have hgen := supported_primaryGenerator_ne_zero (Ideal.span {r}) hr
  have he : a = p^(multiplicity p a)*primaryGenerator (Ideal.span {r}) := by
    calc
      a = primaryGenerator (Ideal.span {a}) := (primaryGenerator_span a
        (supported_element_ne_zero a ha) hpa).symm
      _ = _ := by
        conv_lhs => rw [(primeRemainder_spec p hp a (supported_element_ne_zero a ha)).1]
        rw [← Ideal.span_singleton_mul_span_singleton,primaryGenerator_mul,
          ← Ideal.span_singleton_pow,primaryGenerator_power,primaryGenerator_span p hp.ne_zero hpp]
  have hre : r = primaryGenerator (Ideal.span {r}) := by
    apply mul_left_cancel₀ (pow_ne_zero (multiplicity p a) hp.ne_zero)
    exact (primeRemainder_spec p hp a (supported_element_ne_zero a ha)).1.symm.trans he
  change goodLambda^2 ∣ r-1
  rw [hre]
  exact (primaryGenerator_spec _ hgen).2

theorem plain_product_valuation (p : O) (hp : Prime p) (q a b : O)
    (hq : q ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0) (hpq : ¬p ∣ q) :
    multiplicity p (q*a*b) = multiplicity p a + multiplicity p b := by
  rw [multiplicity_mul hp (FiniteMultiplicity.of_prime_left hp (mul_ne_zero (mul_ne_zero hq ha) hb)),
    multiplicity_mul hp (FiniteMultiplicity.of_prime_left hp (mul_ne_zero hq ha)),
    multiplicity_eq_zero_of_not_dvd hpq,zero_add]

theorem plain_product_remainder (p : O) (hp : Prime p) (q a b : O)
    (ha : a ≠ 0) (hb : b ≠ 0) :
    q*a*b = p^(multiplicity p a + multiplicity p b) *
      (q*primeRemainder p hp a ha*primeRemainder p hp b hb) := by
  conv_lhs => rw [(primeRemainder_spec p hp a ha).1,(primeRemainder_spec p hp b hb).1]
  rw [pow_add]
  ring

theorem split_plain_valuation {α β : Type*} (S : Finset α) (T : Finset β)
    (v : α → ℕ) (w : β → ℕ) (k : ℕ) (c : α → β → ℂ) :
    (∑ i ∈ S, ∑ j ∈ T, if v i + w j = k then c i j else 0) =
      ∑ r ∈ Finset.range (k+1), ∑ i ∈ S, ∑ j ∈ T,
        if v i = r ∧ w j = k-r then c i j else 0 := by
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hk : v i + w j = k
  · rw [ite_eq_left hk,Finset.sum_eq_single (v i)]
    · simp only [true_and]
      rw [ite_eq_left (by omega)]
    · intro r hr hne
      rw [ite_eq_right (fun h => hne h.1.symm)]
    · intro hnot
      exact False.elim (hnot (Finset.mem_range.mpr (by omega)))
  · rw [ite_eq_right hk]
    symm
    apply Finset.sum_eq_zero
    intro r hr
    rw [ite_eq_right]
    intro h
    exact hk (by have hh := Finset.mem_range.mp hr; omega)

theorem split_actual_plain_product {α β : Type*} (S : Finset α) (T : Finset β)
    (p : O) (hp : Prime p) (q : O) (hq : q ≠ 0) (hpq : ¬p ∣ q)
    (a : α → O) (ha : ∀ i, a i ≠ 0) (b : β → O) (hb : ∀ j, b j ≠ 0)
    (k : ℕ) (c : α → β → ℂ) :
    (∑ i ∈ S, ∑ j ∈ T, if multiplicity p (q*a i*b j) = k then c i j else 0) =
      ∑ r ∈ Finset.range (k+1), ∑ i ∈ S, ∑ j ∈ T,
        if multiplicity p (a i) = r ∧ multiplicity p (b j) = k-r then c i j else 0 := by
  simp_rw [plain_product_valuation p hp q _ _ hq (ha _) (hb _) hpq]
  exact split_plain_valuation S T _ _ k c

theorem error_allocation_count (k : ℕ) (hk : k=1 ∨ k=6 ∨ k=7) :
    (Finset.range (k+1)).card ≤ 8 := by
  rw [Finset.card_range]
  rcases hk with rfl | rfl | rfl <;> omega

end SevenEighths.CenteredMomentAmplificationAllocation

end

end OAI
