import OAI.NumberTheory.Ostmann.Construction.RepeatedPrimeGroups

namespace OAI

noncomputable section
namespace Ostmann.Construction
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
lemma tuple_prime_power_product (p : ι → ℕ) :
    (∏q∈tupleDistinctPrimes p,q^(tuplePrimeFiber p q).card)=∏i,p i := by
  simp_rw [← Finset.prod_const]
  unfold tupleDistinctPrimes tuplePrimeFiber
  exact Finset.prod_fiberwise_of_maps_to' (fun i _ => Finset.mem_image_of_mem p (Finset.mem_univ i)) _

omit [DecidableEq ι] in
theorem repeated_prime_mul_distinct_le (p : ι → ℕ) (hp : ∀i,1≤p i)
    (hn : ¬Function.Injective p) :
    ∃q∈tupleDistinctPrimes p, q*(∏r∈tupleDistinctPrimes p,r)≤∏i,p i := by
  classical
  obtain ⟨i,j,hij,hne⟩ := Function.not_injective_iff.mp hn
  have hqi : p i∈tupleDistinctPrimes p := Finset.mem_image_of_mem p (Finset.mem_univ i)
  have hi : i∈tuplePrimeFiber p (p i) := Finset.mem_filter.mpr ⟨Finset.mem_univ _,rfl⟩
  have hj : j∈tuplePrimeFiber p (p i) := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hij.symm⟩
  have hc : 2≤(tuplePrimeFiber p (p i)).card := by
    exact Finset.one_lt_card.mpr ⟨i,hi,j,hj,hne⟩
  have hrest : (∏r∈(tupleDistinctPrimes p).erase (p i),r)≤
      ∏r∈(tupleDistinctPrimes p).erase (p i),r^(tuplePrimeFiber p r).card := by
    apply Finset.prod_le_prod
    intro q hq
    have hqp := (Finset.mem_erase.mp hq).2
    have hcard : 1≤(tuplePrimeFiber p q).card := Finset.card_pos.mpr (tuplePrimeFiber_nonempty p hqp)
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hqp
    simpa only [pow_one] using Nat.pow_le_pow_right (hp j) hcard
  have hpow : (p i)^2≤(p i)^(tuplePrimeFiber p (p i)).card := Nat.pow_le_pow_right (hp i) hc
  refine ⟨p i,hqi,?_⟩
  calc
    _ = (p i)^2*(∏r∈(tupleDistinctPrimes p).erase (p i),r) := by
      rw [← Finset.mul_prod_erase (tupleDistinctPrimes p) (fun r : ℕ => r) hqi]
      ring
    _ ≤ (p i)^(tuplePrimeFiber p (p i)).card*
        (∏r∈(tupleDistinctPrimes p).erase (p i),r^(tuplePrimeFiber p r).card) := Nat.mul_le_mul hpow hrest
    _ = ∏r∈tupleDistinctPrimes p,r^(tuplePrimeFiber p r).card :=
      Finset.mul_prod_erase (tupleDistinctPrimes p) (fun r : ℕ => r^(tuplePrimeFiber p r).card) hqi
    _ = _ := tuple_prime_power_product p

omit [DecidableEq ι] in
theorem repeated_distinct_product_le_div (p : ι → ℕ) (hp : ∀i,1≤p i)
    (hn : ¬Function.Injective p) {R : ℝ} (hR : 0<R) (hmin : ∀i,R≤(p i:ℝ)) :
    ((∏q:↥(tupleDistinctPrimes p),(q:ℕ):ℕ):ℝ)≤(∏i,(p i:ℝ))/R := by
  obtain ⟨q,hq,hprod⟩ := repeated_prime_mul_distinct_le p hp hn
  obtain ⟨i,hi,hqi⟩ := Finset.mem_image.mp hq
  have hminq : R≤(q:ℝ) := hqi ▸ hmin i
  have hprod' : (q:ℝ)*((∏r∈tupleDistinctPrimes p,r:ℕ):ℝ)≤∏i,(p i:ℝ) := by
    exact_mod_cast hprod
  apply (le_div_iff₀ hR).mpr
  have he : (∏q:↥(tupleDistinctPrimes p),(q:ℕ))=∏q∈tupleDistinctPrimes p,q :=
    Finset.prod_coe_sort _ (fun q : ℕ => q)
  rw [he]
  have hmul := mul_le_mul_of_nonneg_right hminq (Nat.cast_nonneg (α := ℝ) (∏r∈tupleDistinctPrimes p,r))
  nlinarith

end Ostmann.Construction

end

end OAI
