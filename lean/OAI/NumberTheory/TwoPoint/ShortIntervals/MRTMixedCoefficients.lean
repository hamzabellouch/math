import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTPrimeMoments
import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTFactoredReciprocal

namespace OAI

/-! Coefficients of a prime-polynomial power times a cofactor polynomial.
The cofactor may carry arbitrary bounded masks. Unique factorization costs
only the prime-tuple factorial; the remaining multiplicity is the literal
number of supported divisors, whose second moment was proved separately. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma mrt_prime_tuple_factored {r : ℕ} (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (v : Fin r → ℕ)
    (hv : v ∈ Fintype.piFinset (fun _ : Fin r => P)) :
    (∏ i, v i) ∈ Nat.factoredNumbers P := by
  apply Nat.mem_factoredNumbers'.mpr
  intro p hp hdiv
  obtain ⟨i, _, hi⟩ := (hp.prime.dvd_finsetProd_iff v).mp hdiv
  have hvi := Fintype.mem_piFinset.mp hv i
  have he := (Nat.prime_dvd_prime_iff_eq hp (hP _ hvi)).mp hi
  exact he.symm ▸ hvi

noncomputable def mrtMixedPrimeFiber (P M : Finset ℕ) (r n : ℕ) :
    Finset ((Fin r → ℕ) × ℕ) :=
  ((Fintype.piFinset (fun _ : Fin r => P)) ×ˢ M).filter
    (fun v => (∏ i, v.1 i) * v.2 = n)

theorem mrt_mixed_prime_fiber_card (P M : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (r : ℕ) {n U : ℕ} (hn : 0 < n) (hnU : n ≤ U) :
    (mrtMixedPrimeFiber P M r n).card ≤ r.factorial *
      (((mrtFactoredUpTo P U).filter (fun d => d ∣ n)).card) := by
  let V := Fintype.piFinset (fun _ : Fin r => P)
  let S := mrtMixedPrimeFiber P M r n
  let D := (mrtFactoredUpTo P U).filter (fun d => d ∣ n)
  have htuple (v : Fin r → ℕ) (hv : v ∈ V) : 0 < ∏ i, v i :=
    prod_pos (fun i _ => (hP _ (Fintype.mem_piFinset.mp hv i)).pos)
  have hmap : ∀ v ∈ S, (∏ i, v.1 i) ∈ D := by
    intro v hv
    obtain ⟨hvm, hprod⟩ := mem_filter.mp hv
    obtain ⟨hvP, _⟩ := mem_product.mp hvm
    have hd : (∏ i, v.1 i) ∣ n := hprod ▸ dvd_mul_right _ _
    refine mem_filter.mpr ⟨mem_filter.mpr ⟨mem_Icc.mpr
      ⟨htuple _ hvP, (Nat.le_of_dvd hn hd).trans hnU⟩,
      mrt_prime_tuple_factored P hP v.1 hvP⟩, hd⟩
  have hfiber (d : ℕ) : (S.filter (fun v => (∏ i, v.1 i) = d)).card ≤ r.factorial := by
    apply le_trans (card_le_card_of_injOn Prod.fst ?_ ?_)
      (mrt_prime_product_fiber_card V (fun v hv i =>
        hP _ (Fintype.mem_piFinset.mp hv i)) d)
    · intro v hv
      obtain ⟨hvS, hvd⟩ := mem_filter.mp hv
      exact mem_filter.mpr ⟨(mem_product.mp (mem_filter.mp hvS).1).1, hvd⟩
    · intro v hv w hw he
      obtain ⟨hvS, _⟩ := mem_filter.mp hv
      obtain ⟨hwS, _⟩ := mem_filter.mp hw
      have hvp := (mem_filter.mp hvS).2
      have hwp := (mem_filter.mp hwS).2
      apply Prod.ext he
      apply Nat.eq_of_mul_eq_mul_left
        (htuple v.1 (mem_product.mp (mem_filter.mp hvS).1).1)
      calc
        _ = n := hvp
        _ = _ := by rw [he]; exact hwp.symm
  have hcount : (∑ d ∈ D, (S.filter (fun v => (∏ i, v.1 i) = d)).card) = S.card := by
    simpa using (sum_fiberwise_of_maps_to hmap (fun _ => (1 : ℕ)))
  rw [← hcount]
  calc
    _ ≤ ∑ _d ∈ D, r.factorial := sum_le_sum (fun d _ => hfiber d)
    _ = _ := by simp [D, Nat.mul_comm]

noncomputable def mrtMixedPrimeCoefficient (P M : Finset ℕ)
    (a b : ℕ → ℂ) (r n : ℕ) : ℂ :=
  ∑ v ∈ mrtMixedPrimeFiber P M r n, (∏ i, a (v.1 i)) * b v.2

theorem mrt_mixed_prime_coefficient_bound (P M : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (a b : ℕ → ℂ)
    (ha : ∀ p ∈ P, ‖a p‖ ≤ 1) (hb : ∀ m ∈ M, ‖b m‖ ≤ 1)
    (r : ℕ) {n U : ℕ} (hn : 0 < n) (hnU : n ≤ U) :
    ‖mrtMixedPrimeCoefficient P M a b r n‖ ≤ (r.factorial : ℝ) *
      (((mrtFactoredUpTo P U).filter (fun d => d ∣ n)).card : ℝ) := by
  have ht (v : (Fin r → ℕ) × ℕ) (hv : v ∈ mrtMixedPrimeFiber P M r n) :
      ‖(∏ i, a (v.1 i)) * b v.2‖ ≤ 1 := by
    obtain ⟨hvm, _⟩ := mem_filter.mp hv
    obtain ⟨hvP, hvM⟩ := mem_product.mp hvm
    rw [norm_mul, norm_prod]
    have hp : (∏ i, ‖a (v.1 i)‖) ≤ 1 :=
      prod_le_one₀ (fun _ _ => norm_nonneg _)
        (fun i _ => ha _ (Fintype.mem_piFinset.mp hvP i))
    exact (mul_le_mul hp (hb _ hvM) (norm_nonneg _) zero_le_one).trans_eq (mul_one 1)
  calc
    _ ≤ ∑ _v ∈ mrtMixedPrimeFiber P M r n, (1 : ℝ) :=
      (norm_sum_le _ _).trans (sum_le_sum ht)
    _ = ((mrtMixedPrimeFiber P M r n).card : ℝ) := by simp
    _ ≤ _ := by exact_mod_cast mrt_mixed_prime_fiber_card P M hP r hn hnU

end TwoPointCorrelations

end OAI
