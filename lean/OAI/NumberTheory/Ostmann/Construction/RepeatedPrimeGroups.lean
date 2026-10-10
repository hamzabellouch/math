import OAI.NumberTheory.Ostmann.Construction.CRTResidueMean
import OAI.NumberTheory.Ostmann.Construction.RepeatedMultiplicity

namespace OAI

noncomputable section
namespace Ostmann.Construction
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def tupleDistinctPrimes (p : ι → ℕ) : Finset ℕ := Finset.univ.image p

def tuplePrimeFiber (p : ι → ℕ) (q : ℕ) : Finset ι := Finset.univ.filter (fun i => p i=q)

def groupedLocalTest (p : ι → ℕ) (F : ι → (q : ℕ) → ZMod q → ℂ) (q : ℕ) (x : ZMod q) : ℂ :=
  ∏i:↥(tuplePrimeFiber p q),F i.val q x

omit [DecidableEq ι] in
lemma groupedLocalTest_eq_prod (p : ι → ℕ) (F : ι → (q : ℕ) → ZMod q → ℂ)
    (q : ℕ) (x : ZMod q) : groupedLocalTest p F q x=∏i∈tuplePrimeFiber p q,F i q x := by
  exact Finset.prod_coe_sort (tuplePrimeFiber p q) (fun i : ι => F i q x)

omit [DecidableEq ι] in
lemma tuplePrimeFiber_nonempty (p : ι → ℕ) {q : ℕ} (hq : q∈tupleDistinctPrimes p) :
    (tuplePrimeFiber p q).Nonempty := by
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hq
  exact ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,rfl⟩⟩

omit [DecidableEq ι] in
theorem groupedLocalTest_product (p : ι → ℕ) (F : ι → (q : ℕ) → ZMod q → ℂ) (n : ℤ) :
    (∏q:↥(tupleDistinctPrimes p),groupedLocalTest p F q (n:ZMod (q:ℕ)))=
      ∏i,F i (p i) (n:ZMod (p i)) := by
  simp_rw [groupedLocalTest_eq_prod]
  rw [Finset.prod_coe_sort (tupleDistinctPrimes p)
    (fun q : ℕ => ∏i∈tuplePrimeFiber p q,F i q (n:ZMod q))]
  calc
    _ = ∏q∈tupleDistinctPrimes p,∏i∈tuplePrimeFiber p q,F i (p i) (n:ZMod (p i)) := by
      apply Finset.prod_congr rfl
      intro q hq
      apply Finset.prod_congr rfl
      intro i hi
      rw [(Finset.mem_filter.mp hi).2]
    _ = _ := Finset.prod_fiberwise_of_maps_to (fun i _ => Finset.mem_image_of_mem p (Finset.mem_univ i)) _

omit [DecidableEq ι] in
lemma tuple_prime_sqrt_product (p : ι → ℕ) :
    (∏q:↥(tupleDistinctPrimes p),(Real.sqrt (q:ℕ))^(tuplePrimeFiber p q).card)=
      Real.sqrt (∏i,p i:ℕ) := by
  rw [Finset.prod_coe_sort (tupleDistinctPrimes p)
    (fun q : ℕ => (Real.sqrt q)^(tuplePrimeFiber p q).card)]
  simp_rw [← Finset.prod_const]
  unfold tupleDistinctPrimes tuplePrimeFiber
  rw [Finset.prod_fiberwise_of_maps_to' (fun i _ => Finset.mem_image_of_mem p (Finset.mem_univ i))]
  rw [Nat.cast_prod,Real.sqrt_prod Finset.univ (fun i _ => Nat.cast_nonneg (p i))]

omit [DecidableEq ι] in
theorem grouped_mean_norm_le (p : ι → ℕ)
    [∀q:↥(tupleDistinctPrimes p),NeZero (q:ℕ)]
    (F : ι → (q : ℕ) → ZMod q → ℂ)
    (hcount : ∀q:↥(tupleDistinctPrimes p),2≤(tuplePrimeFiber p q).card)
    (hF : ∀q:↥(tupleDistinctPrimes p),∀i,(∑x:ZMod (q:ℕ),‖F i q x‖^2)≤(q:ℝ)) :
    ‖∏q:↥(tupleDistinctPrimes p),(∑x:ZMod (q:ℕ),groupedLocalTest p F q x)/(q:ℂ)‖≤
      Real.sqrt (∏i,p i:ℕ)/(∏q:↥(tupleDistinctPrimes p),(q:ℕ):ℕ) := by
  have hQ : (0:ℝ)<(∏q:↥(tupleDistinctPrimes p),(q:ℕ):ℕ) := by
    have h : 0<(∏q:↥(tupleDistinctPrimes p),(q:ℕ)) :=
      Finset.prod_pos (fun (q : ↥(tupleDistinctPrimes p)) _ => NeZero.pos (q:ℕ))
    exact_mod_cast h
  apply (le_div_iff₀ hQ).mpr
  rw [norm_prod,Nat.cast_prod]
  rw [← Finset.prod_mul_distrib,← tuple_prime_sqrt_product p]
  apply Finset.prod_le_prod₀
  · intro q hq
    exact mul_nonneg (norm_nonneg _) (Nat.cast_nonneg _)
  · intro q hq
    have h := repeated_family_mean_mul_card
      (fun i:↥(tuplePrimeFiber p q) => F i.val q)
      (by simpa only [Fintype.card_coe] using hcount q)
      (fun i => by simpa only [ZMod.card] using hF q i.val)
    simpa only [Fintype.card_coe,ZMod.card,groupedLocalTest,mul_comm] using h

omit [DecidableEq ι] in
theorem groupedLocalTest_sum_zero_singleton (p : ι → ℕ)
    (F : ι → (q : ℕ) → ZMod q → ℂ) {q : ℕ} [NeZero q]
    (hcount : (tuplePrimeFiber p q).card=1) (hzero : ∀i,∑x:ZMod q,F i q x=0) :
    (∑x:ZMod q,groupedLocalTest p F q x)=0 := by
  obtain ⟨i,hi⟩ := Finset.card_eq_one.mp hcount
  simp_rw [groupedLocalTest_eq_prod,hi,Finset.prod_singleton]
  exact hzero i

end Ostmann.Construction

end

end OAI
