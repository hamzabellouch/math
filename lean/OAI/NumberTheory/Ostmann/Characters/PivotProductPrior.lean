import Mathlib.Algebra.BigOperators.Associated
import OAI.NumberTheory.Ostmann.Construction.DistinctTupleProducts
import OAI.NumberTheory.Ostmann.Construction.HarmonicWordPriors

namespace OAI

/-! # The original prior of an internally distinct pivot total -/

namespace Ostmann

open scoped BigOperators Classical

private theorem tupleImage_mem_iff_dvd (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    {n : ℕ} (e : Fin n ↪ P) (q : P) :
    q ∈ tupleImage e ↔ (q : ℕ) ∣ ∏ i, (e i : ℕ) := by
  constructor
  · intro hq
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hq
    rw [← hi]
    exact Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
  · intro hq
    obtain ⟨i, _, hi⟩ := ((hP _ q.property).prime.dvd_finsetProd_iff (fun i => (e i : ℕ))).mp hq
    have he : (q : ℕ) = (e i : ℕ) :=
      ((Nat.dvd_prime (hP _ (e i).property)).mp hi).resolve_left (hP _ q.property).ne_one
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, Subtype.ext he.symm⟩

private theorem tupleImage_eq_of_product_eq (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    {n : ℕ} (e f : Fin n ↪ P) (h : (∏ i, (e i : ℕ)) = ∏ i, (f i : ℕ)) :
    tupleImage e = tupleImage f := by
  ext q
  rw [tupleImage_mem_iff_dvd P hP, tupleImage_mem_iff_dvd P hP, h]

theorem card_distinct_prime_product_fiber (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (n M : ℕ) :
    ((Finset.univ : Finset (Fin n → P)).filter
      (fun x : Fin n → P => Function.Injective x ∧ (∏ i, (x i : ℕ)) = M)).card ≤ n.factorial := by
  let S := (Finset.univ : Finset (Fin n → P)).filter
    (fun x : Fin n → P => Function.Injective x ∧ (∏ i, (x i : ℕ)) = M)
  by_cases hs : S.Nonempty
  · obtain ⟨x, hx⟩ := hs
    have hxp := (Finset.mem_filter.mp hx).2
    let e : Fin n ↪ P := ⟨x, hxp.1⟩
    let f : S → {g : Fin n ↪ P // tupleImage g = tupleImage e} := fun y =>
      ⟨⟨y.val, (Finset.mem_filter.mp y.property).2.1⟩,
        tupleImage_eq_of_product_eq P hP _ e
          ((Finset.mem_filter.mp y.property).2.2.trans hxp.2.symm)⟩
    have hf : Function.Injective f := by
      intro y z hyz
      apply Subtype.ext
      exact congrArg (fun w : {g : Fin n ↪ P // tupleImage g = tupleImage e} => w.val.toFun) hyz
    have hcard : (tupleImage e).card = n := by
      rw [tupleImage, Finset.card_image_of_injective _ e.injective]
      simp
    have hc := Fintype.card_le_of_injective f hf
    rw [card_tupleImage_fiber n (tupleImage e) hcard] at hc
    change S.card ≤ n.factorial
    simpa only [Fintype.card_coe] using hc
  · have he : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    change S.card ≤ n.factorial
    rw [he, Finset.card_empty]
    exact Nat.zero_le _

theorem harmonic_product_point_bound (P : Finset ℕ) {n : ℕ}
    (Q : Fin n → Finset ℕ) (x : Fin n → P) :
    productPrior (fun i => primeSubsetPrior P (Q i)) x ≤
      (∏ i, (∑ p ∈ Q i, (p : ℝ)⁻¹)⁻¹) * (∏ i, (x i : ℝ))⁻¹ := by
  by_cases hx : productPrior (fun i => primeSubsetPrior P (Q i)) x = 0
  · rw [hx]
    positivity
  · rw [primeSubsetPrior_product P Q x hx, Finset.prod_inv_distrib]

theorem harmonic_distinct_product_mass (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    {n : ℕ} (Q : Fin n → Finset ℕ) (S : Finset (Fin n → P))
    (hS : ∀ x ∈ S, Function.Injective x) (M : ℕ) :
    (∑ x ∈ S.filter (fun x => (∏ i, (x i : ℕ)) = M),
      productPrior (fun i => primeSubsetPrior P (Q i)) x) ≤
      (n.factorial : ℝ) * (∏ i, (∑ p ∈ Q i, (p : ℝ)⁻¹)⁻¹) * (M : ℝ)⁻¹ := by
  let T := S.filter (fun x => (∏ i, (x i : ℕ)) = M)
  have hc : T.card ≤ n.factorial := by
    apply (Finset.card_le_card (show T ⊆ (Finset.univ : Finset (Fin n → P)).filter
      (fun x : Fin n → P => Function.Injective x ∧ (∏ i, (x i : ℕ)) = M) from ?_)).trans
      (card_distinct_prime_product_fiber P hP n M)
    intro x hx
    obtain ⟨hxS, hxM⟩ := Finset.mem_filter.mp hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ x, hS x hxS, hxM⟩
  calc
    _ ≤ ∑ _x ∈ T, (∏ i, (∑ p ∈ Q i, (p : ℝ)⁻¹)⁻¹) * (M : ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro x hx
      have hb := harmonic_product_point_bound P Q x
      have he : (∏ i, (x i : ℝ)) = (M : ℝ) := by
        exact_mod_cast (Finset.mem_filter.mp hx).2
      simpa only [he] using hb
    _ = (T.card : ℝ) * ((∏ i, (∑ p ∈ Q i, (p : ℝ)⁻¹)⁻¹) * (M : ℝ)⁻¹) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ _ := by
      have hc' : (T.card : ℝ) ≤ n.factorial := by exact_mod_cast hc
      nlinarith [mul_le_mul_of_nonneg_right hc'
        (show 0 ≤ (∏ i, (∑ p ∈ Q i, (p : ℝ)⁻¹)⁻¹) * (M : ℝ)⁻¹ by positivity)]

end Ostmann

end OAI
