import OAI.NumberTheory.CubicMoment.Estimates.SquarefreeMajorant

namespace OAI

/-!
# Collecting the squarefree majorant by least common multiples

The join is the product of the union of the primary prime factors. Its
square divides an element exactly when both input squares divide it.
-/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def primarySquarefreeJoin (a b : Eisenstein) : Eisenstein :=
  ∏ p ∈ primaryPrimeFactors a ∪ primaryPrimeFactors b, p

lemma join_factor_primaryPrime {a b p : Eisenstein} (ha : primary a) (hb : primary b)
    (hp : p ∈ primaryPrimeFactors a ∪ primaryPrimeFactors b) : primaryPrime p := by
  rcases Finset.mem_union.mp hp with hp | hp
  · exact (primaryPrimeFactor_spec ha hp).1
  · exact (primaryPrimeFactor_spec hb hp).1

lemma primarySquarefreeJoin_primary {a b : Eisenstein} (ha : primary a) (hb : primary b) :
    primary (primarySquarefreeJoin a b) :=
  primary_finset_prod _ _ (fun _p hp => (join_factor_primaryPrime ha hb hp).1)

lemma primarySquarefreeJoin_squarefree {a b : Eisenstein} (ha : primary a) (hb : primary b) :
    Squarefree (primarySquarefreeJoin a b) := by
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro p hp q hq hpq
    exact isRelPrime_iff_isCoprime.mpr
      (primaryPrimes_isCoprime (join_factor_primaryPrime ha hb hp)
        (join_factor_primaryPrime ha hb hq) hpq)
  · intro p hp
    exact (join_factor_primaryPrime ha hb hp).2.squarefree

lemma dvd_primarySquarefreeJoin_left {a b : Eisenstein} (ha : primary a) (hsa : Squarefree a) :
    a ∣ primarySquarefreeJoin a b := by
  nth_rw 1 [← primaryPrimeFactors_prod ha hsa]
  exact Finset.prod_dvd_prod_of_subset _ _ _ Finset.subset_union_left

lemma dvd_primarySquarefreeJoin_right {a b : Eisenstein} (hb : primary b) (hsb : Squarefree b) :
    b ∣ primarySquarefreeJoin a b := by
  nth_rw 1 [← primaryPrimeFactors_prod hb hsb]
  exact Finset.prod_dvd_prod_of_subset _ _ _ Finset.subset_union_right

/-- This is the divisor condition used in the collected sieve square. -/
theorem primarySquarefreeJoin_sq_dvd_iff {a b : Eisenstein}
    (ha : primary a) (hb : primary b) (hsa : Squarefree a) (hsb : Squarefree b)
    (n : Eisenstein) :
    (primarySquarefreeJoin a b)^2 ∣ n ↔ a^2 ∣ n ∧ b^2 ∣ n := by
  constructor
  · intro h
    exact ⟨(pow_dvd_pow_of_dvd (dvd_primarySquarefreeJoin_left ha hsa) 2).trans h,
      (pow_dvd_pow_of_dvd (dvd_primarySquarefreeJoin_right hb hsb) 2).trans h⟩
  · rintro ⟨han,hbn⟩
    unfold primarySquarefreeJoin
    rw [← Finset.prod_pow]
    apply Finset.prod_dvd_of_coprime
    · intro p hp q hq hpq
      exact (primaryPrimes_isCoprime (join_factor_primaryPrime ha hb hp)
        (join_factor_primaryPrime ha hb hq) hpq).pow
    · intro p hp
      rcases Finset.mem_union.mp hp with hp | hp
      · exact (pow_dvd_pow_of_dvd (primaryPrimeFactor_spec ha hp).2 2).trans han
      · exact (pow_dvd_pow_of_dvd (primaryPrimeFactor_spec hb hp).2 2).trans hbn

lemma primarySquarefreeJoin_dvd_mul {a b : Eisenstein} (ha : primary a) (hb : primary b) :
    primarySquarefreeJoin a b ∣ a*b := by
  apply Finset.prod_dvd_of_coprime
  · intro p hp q hq hpq
    exact primaryPrimes_isCoprime (join_factor_primaryPrime ha hb hp)
      (join_factor_primaryPrime ha hb hq) hpq
  · intro p hp
    rcases Finset.mem_union.mp hp with hp | hp
    · exact dvd_mul_of_dvd_left (primaryPrimeFactor_spec ha hp).2 b
    · exact dvd_mul_of_dvd_right (primaryPrimeFactor_spec hb hp).2 a

lemma norm_le_of_dvd_nonzero {a b : Eisenstein} (hb : b ≠ 0) (h : a ∣ b) : norm a ≤ norm b := by
  obtain ⟨c,rfl⟩ := h
  have hc : c ≠ 0 := by intro h; apply hb; rw [h,mul_zero]
  rw [norm_mul_eq]
  exact le_mul_of_one_le_right (norm_nonneg _) (one_le_norm hc)

lemma primarySquarefreeJoin_norm_le {a b : Eisenstein} (ha : primary a) (hb : primary b) :
    norm (primarySquarefreeJoin a b) ≤ norm a*norm b := by
  rw [← norm_mul_eq]
  exact norm_le_of_dvd_nonzero (mul_ne_zero (primary_ne_zero ha) (primary_ne_zero hb))
    (primarySquarefreeJoin_dvd_mul ha hb)

def collectedSquarefreeSieveCoefficient (C : Finset Eisenstein) (e : Eisenstein) : ℝ :=
  ∑ t ∈ (C.product C).filter (fun t => primarySquarefreeJoin t.1 t.2 = e),
    (idealMoebius t.1 : ℝ)*(idealMoebius t.2 : ℝ)

private lemma weighted_image_sum {ι κ : Type*} [DecidableEq κ]
    (S : Finset ι) (g : ι → κ) (v : ι → ℝ) (w : κ → ℝ) :
    (∑ t ∈ S, v t*w (g t)) =
      ∑ e ∈ S.image g, (∑ t ∈ S.filter (fun t => g t = e), v t)*w e := by
  have hf := Finset.sum_fiberwise_of_maps_to (s := S) (t := S.image g) (g := g)
    (fun t ht => Finset.mem_image_of_mem g ht) (fun t => v t*w (g t))
  rw [← hf]
  apply Finset.sum_congr rfl
  intro e he
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro t ht
  rw [(Finset.mem_filter.mp ht).2]

/-- The square of the truncated Möbius sum is exactly a finite divisor
sum with the collected coefficients. -/
theorem truncatedSquareDivisorSum_collected (C : Finset Eisenstein)
    (hC : ∀ c ∈ C, primary c ∧ Squarefree c) (n : Eisenstein) :
    (truncatedSquareDivisorSum C n)^2 =
      ∑ e ∈ (C.product C).image (fun t => primarySquarefreeJoin t.1 t.2),
        collectedSquarefreeSieveCoefficient C e * (if e^2 ∣ n then (1 : ℝ) else 0) := by
  rw [truncatedSquareDivisorSum_sq]
  calc
    _ = ∑ t ∈ C.product C, (idealMoebius t.1 : ℝ)*(idealMoebius t.2 : ℝ)*
        (if (primarySquarefreeJoin t.1 t.2)^2 ∣ n then (1 : ℝ) else 0) := by
      symm
      calc
        _ = ∑ a ∈ C, ∑ b ∈ C, (idealMoebius a : ℝ)*(idealMoebius b : ℝ)*
            (if (primarySquarefreeJoin a b)^2 ∣ n then (1 : ℝ) else 0) :=
          Finset.sum_product C C _
        _ = _ := by
          apply Finset.sum_congr rfl
          intro a ha
          apply Finset.sum_congr rfl
          intro b hb
          rw [primarySquarefreeJoin_sq_dvd_iff (hC a ha).1 (hC b hb).1 (hC a ha).2 (hC b hb).2]
          by_cases h : a^2 ∣ n ∧ b^2 ∣ n <;> simp [h]
    _ = _ := weighted_image_sum (C.product C)
      (fun t => primarySquarefreeJoin t.1 t.2)
      (fun t => (idealMoebius t.1 : ℝ)*(idealMoebius t.2 : ℝ))
      (fun e => if e^2 ∣ n then (1 : ℝ) else 0)

end CubicFirstMoment

end

end OAI
