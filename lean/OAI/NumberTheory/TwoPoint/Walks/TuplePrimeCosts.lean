import OAI.NumberTheory.TwoPoint.Bounds.PrimeTuplePool

namespace OAI

/-! First moments of additive prime costs for the actual disjoint-band tuple
family. Large band masses dilute any fixed summable prime defect. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma tuple_coordinate_cost_sum {J : ℕ} (P : Fin J → Finset ℕ)
    (c : ℕ → ℝ) (i : Fin J) :
    (∑ x : (j : Fin J) → P j,
      (∏ j, 1 / ((x j).val : ℝ)) * c (x i).val) =
      (∑ p ∈ P i, c p / (p : ℝ)) *
        ∏ j ∈ (univ : Finset (Fin J)).erase i, primeHarmonicMass (P j) := by
  have he (x : (j : Fin J) → P j) :
      (∏ j, 1 / ((x j).val : ℝ)) * c (x i).val =
        ∏ j, if j = i then (1 / ((x j).val : ℝ)) * c (x j).val
          else 1 / ((x j).val : ℝ) := by
    rw [← mul_prod_erase univ _ (mem_univ i),
      ← mul_prod_erase univ _ (mem_univ i)]
    simp only [ite_true]
    have ht : (∏ j ∈ (univ : Finset (Fin J)).erase i,
        if j = i then (1 / ((x j).val : ℝ)) * c (x j).val
          else 1 / ((x j).val : ℝ)) =
        ∏ j ∈ (univ : Finset (Fin J)).erase i, 1 / ((x j).val : ℝ) := by
      apply prod_congr rfl
      intro j hj
      rw [ite_eq_right (mem_erase.mp hj).1]
    rw [ht]
    ring
  simp_rw [he]
  rw [← Fintype.prod_sum (fun (j : Fin J) (p : P j) =>
    if j = i then (1 / (p.val : ℝ)) * c p.val else 1 / (p.val : ℝ)),
    ← mul_prod_erase univ _ (mem_univ i)]
  congr 1
  · simp only [ite_true]
    rw [← sum_coe_sort (P i)]
    apply sum_congr rfl
    intro p _
    ring
  · apply prod_congr rfl
    intro j hj
    simp only [ite_eq_right (mem_erase.mp hj).1, primeHarmonicMass, one_div]

lemma primeTupleDivisors_cost_sum {J : ℕ} (P : Fin J → Finset ℕ)
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j k, k ≠ j → Disjoint (P j) (P k)) (c : ℕ → ℝ) :
    (∑ d ∈ primeTupleDivisors P, (1 / (d : ℝ)) * ∑ p ∈ d.primeFactors, c p) =
      ∑ i : Fin J, (∑ p ∈ P i, c p / (p : ℝ)) *
        ∏ j ∈ (univ : Finset (Fin J)).erase i, primeHarmonicMass (P j) := by
  rw [primeTupleDivisors, sum_image]
  · have he (x : (j : Fin J) → P j) :
        (1 / ((∏ j, (x j).val : ℕ) : ℝ)) *
            (∑ p ∈ (∏ j, (x j).val).primeFactors, c p) =
          ∑ i : Fin J, (∏ j, 1 / ((x j).val : ℝ)) * c (x i).val := by
      have hf : (∏ j, (x j).val).primeFactors = univ.image (fun j => (x j).val) :=
        familyTuple_primeFactors (fun j (p : P j) => p.val)
          (fun j p => hprime j _ p.property) x (selectedPrimeValues_injective x hdisjoint)
      rw [hf, sum_image]
      · simp only [Nat.cast_prod, one_div, prod_inv_distrib, mul_sum]
      · exact fun j _ k _ he => selectedPrimeValues_injective x hdisjoint he
    simp_rw [he]
    rw [sum_comm]
    apply sum_congr rfl
    intro i _
    exact tuple_coordinate_cost_sum P c i
  · exact fun x _ y _ he => primeTuple_injective hprime hdisjoint he

lemma primeTupleDivisors_cost_bound {J : ℕ} (P : Fin J → Finset ℕ)
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j k, k ≠ j → Disjoint (P j) (P k))
    (c : ℕ → ℝ) (hc : ∀ p ∈ primeTuplePool P, 0 ≤ c p)
    (W : ℝ) (hW : 0 < W) (hmass : ∀ j, W ≤ primeHarmonicMass (P j)) :
    (∑ d ∈ primeTupleDivisors P, (1 / (d : ℝ)) * ∑ p ∈ d.primeFactors, c p) ≤
      ((∏ j, primeHarmonicMass (P j)) / W) *
        ∑ p ∈ primeTuplePool P, c p / (p : ℝ) := by
  rw [primeTupleDivisors_cost_sum P hprime hdisjoint]
  have hpool : (∑ p ∈ primeTuplePool P, c p / (p : ℝ)) =
      ∑ j : Fin J, ∑ p ∈ P j, c p / (p : ℝ) := by
    unfold primeTuplePool
    apply sum_biUnion
    intro i _ j _ hij
    exact hdisjoint i j hij.symm
  rw [hpool, mul_sum]
  apply sum_le_sum
  intro i _
  have hprod0 : 0 ≤ ∏ j ∈ (univ : Finset (Fin J)).erase i,
      primeHarmonicMass (P j) := prod_nonneg (fun j _ => (hW.trans_le (hmass j)).le)
  have hprod : (∏ j ∈ (univ : Finset (Fin J)).erase i, primeHarmonicMass (P j)) ≤
      (∏ j, primeHarmonicMass (P j)) / W := by
    apply (le_div_iff₀ hW).mpr
    rw [← mul_prod_erase univ _ (mem_univ i)]
    nlinarith [mul_le_mul_of_nonneg_right (hmass i) hprod0]
  have hcost : 0 ≤ ∑ p ∈ P i, c p / (p : ℝ) := by
    apply sum_nonneg
    intro p hp
    exact div_nonneg (hc p (mem_primeTuplePool.mpr ⟨i, hp⟩)) (Nat.cast_nonneg _)
  exact (mul_le_mul_of_nonneg_left hprod hcost).trans_eq (mul_comm _ _)

end TwoPointCorrelations

end OAI
