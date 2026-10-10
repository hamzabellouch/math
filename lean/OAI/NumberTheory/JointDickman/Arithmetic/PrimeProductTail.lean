import OAI.NumberTheory.JointDickman.Arithmetic.PrimeReciprocalInterval
import OAI.NumberTheory.JointDickman.Arithmetic.OrderedPrimeSubsets

namespace OAI

/-! # Reciprocal mass of prime products near a cutoff -/
namespace JointDickman
open Finset

/-- Fixing all but one prime leaves an interval of multiplicative width `N/Y`.
The bound is uniform in the product `r` of the fixed primes. -/
theorem prime_reciprocal_product_fiber : ∃ C : ℝ, 0 ≤ C ∧
    ∀ (P : Finset ℕ) (y Y N r : ℝ), 2 ≤ y → 0 < Y → Y ≤ N → 0 < r →
      (∀ p ∈ P, p.Prime ∧ y < (p:ℝ)) →
      (∑ p ∈ P.filter (fun p : ℕ => Y < r*(p:ℝ) ∧ r*(p:ℝ) ≤ N), 1/(p:ℝ)) ≤
        (Real.log (N/Y)+C)/Real.log y := by
  classical
  obtain ⟨C,hC,hbound⟩ := prime_reciprocal_interval_subset
  refine ⟨C,hC,?_⟩
  intro P y Y N r hy hY hYN hr hP
  have hN : 0 < N := hY.trans_le hYN
  have hR : 1 ≤ N/Y := (le_div_iff₀ hY).mpr (by simpa using hYN)
  have hL : 2 ≤ max y (Y/r) := hy.trans (le_max_left _ _)
  have hU : N/r ≤ (N/Y)*max y (Y/r) := by
    calc
      N/r = (N/Y)*(Y/r) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_max_right _ _) (div_nonneg hN.le hY.le)
  have hb := hbound (P.filter (fun p : ℕ => Y < r*(p:ℝ) ∧ r*(p:ℝ) ≤ N))
    (max y (Y/r)) (N/r) (N/Y) hL hR hU (by
      intro p hp
      obtain ⟨hp,hlo,hhi⟩ := mem_filter.mp hp
      refine ⟨(hP p hp).1,max_lt (hP p hp).2 ?_,?_⟩
      · exact (div_lt_iff₀ hr).mpr (by simpa [mul_comm] using hlo)
      · exact (le_div_iff₀ hr).mpr (by simpa [mul_comm] using hhi))
  apply hb.trans
  exact div_le_div_of_nonneg_left (add_nonneg (Real.log_nonneg hR) hC)
    (Real.log_pos (by linarith))
    (Real.log_le_log (by linarith) (le_max_left _ _))

noncomputable def reciprocalPrimeTupleTail (P : Finset ℕ) (h : ℕ) (Y N : ℝ) : ℝ := by
  classical
  exact ∑ v ∈ (Fintype.piFinset (fun _ : Fin h => P)).filter
    (fun v => Y < ∏ i, (v i:ℝ) ∧ (∏ i, (v i:ℝ)) ≤ N), 1/(∏ i, (v i:ℝ))

theorem reciprocalPrimeTupleTail_fibers (P : Finset ℕ) (h : ℕ) (Y N : ℝ) :
    reciprocalPrimeTupleTail P (h+1) Y N =
      ∑ v ∈ Fintype.piFinset (fun _ : Fin h => P),
        (1/(∏ i, (v i:ℝ))) *
          ∑ p ∈ P.filter (fun p : ℕ => Y < (∏ i, (v i:ℝ))*(p:ℝ) ∧
            (∏ i, (v i:ℝ))*(p:ℝ) ≤ N), 1/(p:ℝ) := by
  classical
  have he := filter_piFinset_eq_map_consEquiv
    (fun _ : Fin (h+1) => P) (fun _ => True)
  simp only [filter_true] at he
  rw [reciprocalPrimeTupleTail,sum_filter,he,sum_map,sum_product,sum_comm]
  apply sum_congr rfl
  intro v _
  rw [mul_sum,sum_filter]
  apply sum_congr rfl
  intro p _
  simp only [Function.Embedding.coeFn_mk, Fin.consEquiv_apply,
    Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
  rw [mul_comm (p:ℝ)]
  split_ifs <;> simp [div_mul_eq_div_mul_one_div, mul_comm]

/-- Repeated primes are allowed. Thus this also controls every fixed-cardinality
term of the squarefree divisor expansion. -/
theorem reciprocalPrimeTupleTail_bound : ∃ C : ℝ, 0 ≤ C ∧
    ∀ (P : Finset ℕ) (h : ℕ) (y Y N : ℝ), 2 ≤ y → 0 < Y → Y ≤ N →
      (∀ p ∈ P, p.Prime ∧ y < (p:ℝ)) →
      reciprocalPrimeTupleTail P (h+1) Y N ≤
        ((Real.log (N/Y)+C)/Real.log y)*(∑ p ∈ P, 1/(p:ℝ))^h := by
  classical
  obtain ⟨C,hC,hbound⟩ := prime_reciprocal_product_fiber
  refine ⟨C,hC,?_⟩
  intro P h y Y N hy hY hYN hP
  rw [reciprocalPrimeTupleTail_fibers]
  calc
    _ ≤ ∑ v ∈ Fintype.piFinset (fun _ : Fin h => P),
        (1/(∏ i, (v i:ℝ))) * ((Real.log (N/Y)+C)/Real.log y) := by
      apply sum_le_sum
      intro v hv
      have hprod : 0 < ∏ i, (v i:ℝ) := prod_pos (fun i _ => by
        have := (hP (v i) (Fintype.mem_piFinset.mp hv i)).2
        linarith)
      exact mul_le_mul_of_nonneg_left (hbound P y Y N _ hy hY hYN hprod hP)
        (by positivity)
    _ = _ := by
      rw [← sum_mul, sum_pow']
      have he : (∑ v ∈ Fintype.piFinset (fun _ : Fin h => P), 1/(∏ i, (v i:ℝ))) =
          ∑ v ∈ Fintype.piFinset (fun _ : Fin h => P), ∏ i, 1/(v i:ℝ) := by
        apply sum_congr rfl
        intro v _
        simp only [one_div,prod_inv_distrib]
      rw [he,mul_comm]

end JointDickman

end OAI
