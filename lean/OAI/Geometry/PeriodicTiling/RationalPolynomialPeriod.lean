import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Topology.Instances.AddCircle.Defs

namespace OAI

universe uι

noncomputable section

open scoped BigOperators

namespace PeriodicTilingThree

private theorem finite_common_denominator {ι : Type uι} (s : Finset ι) (c : ι → ℝ)
    (hc : ∀ i ∈ s, ∃ q : ℚ, c i = (q : ℝ)) :
    ∃ a : ℕ, 0 < a ∧ ∀ i ∈ s, ∃ z : ℤ, c i * (a : ℝ) = (z : ℝ) := by
  classical
  let q : s → ℚ := fun i => Classical.choose (hc i.1 i.2)
  have hq : ∀ i : s, c i.1 = (q i : ℝ) := fun i => Classical.choose_spec (hc i.1 i.2)
  let a : ℕ := ∏ i : s, (q i).den
  refine ⟨a, Finset.prod_pos (fun i _ => (q i).den_pos), ?_⟩
  intro i hi
  let j : s := ⟨i, hi⟩
  have hj : (q j).den ∣ a := Finset.dvd_prod_of_mem _ (Finset.mem_univ j)
  obtain ⟨b, hb⟩ := hj
  refine ⟨(q j).num * (b : ℤ), ?_⟩
  have hiq : c i = (q j : ℝ) := hq j
  have hden : ((q j).den : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (q j).den_ne_zero
  rw [hiq, hb, Nat.cast_mul, ← mul_assoc, Rat.cast_def,
    div_mul_cancel₀ _ hden,
    Int.cast_mul, Int.cast_natCast]

private theorem circle_eval_eq_sum (P : Polynomial ℝ) (x : ℝ) :
    ((P.eval x : ℝ) : AddCircle (1 : ℝ)) =
      ∑ i ∈ P.support, ((P.coeff i * x ^ i : ℝ) : AddCircle (1 : ℝ)) := by
  change (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℝ))) (P.eval x) = _
  rw [Polynomial.eval_eq_sum, Polynomial.sum_def, map_sum]
  simp only [QuotientAddGroup.mk'_apply]

private theorem circle_monomial_add_period (c : ℝ) (a : ℕ) (z : ℤ)
    (hc : c * (a : ℝ) = (z : ℝ)) (i : ℕ) (n : ℤ) :
    ((c * ((n + (a : ℤ) : ℤ) : ℝ) ^ i : ℝ) : AddCircle (1 : ℝ)) =
      ((c * (n : ℝ) ^ i : ℝ) : AddCircle (1 : ℝ)) := by
  apply sub_eq_zero.mp
  rw [← AddCircle.coe_sub]
  apply (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr
  have hdiv : (a : ℤ) ∣ (n + (a : ℤ)) ^ i - n ^ i := by
    simpa using sub_dvd_pow_sub_pow (n + (a : ℤ)) n i
  obtain ⟨k, hk⟩ := hdiv
  refine ⟨z * k, ?_⟩
  have hk' : (((n + (a : ℤ) : ℤ) : ℝ) ^ i - (n : ℝ) ^ i) =
      (a : ℝ) * (k : ℝ) := by
    exact_mod_cast hk
  rw [← mul_sub, hk', ← mul_assoc, hc]
  simp only [zsmul_eq_mul, mul_one, Int.cast_mul]

theorem rational_nonconstant_circlePolynomial_periodic (P : Polynomial ℝ)
    (hP : ∀ i : ℕ, 0 < i → ∃ q : ℚ, P.coeff i = (q : ℝ)) :
    ∃ q : ℕ, 0 < q ∧ ∀ n : ℤ,
      ((P.eval ((n + (q : ℤ) : ℤ) : ℝ) : ℝ) : AddCircle (1 : ℝ)) =
        ((P.eval (n : ℝ) : ℝ) : AddCircle (1 : ℝ)) := by
  classical
  obtain ⟨a, ha, hcoeff⟩ := finite_common_denominator (P.support.erase 0) P.coeff
    (fun i hi => hP i (Nat.pos_of_ne_zero (Finset.mem_erase.mp hi).1))
  refine ⟨a, ha, ?_⟩
  intro n
  rw [circle_eval_eq_sum, circle_eval_eq_sum]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hi0 : i = 0
  · simp only [hi0, pow_zero, mul_one]
  · obtain ⟨z, hz⟩ := hcoeff i (Finset.mem_erase.mpr ⟨hi0, hi⟩)
    exact circle_monomial_add_period (P.coeff i) a z hz i n

private theorem circle_monomial_scaled_eq_zero (c : ℝ) (a : ℕ) (z : ℤ)
    (hc : c * (a : ℝ) = (z : ℝ)) (i : ℕ) (hi : 0 < i) (n : ℕ) :
    ((c * ((a * n : ℕ) : ℝ) ^ i : ℝ) : AddCircle (1 : ℝ)) = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi.ne'
  apply (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr
  refine ⟨z * (a : ℤ) ^ k * (n : ℤ) ^ (k + 1), ?_⟩
  have hmul : c * ((a * n : ℕ) : ℝ) ^ (k + 1) =
      (z : ℝ) * (a : ℝ) ^ k * (n : ℝ) ^ (k + 1) := by
    calc
      _ = (c * (a : ℝ)) * ((a : ℝ) ^ k * (n : ℝ) ^ (k + 1)) := by
        rw [Nat.cast_mul, mul_pow, pow_succ]
        ring
      _ = _ := by rw [hc]; ring
  simpa only [zsmul_eq_mul, mul_one, Int.cast_mul, Int.cast_pow, Int.cast_natCast]
    using hmul.symm

theorem exists_progression_irrational_leadingCoeff (P : Polynomial ℝ)
    (hP : ∃ i : ℕ, 0 < i ∧ Irrational (P.coeff i)) :
    ∃ a : ℕ, 0 < a ∧ ∃ Q : Polynomial ℝ,
      0 < Q.natDegree ∧ Irrational Q.leadingCoeff ∧ ∀ n : ℕ,
        ((P.eval ((a * n : ℕ) : ℝ) : ℝ) : AddCircle (1 : ℝ)) =
          ((Q.eval (n : ℝ) : ℝ) : AddCircle (1 : ℝ)) := by
  classical
  let s := P.support.filter fun i => 0 < i ∧ Irrational (P.coeff i)
  have hs : s.Nonempty := by
    obtain ⟨i, hi, hirr⟩ := hP
    exact ⟨i, Finset.mem_filter.mpr ⟨Polynomial.mem_support_iff.mpr hirr.ne_zero, hi, hirr⟩⟩
  let d := s.max' hs
  have hdmem : d ∈ s := Finset.max'_mem s hs
  have hdpos : 0 < d := (Finset.mem_filter.mp hdmem).2.1
  have hdirr : Irrational (P.coeff d) := (Finset.mem_filter.mp hdmem).2.2
  have hrat : ∀ j : ℕ, d < j → ∃ q : ℚ, P.coeff j = (q : ℝ) := by
    intro j hj
    have hnot : ¬ Irrational (P.coeff j) := by
      intro hirr
      have hjmem : j ∈ s := Finset.mem_filter.mpr
        ⟨Polynomial.mem_support_iff.mpr hirr.ne_zero, hdpos.trans hj, hirr⟩
      exact (not_le_of_gt hj) (Finset.le_max' s j hjmem)
    simpa only [Irrational, Set.mem_range, not_not, eq_comm] using hnot
  obtain ⟨a, ha, hcoeff⟩ :=
    finite_common_denominator (P.support.filter fun i => d < i) P.coeff
      (fun i hi => hrat i (Finset.mem_filter.mp hi).2)
  let t := P.support.filter fun i => i ≤ d
  let Q : Polynomial ℝ :=
    ∑ i ∈ t, Polynomial.monomial i (P.coeff i * (a : ℝ) ^ i)
  have hQcoeff : ∀ j : ℕ, Q.coeff j =
      if j ∈ t then P.coeff j * (a : ℝ) ^ j else 0 := by
    intro j
    simp only [Q, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial,
      Finset.sum_ite_eq']
  have hdmemt : d ∈ t := Finset.mem_filter.mpr
    ⟨Polynomial.mem_support_iff.mpr hdirr.ne_zero, le_rfl⟩
  have hQirr : Irrational (Q.coeff d) := by
    rw [hQcoeff, ite_eq_left hdmemt]
    simpa only [Nat.cast_pow] using hdirr.mul_natCast (pow_ne_zero d ha.ne')
  have hQdeg : Q.natDegree = d := by
    apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero _ hQirr.ne_zero
    apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    intro j hj
    rw [hQcoeff, ite_eq_right]
    intro hjmem
    exact (not_le_of_gt hj) (Finset.mem_filter.mp hjmem).2
  refine ⟨a, ha, Q, hQdeg.symm ▸ hdpos, ?_, ?_⟩
  · simpa only [Polynomial.leadingCoeff, hQdeg] using hQirr
  · intro n
    have hQeval : ((Q.eval (n : ℝ) : ℝ) : AddCircle (1 : ℝ)) =
        ∑ i ∈ t, ((P.coeff i * ((a * n : ℕ) : ℝ) ^ i : ℝ) : AddCircle (1 : ℝ)) := by
      simp only [Q, Polynomial.eval_finsetSum, Polynomial.eval_monomial]
      change (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℝ)))
        (∑ i ∈ t, (P.coeff i * (a : ℝ) ^ i) * (n : ℝ) ^ i) = _
      rw [map_sum]
      simp only [QuotientAddGroup.mk'_apply]
      apply Finset.sum_congr rfl
      intro i hi
      congr 1
      rw [Nat.cast_mul, mul_pow]
      ring
    rw [circle_eval_eq_sum, hQeval]
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro i hi hit
    have hdi : d < i := lt_of_not_ge fun hid =>
      hit (Finset.mem_filter.mpr ⟨hi, hid⟩)
    obtain ⟨z, hz⟩ := hcoeff i (Finset.mem_filter.mpr ⟨hi, hdi⟩)
    exact circle_monomial_scaled_eq_zero (P.coeff i) a z hz i (hdpos.trans hdi) n

end PeriodicTilingThree

end

end OAI
