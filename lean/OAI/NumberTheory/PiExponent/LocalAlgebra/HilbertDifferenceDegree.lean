import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Tactic

namespace OAI

namespace PiExponentJets.W27
open Polynomial

theorem difference_taylor_coefficient (p : Polynomial ℚ) (s : ℕ)
    (hp : p.natDegree = s+1) (a : ℚ) :
    (p - Polynomial.taylor a p).coeff s = -a * (s+1 : ℚ) * p.leadingCoeff := by
  have hd : (Polynomial.hasseDeriv s p).natDegree ≤ 1 := by
    simpa [hp] using Polynomial.natDegree_hasseDeriv_le p s
  have hlin := Polynomial.eq_X_add_C_of_natDegree_le_one hd
  have h0 : (Polynomial.hasseDeriv s p).coeff 0 = p.coeff s := by
    simp [Polynomial.hasseDeriv_coeff]
  have h1 : (Polynomial.hasseDeriv s p).coeff 1 = (s+1 : ℚ) * p.leadingCoeff := by
    rw [Polynomial.hasseDeriv_coeff]
    simp only [Nat.add_comm 1 s, Nat.choose_succ_self_right, Nat.cast_add, Nat.cast_one]
    rw [← hp, Polynomial.coeff_natDegree]
  rw [Polynomial.coeff_sub, Polynomial.taylor_coeff, hlin]
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
  rw [h0, h1]
  ring

theorem difference_taylor_natDegree_le (p : Polynomial ℚ) (s : ℕ)
    (hp : p.natDegree = s+1) (a : ℚ) :
    (p - Polynomial.taylor a p).natDegree ≤ s := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro n hn
  rw [Polynomial.coeff_sub]
  by_cases he : n = s+1
  · subst n
    rw [← hp, Polynomial.coeff_natDegree, Polynomial.coeff_taylor_natDegree, sub_self]
  · have hlt : p.natDegree < n := by omega
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt hlt,
      Polynomial.coeff_eq_zero_of_natDegree_lt (by simpa using hlt), sub_self]

theorem backward_difference_degree_and_leading
    (p : Polynomial ℚ) (s : ℕ) (hp : p.natDegree = s+1)
    (d : ℚ) (hd : d ≠ 0) :
    (p - Polynomial.taylor (-d) p).natDegree = s ∧
      (p - Polynomial.taylor (-d) p).leadingCoeff = d * (s+1 : ℚ) * p.leadingCoeff := by
  have hp0 : p ≠ 0 := by
    intro hz
    simp [hz] at hp
  have hs : (s+1 : ℚ) ≠ 0 := by positivity
  have hc : (p - Polynomial.taylor (-d) p).coeff s =
      d * (s+1 : ℚ) * p.leadingCoeff := by
    simpa using difference_taylor_coefficient p s hp (-d)
  have hcn : (p - Polynomial.taylor (-d) p).coeff s ≠ 0 := by
    rw [hc]
    exact mul_ne_zero (mul_ne_zero hd hs) (Polynomial.leadingCoeff_ne_zero.mpr hp0)
  have hdeg := Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
    (difference_taylor_natDegree_le p s hp (-d)) hcn
  refine ⟨hdeg, ?_⟩
  simpa only [Polynomial.leadingCoeff, hdeg] using hc

theorem backward_difference_multiplicity
    (p : Polynomial ℚ) (s : ℕ) (hp : p.natDegree = s+1)
    (d : ℚ) (hd : d ≠ 0) :
    (p - Polynomial.taylor (-d) p).leadingCoeff *
        ((p - Polynomial.taylor (-d) p).natDegree.factorial : ℚ) =
      d * (p.leadingCoeff * (p.natDegree.factorial : ℚ)) := by
  obtain ⟨hdeg, hl⟩ := backward_difference_degree_and_leading p s hp d hd
  rw [hl, hdeg, hp, Nat.factorial_succ]
  push_cast
  ring

theorem backward_difference_eq_comp (p : Polynomial ℚ) (d : ℚ) :
    p - Polynomial.taylor (-d) p = p - p.comp (Polynomial.X - Polynomial.C d) := by
  simp only [Polynomial.taylor_apply, Polynomial.C_neg, sub_eq_add_neg]

end PiExponentJets.W27

end OAI
