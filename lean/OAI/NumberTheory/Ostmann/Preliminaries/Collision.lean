import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

namespace OAI

/-!
# Elementary collision estimates

These are the finite probability and support-size inequalities used in §2
and in the final collision argument of §3. No analytic estimate is assumed.
-/

namespace Ostmann

open scoped BigOperators

/-- Cauchy--Schwarz bounds the collision probability of a unit mass on a
finite nonempty support by the reciprocal of the support's size. -/
theorem inverse_card_le_collision {α : Type*} (s : Finset α) (μ : α → ℝ)
    (hs : s.Nonempty) (hmass : ∑ x ∈ s, μ x = 1) :
    1 / (s.card : ℝ) ≤ ∑ x ∈ s, μ x ^ 2 := by
  have hc : (0 : ℝ) < s.card := by exact_mod_cast hs.card_pos
  apply (div_le_iff₀ hc).mpr
  have h := sq_sum_le_card_mul_sum_sq (s := s) (f := μ)
  rw [hmass, one_pow] at h
  simpa only [mul_comm] using h

/-- Exact squared distance from uniform probability on a finite support. -/
theorem collision_sub_uniform {α : Type*} (s : Finset α) (μ : α → ℝ)
    (hs : s.Nonempty) (hmass : ∑ x ∈ s, μ x = 1) :
    ∑ x ∈ s, (μ x - 1 / (s.card : ℝ)) ^ 2 =
      (∑ x ∈ s, μ x ^ 2) - 1 / (s.card : ℝ) := by
  have hc : (s.card : ℝ) ≠ 0 := by exact_mod_cast hs.card_ne_zero
  calc
    ∑ x ∈ s, (μ x - 1 / (s.card : ℝ)) ^ 2 =
        ∑ x ∈ s, (μ x ^ 2 - (2 / (s.card : ℝ)) * μ x +
          (1 / (s.card : ℝ)) ^ 2) := by
      apply Finset.sum_congr rfl
      intro x hx
      ring
    _ = (∑ x ∈ s, μ x ^ 2) -
          2 * (∑ x ∈ s, μ x) / (s.card : ℝ) +
          (s.card : ℝ) * (1 / (s.card : ℝ)) ^ 2 := by
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
      simp only [Finset.sum_const, nsmul_eq_mul]
      ring
    _ = _ := by rw [hmass]; field_simp; ring

/-- Disjoint nonempty supports occupying at most `p` residues have combined
collision probability at least `4 / p`. -/
theorem four_div_le_inverse_add_inverse {a b p : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hab : a + b ≤ p) :
    4 / p ≤ 1 / a + 1 / b := by
  have hp : 0 < p := lt_of_lt_of_le (add_pos ha hb) hab
  have habpos : 0 < a * b := mul_pos ha hb
  have hnum : 4 * (a * b) ≤ p * (a + b) := by
    nlinarith [sq_nonneg (a - b), mul_nonneg (le_of_lt (add_pos ha hb)) (sub_nonneg.mpr hab)]
  apply (div_le_iff₀ hp).mpr
  have hratio : 4 ≤ (p * (a + b)) / (a * b) := (le_div_iff₀ habpos).mpr hnum
  calc
    4 ≤ p * (a + b) / (a * b) := hratio
    _ = (1 / a + 1 / b) * p := by field_simp; ring

/-- The combined collision lower bound on disjoint residue supports, as used
at the split primes in the last paragraph of §3. -/
theorem collision_lower_bound_disjoint {α : Type*} [Fintype α]
    (s t : Finset α) (μ ν : α → ℝ)
    (hs : s.Nonempty) (ht : t.Nonempty) (hst : Disjoint s t)
    (hμ : ∑ x ∈ s, μ x = 1) (hν : ∑ x ∈ t, ν x = 1) :
    4 / (Fintype.card α : ℝ) ≤
      (∑ x ∈ s, μ x ^ 2) + ∑ x ∈ t, ν x ^ 2 := by
  classical
  have hcard : s.card + t.card ≤ Fintype.card α := by
    rw [← Finset.card_union_of_disjoint hst]
    exact Finset.card_le_univ _
  have hspos : (0 : ℝ) < s.card := by exact_mod_cast hs.card_pos
  have htpos : (0 : ℝ) < t.card := by exact_mod_cast ht.card_pos
  have hcard' : (s.card : ℝ) + t.card ≤ Fintype.card α := by exact_mod_cast hcard
  exact (four_div_le_inverse_add_inverse hspos htpos hcard').trans
    (add_le_add (inverse_card_le_collision s μ hs hμ) (inverse_card_le_collision t ν ht hν))

end Ostmann

end OAI
