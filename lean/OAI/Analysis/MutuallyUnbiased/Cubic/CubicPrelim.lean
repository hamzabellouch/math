import Mathlib.RingTheory.Polynomial.Vieta
import OAI.Analysis.MutuallyUnbiased.Cubic.CubicSymmetric

namespace OAI

/-! Characteristic-polynomial reduction for the cubic classification in §3. -/

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

theorem characteristic_polynomial_expansion (v : (Fin 6) → ℂ) :
    (∏ i, (Polynomial.X - Polynomial.C (v i))) =
      ∑ j ∈ Finset.range 7,
        (-1 : Polynomial ℂ) ^ j *
          (Polynomial.C (elementarySum v j) * Polynomial.X ^ (6 - j)) := by
  have h := Multiset.prod_X_sub_X_eq_sum_esymm
    ((Finset.univ : Finset (Fin 6)).val.map v)
  simpa only [Multiset.map_map, Function.comp_def, Finset.prod_map_val,
    Finset.esymm_map_val, Multiset.card_map, Finset.card_val, Finset.card_univ,
    Fintype.card_fin, elementarySum] using h

/-- Unit entries with first and second power sums zero have a characteristic
polynomial depending only on `X³`, as used at the start of cubic classification. -/
theorem characteristic_polynomial_in_cubes (v : (Fin 6) → ℂ)
    (hv : ∀ i, Complex.normSq (v i) = 1)
    (h1 : ∑ i, v i = 0) (h2 : ∑ i, v i ^ 2 = 0) :
    (∏ i, (Polynomial.X - Polynomial.C (v i))) =
      Polynomial.X ^ 6 - Polynomial.C (elementarySum v 3) * Polynomial.X ^ 3 +
        Polynomial.C (∏ i, v i) := by
  obtain ⟨he1, he2⟩ := elementarySum_one_two_zero v h1 h2
  obtain ⟨he4, he5⟩ := elementarySum_four_five_zero v hv h1 h2
  rw [characteristic_polynomial_expansion]
  simp [Finset.sum_range_succ, elementarySum_zero, elementarySum_six,
    he1, he2, he4, he5]
  ring

theorem cubed_entry_quadratic (v : (Fin 6) → ℂ)
    (hv : ∀ i, Complex.normSq (v i) = 1)
    (h1 : ∑ i, v i = 0) (h2 : ∑ i, v i ^ 2 = 0) (i : (Fin 6)) :
    (v i ^ 3) ^ 2 - elementarySum v 3 * v i ^ 3 + (∏ j, v j) = 0 := by
  have h := congrArg (Polynomial.eval (v i))
    (characteristic_polynomial_in_cubes v hv h1 h2)
  simp only [Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X,
    Polynomial.eval_C, Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_mul] at h
  have hz : (∏ j, (v i - v j)) = 0 :=
    Finset.prod_eq_zero (Finset.mem_univ i) (sub_self (v i))
  rw [hz] at h
  calc
    (v i ^ 3) ^ 2 - elementarySum v 3 * v i ^ 3 + (∏ j, v j) =
        v i ^ 6 - elementarySum v 3 * v i ^ 3 + (∏ j, v j) := by ring
    _ = 0 := h.symm

theorem quadratic_two_values {a b c s p : ℂ}
    (ha : a ^ 2 - s * a + p = 0) (hb : b ^ 2 - s * b + p = 0)
    (hc : c ^ 2 - s * c + p = 0) (hab : a ≠ b) : c = a ∨ c = b := by
  have hprod : (a - b) * (a + b - s) = 0 := by linear_combination ha - hb
  have hsum : a + b - s = 0 :=
    (mul_eq_zero.mp hprod).resolve_left (sub_ne_zero.mpr hab)
  have hs : s = a + b := by linear_combination -hsum
  have hp : p = a * b := by rw [hs] at ha; linear_combination ha
  rw [hs, hp] at hc
  have hfactor : (c - a) * (c - b) = 0 := by linear_combination hc
  simpa only [sub_eq_zero] using (mul_eq_zero.mp hfactor)

/-- This gives the first, algebraic part of the two-triples conclusion.
The multiplicity statement is a separate obligation. -/
theorem cube_values_at_most_two (v : (Fin 6) → ℂ)
    (hv : ∀ i, Complex.normSq (v i) = 1)
    (h1 : ∑ i, v i = 0) (h2 : ∑ i, v i ^ 2 = 0) :
    ∃ a b : ℂ, ∀ i, v i ^ 3 = a ∨ v i ^ 3 = b := by
  classical
  by_cases h : ∀ i, v i ^ 3 = v 0 ^ 3
  · exact ⟨v 0 ^ 3, v 0 ^ 3, fun i => Or.inl (h i)⟩
  · obtain ⟨j, hj⟩ := not_forall.mp h
    refine ⟨v 0 ^ 3, v j ^ 3, fun i => ?_⟩
    exact quadratic_two_values
      (cubed_entry_quadratic v hv h1 h2 0)
      (cubed_entry_quadratic v hv h1 h2 j)
      (cubed_entry_quadratic v hv h1 h2 i) (Ne.symm hj)

end MUB6

end

end OAI
