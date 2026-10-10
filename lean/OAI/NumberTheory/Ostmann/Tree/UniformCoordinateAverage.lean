import Mathlib.Logic.Equiv.Prod
import OAI.NumberTheory.Ostmann.Arithmetic.CRTLineAverage

namespace OAI

/-! # Coordinate marginals of the finite uniform CRT product -/

namespace Ostmann
open scoped BigOperators Classical

theorem uniform_pi_coordinate_average {I : Type*} [Fintype I] [DecidableEq I]
    (X : I → Type*) [∀ i, Fintype (X i)] [∀ i, Nonempty (X i)] (i : I)
    (f : X i → ℝ) :
    (Fintype.card (∀ j, X j) : ℝ)⁻¹ * (∑ x : ∀ j, X j, f (x i)) =
      (Fintype.card (X i) : ℝ)⁻¹ * ∑ x : X i, f x := by
  let e := Equiv.piSplitAt i X
  have hs := e.symm.sum_comp (fun x : ∀ j, X j => f (x i))
  have hc := Fintype.card_congr e
  have hn : (Fintype.card (∀ j : {j // j ≠ i}, X j) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  rw [← hs, hc, Fintype.card_prod, Nat.cast_mul, Fintype.sum_prod_type]
  simp only [e, Equiv.piSplitAt, Equiv.coe_fn_mk, Equiv.symm_mk]
  simp only [dite_true, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← Finset.mul_sum]
  field_simp

end Ostmann

end OAI
