import OAI.MathematicalPhysics.DefocusingNLS.Certificates.SeparatorPolynomials

namespace OAI

/-! # Degree bounds for the zero-tail matching polynomial -/

open Polynomial

namespace DefocusingNLS.SeparatorArithmetic

theorem length_addCoefficients (xs ys : List GaussianInt) :
    (addCoefficients xs ys).length = max xs.length ys.length := by
  induction xs generalizing ys with
  | nil => simp [addCoefficients]
  | cons x xs ih =>
    cases ys with
    | nil => simp [addCoefficients]
    | cons y ys => simp [addCoefficients, ih, Nat.succ_max_succ]

theorem length_mulLinear (a : GaussianInt) (xs : List GaussianInt) :
    (mulLinear a xs).length = xs.length + 1 := by
  simp [mulLinear, length_addCoefficients, scaleCoefficients]

theorem backwardStep_lengths (ℓ n k : ℕ) (xy : List GaussianInt × List GaussianInt)
    (hx : xy.1.length = k) (hy : xy.2.length = k + 1) :
    (backwardStep ℓ n xy).1.length = k + 1 ∧
      (backwardStep ℓ n xy).2.length = k + 2 := by
  simp only [backwardStep, length_addCoefficients, length_mulLinear,
    scaleCoefficients, List.length_map, hx, hy, max_self]
  simp [Nat.add_assoc]

theorem backward_fold_lengths (ℓ : ℕ) (ns : List ℕ)
    (xy : List GaussianInt × List GaussianInt) (k : ℕ)
    (hx : xy.1.length = k) (hy : xy.2.length = k + 1) :
    (ns.foldl (fun xy n => backwardStep ℓ n xy) xy).1.length = k + ns.length ∧
      (ns.foldl (fun xy n => backwardStep ℓ n xy) xy).2.length = k + ns.length + 1 := by
  induction ns generalizing xy k with
  | nil => simp [hx, hy]
  | cons n ns ih =>
    have h := backwardStep_lengths ℓ n k xy hx hy
    simpa only [List.foldl_cons, List.length_cons, Nat.add_assoc, Nat.add_left_comm,
      Nat.add_comm] using ih (backwardStep ℓ n xy) (k + 1) h.1 h.2

theorem backwardCoefficients_lengths (ℓ : ℕ) :
    (backwardCoefficients ℓ).1.length = 8 ∧
      (backwardCoefficients ℓ).2.length = 9 := by
  exact backward_fold_lengths ℓ [7, 6, 5, 4, 3, 2, 1, 0] ([], [1]) 0 rfl rfl

theorem toPolynomial_natDegree_le (xs : List GaussianInt) (n : ℕ)
    (h : xs.length ≤ n + 1) : (toPolynomial xs).natDegree ≤ n := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro j hj
  rw [coeff_toPolynomial, List.getElem?_eq_none (by omega)]
  rfl

theorem backward_polynomial_product_degree (ℓ : ℕ) :
    (toPolynomial (backwardCoefficients ℓ).1 *
      (toPolynomial (backwardCoefficients ℓ).2).map (starRingEnd GaussianInt)).natDegree ≤ 15 := by
  have h := backwardCoefficients_lengths ℓ
  exact natDegree_mul_le.trans (add_le_add
    (toPolynomial_natDegree_le _ 7 (by omega))
    (natDegree_map_le.trans (toPolynomial_natDegree_le _ 8 (by omega))))

theorem windingCoefficient_eq_zero (ℓ j : ℕ) (hj : 15 < j) :
    windingCoefficient ℓ j = 0 := by
  rw [windingCoefficient_eq,
    coeff_eq_zero_of_natDegree_lt ((backward_polynomial_product_degree ℓ).trans_lt hj)]
  rfl

end DefocusingNLS.SeparatorArithmetic

end OAI
