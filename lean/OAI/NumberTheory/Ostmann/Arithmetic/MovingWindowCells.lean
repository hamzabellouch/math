import OAI.NumberTheory.Ostmann.Arithmetic.MovingScalarWindows
import OAI.NumberTheory.Ostmann.Arithmetic.MovingArithmeticCells

namespace OAI

/-! # Sharp terminal windows have explicit polynomial root cells -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def movingWindowPolynomials {σ : Type*} (value : σ → ℕ) {n : ℕ}
    (T : MovingSlotData σ n) (L R : Polynomial ℝ) (X lo hi : ℝ)
    (i : TreeLeafIndex n × Bool) : Polynomial ℝ :=
  if i.2 then Polynomial.C hi - movingLeafNormalizedPolynomial value T L R X i.1
  else movingLeafNormalizedPolynomial value T L R X i.1 - Polynomial.C lo

noncomputable def movingWindowRootCuts {σ : Type*} (value : σ → ℕ) {n : ℕ}
    (T : MovingSlotData σ n) (L R : Polynomial ℝ) (X lo hi : ℝ) : Finset ℝ :=
  polynomialRootCuts (movingWindowPolynomials value T L R X lo hi)

theorem movingWindowPolynomials_mem_iff {σ : Type*} (value : σ → ℕ) {n : ℕ}
    (T : MovingSlotData σ n) (L R : Polynomial ℝ) (X lo hi z : ℝ) :
    (∀ i, (movingLeafNormalizedPolynomial value T L R X i).eval z ∈ Set.Icc lo hi) ↔
      ∀ i, 0 ≤ (movingWindowPolynomials value T L R X lo hi i).eval z := by
  constructor
  · intro h i
    cases hb : i.2
    · simpa only [movingWindowPolynomials, hb, Bool.false_eq_true, ite_false,
        Polynomial.eval_sub, Polynomial.eval_C, sub_nonneg] using (h i.1).1
    · simpa only [movingWindowPolynomials, hb, ite_true,
        Polynomial.eval_sub, Polynomial.eval_C, sub_nonneg] using (h i.1).2
  · intro h i
    constructor
    · simpa only [movingWindowPolynomials, Bool.false_eq_true, ite_false,
        Polynomial.eval_sub, Polynomial.eval_C, sub_nonneg] using h (i, false)
    · simpa only [movingWindowPolynomials, ite_true,
        Polynomial.eval_sub, Polynomial.eval_C, sub_nonneg] using h (i, true)

theorem movingWindowRootCuts_card {σ : Type*} (value : σ → ℕ) {n : ℕ}
    (T : MovingSlotData σ n) (L R : Polynomial ℝ) (X lo hi : ℝ)
    (hL : L.natDegree ≤ 1) (hR : R.natDegree ≤ 1) :
    (movingWindowRootCuts value T L R X lo hi).card ≤ 4 * 2 ^ n := by
  have hp (i : TreeLeafIndex n) : (movingLeafNormalizedPolynomial value T L R X i).natDegree ≤ 2 := by
    apply Polynomial.natDegree_mul_le.trans
    simpa only [Polynomial.natDegree_C, zero_add, mul_one] using T.leafPolynomials_degree value L R 1 hL hR i
  have hdeg (i : TreeLeafIndex n × Bool) :
      (movingWindowPolynomials value T L R X lo hi i).natDegree ≤ 2 := by
    unfold movingWindowPolynomials
    split_ifs
    · exact (Polynomial.natDegree_sub_le _ _).trans (max_le (by simp) (hp i.1))
    · exact (Polynomial.natDegree_sub_le _ _).trans (max_le (hp i.1) (by simp))
  apply (polynomialRootCuts_card _).trans
  calc
    _ ≤ ∑ _i : TreeLeafIndex n × Bool, 2 := Finset.sum_le_sum (fun i _ => hdeg i)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod,
        Fintype.card_bool, card_treeLeafIndex, smul_eq_mul]; omega

theorem movingPolynomialWindows_of_rootCell {σ : Type*} (value : σ → ℕ) {n : ℕ}
    (T : MovingSlotData σ n) (L R : Polynomial ℝ) (X lo hi x y : ℝ)
    (S : Finset ℝ) (hS : movingWindowRootCuts value T L R X lo hi ⊆ S)
    (hcode : rootCellCode S x = rootCellCode S y) :
    (∀ i, (movingLeafNormalizedPolynomial value T L R X i).eval x ∈ Set.Icc lo hi) ↔
      (∀ i, (movingLeafNormalizedPolynomial value T L R X i).eval y ∈ Set.Icc lo hi) := by
  rw [movingWindowPolynomials_mem_iff, movingWindowPolynomials_mem_iff]
  apply forall_congr'
  intro i
  apply polynomial_nonneg_iff_of_root_cell _ S _ hcode
  intro r hr
  exact hS (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, Multiset.mem_toFinset.mpr hr⟩)

theorem movingNaturalWindows_of_rootCell {σ : Type*} (value : σ → ℕ)
    (hvalue : ∀ i, value i ≠ 0) {n : ℕ} (T : MovingSlotData σ n)
    (hf : T.Frequencies (· ≠ 0)) (XR XL YL : ℕ) (X lo hi : ℝ) (S : Finset ℝ)
    (hS : movingWindowRootCuts value T Polynomial.X (Polynomial.C XR) X lo hi ⊆ S)
    (hcode : rootCellCode S (XL : ℝ) = rootCellCode S (YL : ℝ))
    (hX : T.Integral value XL XR) (hY : T.Integral value YL XR) :
    (∀ i, (T.leafModuli value XL XR i : ℝ) / X ∈ Set.Icc lo hi) ↔
      (∀ i, (T.leafModuli value YL XR i : ℝ) / X ∈ Set.Icc lo hi) := by
  have h := movingPolynomialWindows_of_rootCell value T Polynomial.X (Polynomial.C XR)
    X lo hi XL YL S hS hcode
  have hx (i : TreeLeafIndex n) :
      (movingLeafNormalizedPolynomial value T Polynomial.X (Polynomial.C XR) X i).eval (XL : ℝ) =
        (T.leafModuli value XL XR i : ℝ) / X := by
    rw [movingLeafNormalizedPolynomial_eval, T.leafPolynomials_eval value hvalue hf XL XR hX
      _ _ _ (by simp) (by simp)]
  have hy (i : TreeLeafIndex n) :
      (movingLeafNormalizedPolynomial value T Polynomial.X (Polynomial.C XR) X i).eval (YL : ℝ) =
        (T.leafModuli value YL XR i : ℝ) / X := by
    rw [movingLeafNormalizedPolynomial_eval, T.leafPolynomials_eval value hvalue hf YL XR hY
      _ _ _ (by simp) (by simp)]
  simpa only [hx, hy] using h

end Ostmann

end OAI
