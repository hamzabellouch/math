import OAI.NumberTheory.TwoPoint.Bounds.IntegerEdges

namespace OAI

/-! Derivation of the weighted row estimate for the concrete integer graph. -/

namespace TwoPointCorrelations

open Finset

variable (Q : Finset ℕ) (u : ℕ → ℝ) (eligible : ℕ → Prop)
  (g center : ℤ → ℝ) (L K : ℝ) (extra : ℤ → Prop) (h d : ℕ)

lemma directedIntegerEdge_forward_bound
    (hL : 0 ≤ L) (hu : ∀ q ∈ Q, 0 ≤ u q) (hg : ∀ n, 0 < g n)
    (q : ℕ) (hq : q ∈ Q) (n m : ℤ) :
    |directedIntegerEdge Q u eligible g center L K extra h d q n m| * g m / g n ≤
      if m = n + (h * q * d : ℕ) then
        |center n| * retainedPaddingAtom Q u eligible g L K extra n q else 0 := by
  classical
  unfold directedIntegerEdge
  by_cases he : q ∈ Q ∧ m = n + (h * q * d : ℕ) ∧ eligible q ∧ (q : ℤ) ∣ n ∧
      integerEdgeKeep Q u eligible g L K extra n ∧ integerEdgeKeep Q u eligible g L K extra m
  · rw [ite_eq_left he]
    have hkeep : eligible q ∧ (q : ℤ) ∣ n ∧ integerEdgeKeep Q u eligible g L K extra n :=
      ⟨he.2.2.1, he.2.2.2.1, he.2.2.2.2.1⟩
    rw [ite_eq_left he.2.1, retainedPaddingAtom, ite_eq_left hkeep]
    simp only [abs_div, abs_mul, abs_of_nonneg hL, abs_of_nonneg (hu q hq),
      abs_of_pos (hg n), abs_of_pos (hg m)]
    apply le_of_eq
    field_simp [(hg n).ne', (hg m).ne']
  · rw [ite_eq_right he, abs_zero, zero_mul, zero_div]
    split_ifs
    · exact mul_nonneg (abs_nonneg _) (retainedPaddingAtom_nonneg Q u eligible g L K extra n q hL (hu q hq))
    · exact le_rfl

lemma directedIntegerEdge_backward_bound
    (hL : 0 ≤ L) (hu : ∀ q ∈ Q, 0 ≤ u q) (hg : ∀ n, 0 < g n)
    (hperiod : ∀ q ∈ Q, ∀ n, center (n + (h * q * d : ℕ)) = center n)
    (q : ℕ) (hq : q ∈ Q) (n m : ℤ) :
    |directedIntegerEdge Q u eligible g center L K extra h d q m n| * g m / g n ≤
      if m = n - (h * q * d : ℕ) then
        |center n| * retainedPaddingAtom Q u eligible g L K extra n q else 0 := by
  classical
  unfold directedIntegerEdge
  by_cases he : q ∈ Q ∧ n = m + (h * q * d : ℕ) ∧ eligible q ∧ (q : ℤ) ∣ m ∧
      integerEdgeKeep Q u eligible g L K extra m ∧ integerEdgeKeep Q u eligible g L K extra n
  · rw [ite_eq_left he]
    have hm : m = n - (h * q * d : ℕ) := by omega
    have hdiv : (q : ℤ) ∣ n := (padding_dvd_along_edge h q d m n he.2.1).mpr he.2.2.2.1
    have hkeep : eligible q ∧ (q : ℤ) ∣ n ∧ integerEdgeKeep Q u eligible g L K extra n :=
      ⟨he.2.2.1, hdiv, he.2.2.2.2.2⟩
    have hc : center m = center n := by rw [he.2.1, hperiod q hq m]
    rw [ite_eq_left hm, retainedPaddingAtom, ite_eq_left hkeep, hc]
    simp only [abs_div, abs_mul, abs_of_nonneg hL, abs_of_nonneg (hu q hq),
      abs_of_pos (hg n), abs_of_pos (hg m)]
    apply le_of_eq
    field_simp [(hg n).ne', (hg m).ne']
  · rw [ite_eq_right he, abs_zero, zero_mul, zero_div]
    split_ifs
    · exact mul_nonneg (abs_nonneg _) (retainedPaddingAtom_nonneg Q u eligible g L K extra n q hL (hu q hq))
    · exact le_rfl

lemma directedIntegerEdge_forward_row
    {ι : Type*} [Fintype ι] (site : ι → ℤ) (hinj : Function.Injective site)
    (hL : 0 ≤ L) (hu : ∀ q ∈ Q, 0 ≤ u q) (hg : ∀ n, 0 < g n)
    (q : ℕ) (hq : q ∈ Q) (i : ι) :
    (∑ j, |directedIntegerEdge Q u eligible g center L K extra h d q (site i) (site j)| *
      g (site j) / g (site i)) ≤
      |center (site i)| * retainedPaddingAtom Q u eligible g L K extra (site i) q := by
  apply le_trans (sum_le_sum (fun j _ =>
    directedIntegerEdge_forward_bound Q u eligible g center L K extra h d hL hu hg q hq _ _))
  exact sum_indicator_site_le site hinj _ _ (mul_nonneg (abs_nonneg _)
    (retainedPaddingAtom_nonneg Q u eligible g L K extra _ q hL (hu q hq)))

lemma directedIntegerEdge_backward_row
    {ι : Type*} [Fintype ι] (site : ι → ℤ) (hinj : Function.Injective site)
    (hL : 0 ≤ L) (hu : ∀ q ∈ Q, 0 ≤ u q) (hg : ∀ n, 0 < g n)
    (hperiod : ∀ q ∈ Q, ∀ n, center (n + (h * q * d : ℕ)) = center n)
    (q : ℕ) (hq : q ∈ Q) (i : ι) :
    (∑ j, |directedIntegerEdge Q u eligible g center L K extra h d q (site j) (site i)| *
      g (site j) / g (site i)) ≤
      |center (site i)| * retainedPaddingAtom Q u eligible g L K extra (site i) q := by
  apply le_trans (sum_le_sum (fun j _ =>
    directedIntegerEdge_backward_bound Q u eligible g center L K extra h d hL hu hg hperiod q hq _ _))
  exact sum_indicator_site_le site hinj _ _ (mul_nonneg (abs_nonneg _)
    (retainedPaddingAtom_nonneg Q u eligible g L K extra _ q hL (hu q hq)))

/-- Both edge orientations are bounded by the same retained padding mass.
Incoming divisibility uses the actual integer step `h*q*d`. -/
theorem integerEdgeMatrix_weighted_row
    {ι : Type*} [Fintype ι] (site : ι → ℤ) (hinj : Function.Injective site)
    (hL : 0 < L) (hK : 0 ≤ K) (hu : ∀ q ∈ Q, 0 ≤ u q) (hg : ∀ n, 0 < g n)
    (hperiod : ∀ q ∈ Q, ∀ n, center (n + (h * q * d : ℕ)) = center n)
    (i : ι) :
    ∑ j, |integerEdgeMatrix site Q u eligible g center L K extra h d i j| *
      g (site j) / g (site i) ≤ 2 * K * |center (site i)| := by
  have habs (j : ι) : |integerEdgeMatrix site Q u eligible g center L K extra h d i j| ≤
      ∑ q ∈ Q, (|directedIntegerEdge Q u eligible g center L K extra h d q (site i) (site j)| +
        |directedIntegerEdge Q u eligible g center L K extra h d q (site j) (site i)|) := by
    apply (abs_sum_le_sum_abs _ _).trans
    exact sum_le_sum (fun q _ => abs_add_le _ _)
  calc
    _ ≤ ∑ j, (∑ q ∈ Q, (|directedIntegerEdge Q u eligible g center L K extra h d q (site i) (site j)| +
        |directedIntegerEdge Q u eligible g center L K extra h d q (site j) (site i)|)) *
        g (site j) / g (site i) := by
      apply sum_le_sum
      intro j _
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (habs j) (hg _).le) (hg _).le
    _ = ∑ q ∈ Q, ∑ j, (|directedIntegerEdge Q u eligible g center L K extra h d q (site i) (site j)| +
        |directedIntegerEdge Q u eligible g center L K extra h d q (site j) (site i)|) *
        g (site j) / g (site i) := by
      simp only [sum_mul, sum_div]
      rw [sum_comm]
    _ = ∑ q ∈ Q,
        ((∑ j, |directedIntegerEdge Q u eligible g center L K extra h d q (site i) (site j)| * g (site j) / g (site i)) +
          ∑ j, |directedIntegerEdge Q u eligible g center L K extra h d q (site j) (site i)| * g (site j) / g (site i)) := by
      simp only [add_mul, add_div, sum_add_distrib]
    _ ≤ ∑ q ∈ Q, 2 * |center (site i)| * retainedPaddingAtom Q u eligible g L K extra (site i) q := by
      apply sum_le_sum
      intro q hq
      have hf := directedIntegerEdge_forward_row Q u eligible g center L K extra h d site hinj hL.le hu hg q hq i
      have hb := directedIntegerEdge_backward_row Q u eligible g center L K extra h d site hinj hL.le hu hg hperiod q hq i
      exact (add_le_add hf hb).trans_eq (by ring)
    _ = 2 * |center (site i)| * (∑ q ∈ Q, retainedPaddingAtom Q u eligible g L K extra (site i) q) :=
      (mul_sum ..).symm
    _ ≤ 2 * |center (site i)| * K := mul_le_mul_of_nonneg_left
      (retainedPaddingAtom_sum_le Q u eligible g L K extra _ hL hK) (by positivity)
    _ = _ := by ring

lemma integerEdgeMatrix_center_invariant
    {ι : Type*} [Fintype ι] (site : ι → ℤ)
    (hperiod : ∀ q ∈ Q, ∀ n, center (n + (h * q * d : ℕ)) = center n)
    (i j : ι)
    (hA : integerEdgeMatrix site Q u eligible g center L K extra h d i j ≠ 0) :
    center (site i) = center (site j) := by
  classical
  by_contra hc
  apply hA
  unfold integerEdgeMatrix
  apply sum_eq_zero
  intro q hq
  have hf : directedIntegerEdge Q u eligible g center L K extra h d q (site i) (site j) = 0 := by
    unfold directedIntegerEdge
    split_ifs with he
    · exact False.elim (hc (by rw [he.2.1, hperiod q hq (site i)]))
    · rfl
  have hb : directedIntegerEdge Q u eligible g center L K extra h d q (site j) (site i) = 0 := by
    unfold directedIntegerEdge
    split_ifs with he
    · exact False.elim (hc (by rw [he.2.1, hperiod q hq (site j)]))
    · rfl
  simp only [hf, hb, add_zero]

end TwoPointCorrelations

end OAI
