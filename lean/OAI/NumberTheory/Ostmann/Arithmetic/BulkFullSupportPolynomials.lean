import OAI.NumberTheory.Ostmann.Arithmetic.RealBulkKernel
import OAI.NumberTheory.Ostmann.Arithmetic.BulkNodeSupportPolynomials
import OAI.NumberTheory.Ostmann.Arithmetic.BulkSmoothRootCuts

namespace OAI

/-! # Root cells for every original bulk support gate -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def bulkFullSupportPolynomials {σ : Type*} (value : σ → ℝ) (i : σ)
    (childBound pivotBound : ℕ → ℕ) {n : ℕ} (T : MovingSlotData σ n)
    (L R : Polynomial ℝ) (X lo hi : ℝ) :
    Fin (T.bulkNodeSupportPolynomials value i childBound pivotBound L R).length ⊕
      (TreeLeafIndex n × Bool) → Polynomial ℝ :=
  Sum.elim (fun j => (T.bulkNodeSupportPolynomials value i childBound pivotBound L R)[j])
    (fun j => let M := Polynomial.C X⁻¹ * T.bulkLeafPolynomials value i L R j.1
      if j.2 then Polynomial.C hi - M else M - Polynomial.C lo)

theorem bulkFullSupportPolynomials_eval {σ : Type*} (value : σ → ℝ) (i : σ)
    (childBound pivotBound : ℕ → ℕ) {n : ℕ} (T : MovingSlotData σ n)
    (hT : T.CompensationAbsent i) (L R : Polynomial ℝ) (X lo hi z : ℝ) :
    (∀ j, 0 ≤ (bulkFullSupportPolynomials value i childBound pivotBound T L R X lo hi j).eval z) ↔
      realValueFullSupport (Function.update value i z) childBound pivotBound T X lo hi (L.eval z) (R.eval z) := by
  have hn := T.bulkNodeSupportPolynomials_eval value i childBound pivotBound hT L R z
  rw [List.forall_mem_iff_get] at hn
  constructor
  · intro h
    refine ⟨hn.mp (fun j => h (.inl j)), ?_⟩
    intro j
    have hl := h (.inr (j, false))
    have hh := h (.inr (j, true))
    simp only [bulkFullSupportPolynomials, Sum.elim_inr, Bool.false_eq_true, ite_false,
      ite_true, Polynomial.eval_sub, Polynomial.eval_C, Polynomial.eval_mul,
      T.bulkLeafPolynomials_eval value i hT L R z] at hl hh
    exact ⟨by simpa only [sub_nonneg, div_eq_mul_inv, mul_comm] using hl,
      by simpa only [sub_nonneg, div_eq_mul_inv, mul_comm] using hh⟩
  · rintro ⟨hnode, hwindow⟩ j
    cases j with
    | inl j => exact hn.mpr hnode j
    | inr j =>
      rcases j with ⟨j, b⟩
      have hj := hwindow j
      cases b
      · simpa only [bulkFullSupportPolynomials, Sum.elim_inr, Bool.false_eq_true, ite_false,
          Polynomial.eval_sub, Polynomial.eval_C, Polynomial.eval_mul,
          T.bulkLeafPolynomials_eval value i hT L R z, sub_nonneg, div_eq_mul_inv, mul_comm] using hj.1
      · simpa only [bulkFullSupportPolynomials, Sum.elim_inr, ite_true,
          Polynomial.eval_sub, Polynomial.eval_C, Polynomial.eval_mul,
          T.bulkLeafPolynomials_eval value i hT L R z, sub_nonneg, div_eq_mul_inv, mul_comm] using hj.2

theorem bulkFullSupportPolynomials_degree {σ : Type*} (value : σ → ℝ) (i : σ)
    (childBound pivotBound : ℕ → ℕ) {n : ℕ} (T : MovingSlotData σ n)
    (L R : Polynomial ℝ) (X lo hi : ℝ) (d r e : ℕ)
    (hsize : T.SizeLE d) (hregular : T.RegularLengthLE r)
    (hL : L.natDegree ≤ e) (hR : R.natDegree ≤ e) :
    ∀ j, (bulkFullSupportPolynomials value i childBound pivotBound T L R X lo hi j).natDegree ≤
      2 * (n * d + e) + r := by
  intro j
  cases j with
  | inl j =>
    exact (T.bulkNodeSupportPolynomials_degree value i childBound pivotBound L R d e hsize hL hR
      _ (List.getElem_mem j.isLt)).trans (by omega)
  | inr j =>
    have hM : (Polynomial.C X⁻¹ * T.bulkLeafPolynomials value i L R j.1).natDegree ≤
        2 * (n * d + e) + r := by
      have ht := T.bulkLeafPolynomials_degree value i L R d r e hsize hregular hL hR j.1
      exact Polynomial.natDegree_mul_le.trans (by simpa only [Polynomial.natDegree_C, zero_add] using ht)
    rcases j with ⟨j, b⟩
    cases b
    · exact (Polynomial.natDegree_sub_le _ _).trans (by
        simpa only [Polynomial.natDegree_C, max_zero] using hM)
    · exact (Polynomial.natDegree_sub_le _ _).trans (by
        simpa only [Polynomial.natDegree_C, zero_max] using hM)

/-- These roots include all node ranges and terminal windows. The count is
uniform in all other real bulk values and both giant coefficients. -/
theorem bulkFullSupport_root_cuts {σ : Type*} (value : σ → ℝ) (i : σ)
    (childBound pivotBound : ℕ → ℕ) {n : ℕ} (T : MovingSlotData σ n)
    (hT : T.CompensationAbsent i) (L R : Polynomial ℝ) (X lo hi : ℝ) (d r e : ℕ)
    (hsize : T.SizeLE d) (hregular : T.RegularLengthLE r)
    (hL : L.natDegree ≤ e) (hR : R.natDegree ≤ e) :
    ∃ S : Finset ℝ, S.card ≤ (3 * (2 ^ n - 1) + 2 * 2 ^ n) * (2 * (n * d + e) + r) ∧
      ∀ x y, rootCellCode S x = rootCellCode S y →
        realValueSupportFlag (Function.update value i x) childBound pivotBound T X lo hi (L.eval x) (R.eval x) =
        realValueSupportFlag (Function.update value i y) childBound pivotBound T X lo hi (L.eval y) (R.eval y) := by
  let J := Fin (T.bulkNodeSupportPolynomials value i childBound pivotBound L R).length ⊕
    (TreeLeafIndex n × Bool)
  let H := bulkFullSupportPolynomials value i childBound pivotBound T L R X lo hi
  let S := polynomialRootCuts H
  have hroot (j) (z) (hz : z ∈ (H j).roots) : z ∈ S :=
    Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, Multiset.mem_toFinset.mpr hz⟩
  refine ⟨S, ?_, ?_⟩
  · apply (polynomialRootCuts_card H).trans
    calc
      _ ≤ ∑ _j : J, (2 * (n * d + e) + r) := Finset.sum_le_sum (fun j _ =>
        bulkFullSupportPolynomials_degree value i childBound pivotBound T L R X lo hi d r e
          hsize hregular hL hR j)
      _ = _ := by
        simp only [J, Finset.sum_const, Finset.card_univ, Fintype.card_sum, Fintype.card_fin,
          Fintype.card_prod, Fintype.card_bool, card_treeLeafIndex,
          MovingSlotData.bulkNodeSupportPolynomials_length, smul_eq_mul]
        ring
  · intro x y hxy
    have hp : (∀ j, 0 ≤ (H j).eval x) ↔ ∀ j, 0 ≤ (H j).eval y :=
      forall_congr' (fun j => polynomial_nonneg_iff_of_root_cell (H j) S (hroot j) hxy)
    have hx := bulkFullSupportPolynomials_eval value i childBound pivotBound T hT L R X lo hi x
    have hy := bulkFullSupportPolynomials_eval value i childBound pivotBound T hT L R X lo hi y
    have he := hx.symm.trans (hp.trans hy)
    exact if_congr he rfl rfl

end Ostmann

end OAI
