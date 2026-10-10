import OAI.Probability.SignedSweeps.RowDimensionFormula

namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators Classical

lemma shifted_empty_vandermonde (q : ℕ) (lam : Partition 0) :
    nodeVandermonde (fun i => (shiftedRowNodes q lam.1 i : ℝ)) =
      ∏ i : Fin q, (Nat.factorial (shiftedRowNodes q lam.1 i) : ℝ) := by
  have hrow (i : ℕ) : lam.1.rowLen i = 0 := by
    have hh : lam.1.rowLen i ≤ 0 := by
      rw [YoungDiagram.rowLen_eq_card]
      exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq lam.2
    omega
  unfold nodeVandermonde
  apply Finset.prod_congr rfl
  intro a _
  have ht (b : Fin q) :
      (if a < b then (shiftedRowNodes q lam.1 a : ℝ) - shiftedRowNodes q lam.1 b else 1) =
        if a.val < b.val then ((b.val - a.val : ℕ) : ℝ) else 1 := by
    simp only [shiftedRowNodes, hrow, zero_add, Fin.lt_def]
    split_ifs with hab
    · simp only [Nat.cast_sub (by omega : a.val ≤ q - 1),
        Nat.cast_sub (by omega : b.val ≤ q - 1),
        Nat.cast_sub (by omega : 1 ≤ q), Nat.cast_sub hab.le, Nat.cast_one]
      ring
    · rfl
  simp_rw [ht]
  rw [Fin.prod_univ_eq_prod_range (fun b => if a.val < b then ((b - a.val : ℕ) : ℝ) else 1) q]
  rw [Finset.prod_ite]
  simp only [Finset.prod_const_one, mul_one]
  have he : (Finset.range q).filter (fun b => a.val < b) = Finset.Ico (a.val + 1) q := by
    ext b
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    omega
  rw [he, Finset.prod_Ico_eq_prod_range]
  have hv : ∀ j, (a.val + 1 + j - a.val : ℕ) = j + 1 := by intro j; omega
  simp_rw [hv]
  rw [← Nat.cast_prod, Finset.prod_range_add_one_eq_factorial]
  simp only [shiftedRowNodes, hrow, zero_add]
  congr 2
  omega

def tableauDegree {n : ℕ} (q : ℕ) (lam : Partition n) : ℝ :=
  (Nat.factorial n : ℝ) * nodeVandermonde (fun i => (shiftedRowNodes q lam.1 i : ℝ)) /
    (∏ i, (Nat.factorial (shiftedRowNodes q lam.1 i) : ℝ))

lemma tableauDegree_eq_candidate {n : ℕ} (q : ℕ) (lam : Partition n) :
    tableauDegree q lam = rowDegreeCandidate q lam * (q + 1 : ℝ) ^ (q * q) := by
  unfold tableauDegree rowDegreeCandidate
  have hz : (q + 1 : ℝ) ^ (q * q) ≠ 0 := by positivity
  field_simp

lemma tableauDegree_empty (q : ℕ) (lam : Partition 0) : tableauDegree q lam = 1 := by
  unfold tableauDegree
  simp only [Nat.factorial_zero, Nat.cast_one, one_mul, shifted_empty_vandermonde]
  exact div_self (ne_of_gt (shiftedRowFactorial_product_pos q lam.1))

lemma tableauDegree_pos {n : ℕ} (q : ℕ) (lam : Partition n) :
    0 < tableauDegree q lam := by
  unfold tableauDegree
  exact div_pos (mul_pos (Nat.cast_pos.mpr (Nat.factorial_pos n))
    (nodeVandermonde_pos _ (shiftedRealRows_strictAnti q lam.1)))
    (shiftedRowFactorial_product_pos q lam.1)

lemma tableauDegree_branching {n q : ℕ} (lam : Partition (n + 1))
    (hq : lam.1.colLen 0 ≤ q) :
    tableauDegree q lam = ∑ i : {i : Fin q // IsRowCorner lam.1 i.1},
      tableauDegree q (predecessorPartition lam i.2) := by
  simp_rw [tableauDegree_eq_candidate]
  rw [rowDegreeCandidate_branching lam hq, Finset.sum_mul]

theorem tableauDegree_le_dimension (n q : ℕ) (lam : Partition n)
    (hq : lam.1.colLen 0 ≤ q) : tableauDegree q lam ≤ spechtDimension lam := by
  induction n with
  | zero => simp only [tableauDegree_empty, spechtDimension_empty, Nat.cast_one, le_refl]
  | succ n ih =>
    rw [tableauDegree_branching lam hq]
    have hsub : ∑ i : {i : Fin q // IsRowCorner lam.1 i.1},
        spechtDimension (predecessorPartition lam i.2) ≤ spechtDimension lam := by
      apply sum_spechtDimensions_le
        ((spechtRepresentation lam).comp (Equiv.Perm.viaEmbeddingHom (Fin.castLEEmb (Nat.le_succ n))))
        (fun g => spechtRepresentation_norm lam _)
        (fun i : {i : Fin q // IsRowCorner lam.1 i.1} => predecessorPartition lam i.2)
      · intro i j hij
        apply Subtype.ext
        apply Fin.ext
        exact congrArg Subtype.val (@predecessorPartition_injective n lam
          ⟨i.1.val, i.2⟩ ⟨j.1.val, j.2⟩ hij)
      · intro i
        exact subdiagram_specht_occurs_at _ lam (eraseRowCorner_le _ i.2) _
    have hreal : ∑ i : {i : Fin q // IsRowCorner lam.1 i.1},
        (spechtDimension (predecessorPartition lam i.2) : ℝ) ≤ spechtDimension lam := by
      exact_mod_cast hsub
    apply le_trans (Finset.sum_le_sum (fun i _ => ih _ ?_)) hreal
    by_contra hh
    have hm : (q, 0) ∈ (predecessorPartition lam i.2).1 :=
      YoungDiagram.mem_iff_lt_colLen.mpr (Nat.lt_of_not_ge hh)
    have hm' := eraseRowCorner_le lam.1 i.2 hm
    exact (not_lt_of_ge hq) (YoungDiagram.mem_iff_lt_colLen.mp hm')

end SignedSweeps
end

end OAI
