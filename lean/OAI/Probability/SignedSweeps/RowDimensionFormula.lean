import OAI.Probability.SignedSweeps.BranchingDimensions
import OAI.Probability.SignedSweeps.ShiftedRows

namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators Classical

lemma factorial_product_decrement {I : Type*} [Fintype I] [DecidableEq I]
    (x : I → ℕ) (i : I) (hi : 0 < x i) :
    (∏ j, (Nat.factorial (x j) : ℝ)) = (x i : ℝ) *
      ∏ j, (Nat.factorial (Function.update x i (x i - 1) j) : ℝ) := by
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
  rw [← Finset.mul_prod_erase Finset.univ (fun j =>
    (Nat.factorial (Function.update x i (x i - 1) j) : ℝ)) (Finset.mem_univ i)]
  rw [Function.update_self]
  have he : (∏ j ∈ Finset.univ.erase i,
      (Nat.factorial (Function.update x i (x i - 1) j) : ℝ)) =
      ∏ j ∈ Finset.univ.erase i, (Nat.factorial (x j) : ℝ) := by
    apply Finset.prod_congr rfl
    intro j hj
    rw [Function.update_of_ne (Finset.mem_erase.mp hj).1]
  rw [he, ← mul_assoc, ← Nat.cast_mul, Nat.mul_factorial_pred (Nat.ne_of_gt hi)]

def rowDegreeCandidate {n : ℕ} (q : ℕ) (lam : Partition n) : ℝ :=
  (Nat.factorial n : ℝ) * nodeVandermonde (fun i => (shiftedRowNodes q lam.1 i : ℝ)) /
    ((∏ i, (Nat.factorial (shiftedRowNodes q lam.1 i) : ℝ)) * (q + 1 : ℝ) ^ (q * q))

lemma rowDegreeCandidate_nonneg {n : ℕ} (q : ℕ) (lam : Partition n) :
    0 ≤ rowDegreeCandidate q lam := by
  apply div_nonneg
  · exact mul_nonneg (Nat.cast_nonneg _) (nodeVandermonde_pos _ (shiftedRealRows_strictAnti q lam.1)).le
  · positivity

lemma shiftedRowFactorial_product_pos (q : ℕ) (lam : YoungDiagram) :
    0 < ∏ i : Fin q, (Nat.factorial (shiftedRowNodes q lam i) : ℝ) := by
  exact Finset.prod_pos (fun i _ => Nat.cast_pos.mpr (Nat.factorial_pos _))

theorem rowDegreeCandidate_branching {n q : ℕ} (lam : Partition (n + 1))
    (hq : lam.1.colLen 0 ≤ q) :
    rowDegreeCandidate q lam = ∑ i : {i : Fin q // IsRowCorner lam.1 i.1},
      rowDegreeCandidate q (predecessorPartition lam i.2) := by
  let x := shiftedRowNodes q lam.1
  let D : ℝ := ∏ i, (Nat.factorial (x i) : ℝ)
  let Z : ℝ := (q + 1 : ℝ) ^ (q * q)
  have hx : Function.Injective (fun i => (x i : ℝ)) :=
    (shiftedRealRows_strictAnti q lam.1).injective
  have hD : D ≠ 0 := ne_of_gt (shiftedRowFactorial_product_pos q lam.1)
  have hZ : Z ≠ 0 := by dsimp [Z]; positivity
  have hs : (∑ i, (x i : ℝ) * nodeVandermonde
      (Function.update (fun j => (x j : ℝ)) i ((x i : ℝ) - 1))) =
      (n + 1) * nodeVandermonde (fun j => (x j : ℝ)) := by
    rw [nodeVandermonde_branching _ hx]
    simp only [x, Fintype.card_fin, shiftedRowNodes_sum lam hq, Nat.cast_add, Nat.cast_one]
  have hterm (i : Fin q) :
      (Nat.factorial n : ℝ) * ((x i : ℝ) * nodeVandermonde
          (Function.update (fun j => (x j : ℝ)) i ((x i : ℝ) - 1))) / (D * Z) =
        if hi : IsRowCorner lam.1 i then
          rowDegreeCandidate q (predecessorPartition lam hi) else 0 := by
    split_ifs with hi
    · have hxi := shiftedRowNodes_corner_pos lam.1 i hi
      have hfac : D = (x i : ℝ) *
          ∏ j : Fin q, (Nat.factorial (shiftedRowNodes q (eraseRowCorner lam.1 hi) j) : ℝ) := by
        rw [shiftedRowNodes_erase lam.1 i hi]
        exact factorial_product_decrement x i hxi
      have hchild : (∏ j : Fin q,
          (Nat.factorial (shiftedRowNodes q (eraseRowCorner lam.1 hi) j) : ℝ)) ≠ 0 :=
        ne_of_gt (shiftedRowFactorial_product_pos q _)
      have hxi0 : (x i : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hxi)
      change _ = (Nat.factorial n : ℝ) *
        nodeVandermonde (fun j => (shiftedRowNodes q (eraseRowCorner lam.1 hi) j : ℝ)) /
          ((∏ j, (Nat.factorial (shiftedRowNodes q (eraseRowCorner lam.1 hi) j) : ℝ)) * Z)
      rw [shiftedRealRows_erase lam.1 i hi, hfac]
      dsimp only [x]
      field_simp
    · rw [shiftedRows_noncorner_zero lam.1 hq i hi]
      simp
  calc
    rowDegreeCandidate q lam = (Nat.factorial n : ℝ) *
        ((n + 1) * nodeVandermonde (fun i => (x i : ℝ))) / (D * Z) := by
      unfold rowDegreeCandidate
      rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
      dsimp only [x, D, Z]
      ring
    _ = ∑ i : Fin q, (if hi : IsRowCorner lam.1 i then
        rowDegreeCandidate q (predecessorPartition lam hi) else 0) := by
      rw [← hs, Finset.mul_sum, Finset.sum_div]
      exact Finset.sum_congr rfl (fun i _ => hterm i)
    _ = _ := by
      rw [← Fintype.sum_subtype_add_sum_subtype
        (fun i : Fin q => IsRowCorner lam.1 i.1)]
      have hy : (∑ i : {i : Fin q // IsRowCorner lam.1 i.1},
          if hi : IsRowCorner lam.1 i.1.1 then
            rowDegreeCandidate q (predecessorPartition lam hi) else 0) =
          ∑ i : {i : Fin q // IsRowCorner lam.1 i.1},
            rowDegreeCandidate q (predecessorPartition lam i.2) := by
        exact Finset.sum_congr rfl (fun i _ => dite_eq_left i.2)
      have hn : (∑ i : {i : Fin q // ¬ IsRowCorner lam.1 i.1},
          if hi : IsRowCorner lam.1 i.1.1 then
            rowDegreeCandidate q (predecessorPartition lam hi) else 0) = 0 := by
        exact Finset.sum_eq_zero (fun i _ => dite_eq_right i.2)
      rw [hy, hn, add_zero]

lemma rowDegreeCandidate_empty (q : ℕ) (lam : Partition 0) :
    rowDegreeCandidate q lam ≤ 1 := by
  have hrow (i : ℕ) : lam.1.rowLen i = 0 := by
    have hh : lam.1.rowLen i ≤ 0 := by
      rw [YoungDiagram.rowLen_eq_card]
      exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq lam.2
    omega
  have hv : nodeVandermonde (fun i => (shiftedRowNodes q lam.1 i : ℝ)) ≤
      (q + 1 : ℝ) ^ (q * q) := by
    have hb (a b : Fin q) :
        0 ≤ (if a < b then (shiftedRowNodes q lam.1 a : ℝ) - shiftedRowNodes q lam.1 b else 1) ∧
        (if a < b then (shiftedRowNodes q lam.1 a : ℝ) - shiftedRowNodes q lam.1 b else 1) ≤ q + 1 := by
      split_ifs with hab
      · constructor
        · exact (sub_pos.mpr (shiftedRealRows_strictAnti q lam.1 hab)).le
        · rw [shiftedRowNodes, hrow]
          have ha : (q - 1 - a.1 : ℕ) ≤ q := by omega
          have hb' : (0 : ℝ) ≤ shiftedRowNodes q lam.1 b := Nat.cast_nonneg _
          have ha' : (q - 1 - a.1 : ℕ) ≤ (q : ℝ) := Nat.cast_le.mpr ha
          simp only [zero_add]
          linarith
      · constructor
        · norm_num
        · linarith [Nat.cast_nonneg (α := ℝ) q]
    calc
      _ ≤ ∏ a : Fin q, ∏ b : Fin q, (q + 1 : ℝ) := by
        apply Finset.prod_le_prod₀
        · intro a _
          exact Finset.prod_nonneg (fun b _ => (hb a b).1)
        · intro a _
          exact Finset.prod_le_prod₀ (fun b _ => (hb a b).1) (fun b _ => (hb a b).2)
      _ = _ := by simp [pow_mul]
  have hD : 1 ≤ ∏ i : Fin q, (Nat.factorial (shiftedRowNodes q lam.1 i) : ℝ) := by
    apply Finset.one_le_prod₀
    intro i _
    exact_mod_cast Nat.factorial_pos (shiftedRowNodes q lam.1 i)
  have hZ : 0 < (q + 1 : ℝ) ^ (q * q) := by positivity
  unfold rowDegreeCandidate
  simp only [Nat.factorial_zero, Nat.cast_one, one_mul]
  rw [div_le_one (mul_pos (shiftedRowFactorial_product_pos q lam.1) hZ)]
  exact hv.trans (by nlinarith)

theorem rowDegreeCandidate_le_dimension (n q : ℕ) (lam : Partition n)
    (hq : lam.1.colLen 0 ≤ q) : rowDegreeCandidate q lam ≤ spechtDimension lam := by
  induction n with
  | zero => simpa only [spechtDimension_empty, Nat.cast_one] using rowDegreeCandidate_empty q lam
  | succ n ih =>
    rw [rowDegreeCandidate_branching lam hq]
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
