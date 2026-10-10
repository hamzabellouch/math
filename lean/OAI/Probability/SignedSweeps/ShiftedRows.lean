import OAI.Probability.SignedSweeps.YoungCorners
import OAI.Probability.SignedSweeps.VandermondeBranch

namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators Classical

lemma rowLen_eq_zero_of_height_le (lam : YoungDiagram) {k : ℕ}
    (hk : lam.colLen 0 ≤ k) : lam.rowLen k = 0 := by
  by_contra hn
  have hm : (k, 0) ∈ lam := YoungDiagram.mem_iff_lt_rowLen.mpr (Nat.pos_of_ne_zero hn)
  have hc := YoungDiagram.mem_iff_lt_colLen.mp hm
  omega

lemma partition_sum_padded_rows {n q : ℕ} (lam : Partition n) (hq : lam.1.colLen 0 ≤ q) :
    ∑ i : Fin q, lam.1.rowLen i = n := by
  rw [Fin.sum_univ_eq_sum_range]
  have hs : ∑ i ∈ Finset.range (lam.1.colLen 0), lam.1.rowLen i = n := by
    simpa [Fin.sum_univ_eq_sum_range] using lam.sum_rowLen
  apply Eq.trans ?_ hs
  symm
  apply Finset.sum_subset (Finset.range_mono hq)
  intro k _ hk
  exact rowLen_eq_zero_of_height_le lam.1 (by simpa using hk)

def shiftedRowNodes (q : ℕ) (lam : YoungDiagram) (i : Fin q) : ℕ :=
  lam.rowLen i + (q - 1 - i.1)

lemma shiftedRowNodes_strictAnti (q : ℕ) (lam : YoungDiagram) :
    StrictAnti (shiftedRowNodes q lam) := by
  intro i j hij
  have hrows := lam.rowLen_anti i j (Fin.le_iff_val_le_val.mp hij.le)
  unfold shiftedRowNodes
  have hi := i.isLt
  have hj := j.isLt
  have hij' := Fin.lt_def.mp hij
  omega

lemma shiftedRealRows_strictAnti (q : ℕ) (lam : YoungDiagram) :
    StrictAnti (fun i => (shiftedRowNodes q lam i : ℝ)) := by
  intro i j hij
  exact Nat.cast_lt.mpr (shiftedRowNodes_strictAnti q lam hij)

lemma shiftedRowNodes_sum {n q : ℕ} (lam : Partition n) (hq : lam.1.colLen 0 ≤ q) :
    (∑ i : Fin q, (shiftedRowNodes q lam.1 i : ℝ)) -
      (q : ℝ) * ((q : ℝ) - 1) / 2 = n := by
  have hst : (∑ i : Fin q, (q - 1 - i.1 : ℕ)) * 2 = q * (q - 1) := by
    rw [Fin.sum_univ_eq_sum_range, Finset.sum_range_reflect (fun i : ℕ => i) q]
    exact Finset.sum_range_id_mul_two q
  have hsum : ∑ i : Fin q, (lam.1.rowLen i : ℝ) = n := by
    exact_mod_cast partition_sum_padded_rows lam hq
  have hs : (∑ i : Fin q, ((q - 1 - i.1 : ℕ) : ℝ)) =
      (q : ℝ) * ((q : ℝ) - 1) / 2 := by
    by_cases hzero : q = 0
    · subst q
      simp
    · have hcast := congrArg (fun k : ℕ => (k : ℝ)) hst
      rw [Nat.cast_mul, Nat.cast_sum, Nat.cast_ofNat, Nat.cast_mul,
        Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hzero), Nat.cast_one] at hcast
      linarith
  simp only [shiftedRowNodes, Nat.cast_add, Finset.sum_add_distrib, hsum, hs]
  ring

lemma shiftedRowNodes_erase {q : ℕ} (lam : YoungDiagram) (i : Fin q)
    (hi : IsRowCorner lam i) :
    shiftedRowNodes q (eraseRowCorner lam hi) =
      Function.update (shiftedRowNodes q lam) i (shiftedRowNodes q lam i - 1) := by
  funext j
  rw [shiftedRowNodes, eraseRowCorner_rowLen]
  by_cases hj : j = i
  · subst j
    rw [ite_eq_left rfl, Function.update_self]
    have hp : 0 < lam.rowLen i := by have := hi; unfold IsRowCorner at this; omega
    unfold shiftedRowNodes
    omega
  · rw [ite_eq_right (fun h => hj (Fin.ext h)), Function.update_of_ne hj]
    rfl

lemma shiftedRowNodes_corner_pos {q : ℕ} (lam : YoungDiagram) (i : Fin q)
    (hi : IsRowCorner lam i) : 0 < shiftedRowNodes q lam i := by
  have hp : 0 < lam.rowLen i := by have := hi; unfold IsRowCorner at this; omega
  unfold shiftedRowNodes
  omega

lemma shiftedRealRows_erase {q : ℕ} (lam : YoungDiagram) (i : Fin q)
    (hi : IsRowCorner lam i) :
    (fun j => (shiftedRowNodes q (eraseRowCorner lam hi) j : ℝ)) =
      Function.update (fun j => (shiftedRowNodes q lam j : ℝ)) i
        ((shiftedRowNodes q lam i : ℝ) - 1) := by
  rw [shiftedRowNodes_erase lam i hi]
  funext j
  by_cases hj : j = i
  · subst j
    simp only [Function.update_self]
    rw [Nat.cast_sub (shiftedRowNodes_corner_pos lam i hi), Nat.cast_one]
  · simp [Function.update_of_ne hj]

lemma nodeVandermonde_eq_zero_of_eq {I : Type*} [Fintype I] [LinearOrder I]
    (x : I → ℝ) {a b : I} (hab : a ≠ b) (he : x a = x b) : nodeVandermonde x = 0 := by
  suffices ∀ a b, a < b → x a = x b → nodeVandermonde x = 0 by
    rcases lt_or_gt_of_ne hab with hh | hh
    · exact this a b hh he
    · exact this b a hh he.symm
  intro a b hab he
  apply Finset.prod_eq_zero (Finset.mem_univ a)
  apply Finset.prod_eq_zero (Finset.mem_univ b)
  simp [hab, he]

lemma shiftedRows_noncorner_zero {q : ℕ} (lam : YoungDiagram)
    (hq : lam.colLen 0 ≤ q) (i : Fin q) (hi : ¬ IsRowCorner lam i) :
    (shiftedRowNodes q lam i : ℝ) *
      nodeVandermonde (Function.update (fun j => (shiftedRowNodes q lam j : ℝ)) i
        ((shiftedRowNodes q lam i : ℝ) - 1)) = 0 := by
  have he : lam.rowLen (i.1 + 1) = lam.rowLen i :=
    le_antisymm (lam.rowLen_anti _ _ (Nat.le_succ _)) (Nat.le_of_not_gt hi)
  by_cases hlast : i.1 + 1 = q
  · have hz : lam.rowLen i = 0 := by
      rw [← he, hlast]
      exact rowLen_eq_zero_of_height_le lam hq
    have hh : shiftedRowNodes q lam i = 0 := by unfold shiftedRowNodes; rw [hz]; omega
    rw [hh, Nat.cast_zero, zero_mul]
  · have hj : i.1 + 1 < q := by have := i.isLt; omega
    let j : Fin q := ⟨i.1 + 1, hj⟩
    have hjne : j ≠ i := by intro h; have := congrArg Fin.val h; dsimp [j] at this; omega
    have hh : shiftedRowNodes q lam i = shiftedRowNodes q lam j + 1 := by
      unfold shiftedRowNodes
      dsimp [j]
      rw [he]
      omega
    have hnew : Function.update (fun j => (shiftedRowNodes q lam j : ℝ)) i
        ((shiftedRowNodes q lam i : ℝ) - 1) i =
        Function.update (fun j => (shiftedRowNodes q lam j : ℝ)) i
          ((shiftedRowNodes q lam i : ℝ) - 1) j := by
      simp [Function.update_of_ne hjne, hh]
    rw [nodeVandermonde_eq_zero_of_eq _ hjne.symm hnew, mul_zero]

end SignedSweeps
end

end OAI
