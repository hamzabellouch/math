import OAI.Probability.SignedSweeps.ColorEntropy
import OAI.Probability.SignedSweeps.InducedCarrier

namespace OAI

noncomputable section
namespace SignedSweeps.Partition
open scoped BigOperators TensorProduct
open Module

lemma rowOf_lt_colLen {n : ℕ} (lam : Partition n) (x : Fin n) :
    lam.rowOf x < lam.1.colLen (lam.colOf x) :=
  YoungDiagram.mem_iff_lt_colLen.mp (lam.tableau.symm x).property

def colEquiv {n : ℕ} (lam : Partition n) :
    (Σ j : Fin (lam.1.rowLen 0), Fin (lam.1.colLen j)) ≃ Fin n where
  toFun x := lam.tableau ⟨(x.2.val, x.1.val), YoungDiagram.mem_iff_lt_colLen.mpr x.2.isLt⟩
  invFun x := ⟨⟨lam.colOf x, lam.colOf_lt x⟩, ⟨lam.rowOf x, lam.rowOf_lt_colLen x⟩⟩
  left_inv x := by
    apply Sigma.ext
    · apply Fin.ext
      simp [colOf]
    · apply (Fin.heq_ext_iff (by simp [colOf])).mpr
      simp [rowOf]
  right_inv x := by simp only; exact lam.tableau.apply_symm_apply x

@[simp] lemma colOf_colEquiv {n : ℕ} (lam : Partition n)
    (i : Fin (lam.1.rowLen 0)) (j : Fin (lam.1.colLen i)) :
    lam.colOf (lam.colEquiv ⟨i, j⟩) = i.val := by simp [colEquiv, colOf]

lemma sum_rowLen {n : ℕ} (lam : Partition n) :
    ∑ i : Fin (lam.1.colLen 0), lam.1.rowLen i = n := by
  simpa using Fintype.card_congr lam.rowEquiv

lemma sum_colLen {n : ℕ} (lam : Partition n) :
    ∑ i : Fin (lam.1.rowLen 0), lam.1.colLen i = n := by
  simpa using Fintype.card_congr lam.colEquiv

lemma rowLen_pos {n : ℕ} (lam : Partition n) (i : Fin (lam.1.colLen 0)) :
    0 < lam.1.rowLen i :=
  YoungDiagram.mem_iff_lt_rowLen.mp (YoungDiagram.mem_iff_lt_colLen.mpr i.isLt)

lemma colLen_pos {n : ℕ} (lam : Partition n) (i : Fin (lam.1.rowLen 0)) :
    0 < lam.1.colLen i :=
  YoungDiagram.mem_iff_lt_colLen.mp (YoungDiagram.mem_iff_lt_rowLen.mpr i.isLt)

lemma sum_rowOf {n : ℕ} (lam : Partition n) (f : ℕ → ℝ) :
    ∑ x, f (lam.rowOf x) = ∑ i : Fin (lam.1.colLen 0), (lam.1.rowLen i : ℝ) * f i := by
  rw [← Equiv.sum_comp lam.rowEquiv (fun x => f (lam.rowOf x)), Fintype.sum_sigma]
  simp only [rowOf_rowEquiv, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

lemma sum_colOf {n : ℕ} (lam : Partition n) (f : ℕ → ℝ) :
    ∑ x, f (lam.colOf x) = ∑ i : Fin (lam.1.rowLen 0), (lam.1.colLen i : ℝ) * f i := by
  rw [← Equiv.sum_comp lam.colEquiv (fun x => f (lam.colOf x)), Fintype.sum_sigma]
  simp only [colOf_colEquiv, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

end SignedSweeps.Partition
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module

lemma partsEntropy_rowLen {n : ℕ} (lam : Partition n) (N : ℝ) :
    partsEntropy N lam.1.rowLens =
      ∑ i : Fin (lam.1.colLen 0), (lam.1.rowLen i : ℝ) * Real.log (N / lam.1.rowLen i) := by
  rw [partsEntropy, YoungDiagram.rowLens, List.map_map,
    ← List.sum_toFinset _ List.nodup_range, List.toFinset_range]
  exact (Fin.sum_univ_eq_sum_range (fun i => (lam.1.rowLen i : ℝ) * Real.log (N / lam.1.rowLen i)) _).symm

def signedColorProbability {u v : ℕ} (α : Partition u) (β : Partition v) (l n : ℕ) :
    ((Fin (α.1.colLen 0) ⊕ Fin (β.transpose.1.rowLen 0)) ⊕ Unit) → ℝ :=
  Sum.elim (Sum.elim (fun i => (α.1.rowLen i : ℝ) / n)
    (fun j => (β.transpose.1.colLen j : ℝ) / n)) (fun _ => (l : ℝ) / n)

lemma signedColorProbability_nonneg {u v : ℕ} (α : Partition u) (β : Partition v) (l n : ℕ) (i) :
    0 ≤ signedColorProbability α β l n i := by
  rcases i with ((i | j) | k) <;> dsimp [signedColorProbability] <;> positivity

lemma signedColorProbability_sum {u v l n : ℕ} (h : u + v + l = n) (hn : 0 < n)
    (α : Partition u) (β : Partition v) :
    ∑ i, signedColorProbability α β l n i = 1 := by
  simp only [signedColorProbability, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
    Fintype.sum_unique, ← Finset.sum_div, ← Nat.cast_sum, Partition.sum_rowLen, Partition.sum_colLen,
    ← add_div, ← Nat.cast_add, h]
  exact div_self (by exact_mod_cast hn.ne')

lemma signedColorProbability_used_pos {u v l n : ℕ} (h : u + v + l = n) (hn : 0 < n)
    (α : Partition u) (β : Partition v) (x : Fin n) :
    0 < signedColorProbability α β l n (blockColoring h α.rowIndex β.transpose.colIndex x) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rcases hx : (blockEquiv h).symm x with ((a | b) | c)
  · change 0 < Sum.elim _ _ (Sum.map _ _ ((blockEquiv h).symm x))
    rw [hx]
    exact div_pos (by exact_mod_cast α.rowLen_pos (α.rowIndex a)) hn'
  · change 0 < Sum.elim _ _ (Sum.map _ _ ((blockEquiv h).symm x))
    rw [hx]
    exact div_pos (by exact_mod_cast β.transpose.colLen_pos (β.transpose.colIndex b)) hn'
  · change 0 < Sum.elim _ _ (Sum.map _ _ ((blockEquiv h).symm x))
    rw [hx]
    exact div_pos (by exact_mod_cast c.pos) hn'

lemma signedColorProbability_entropy {u v l n : ℕ} (h : u + v + l = n)
    (α : Partition u) (β : Partition v) :
    -(∑ x, Real.log (signedColorProbability α β l n
      (blockColoring h α.rowIndex β.transpose.colIndex x))) =
      partsEntropy n α.1.rowLens + partsEntropy n β.1.rowLens +
        (l : ℝ) * Real.log ((n : ℝ) / l) := by
  rw [← Equiv.sum_comp (blockEquiv h)
    (fun x => Real.log (signedColorProbability α β l n (blockColoring h α.rowIndex β.transpose.colIndex x)))]
  simp only [blockColoring, Function.comp_apply, Equiv.symm_apply_apply,
    Fintype.sum_sum_type, Sum.map_inl, Sum.map_inr, signedColorProbability, Sum.elim_inl, Sum.elim_inr,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Partition.rowIndex, Partition.colIndex]
  rw [α.sum_rowOf (fun i => Real.log ((α.1.rowLen i : ℝ) / n)),
    β.transpose.sum_colOf (fun i => Real.log ((β.transpose.1.colLen i : ℝ) / n))]
  rw [partsEntropy_rowLen, partsEntropy_rowLen]
  dsimp +instances only [Partition.transpose]
  simp only [YoungDiagram.colLen_transpose]
  have hl (a : ℝ) : Real.log (a / n) = -Real.log ((n : ℝ) / a) := by
    rw [← Real.log_inv, inv_div]
  simp only [hl, mul_neg, Finset.sum_neg_distrib, neg_add, neg_neg]
  have hb := Fin.sum_univ_eq_sum_range
    (fun i => (β.1.rowLen i : ℝ) * Real.log ((n : ℝ) / β.1.rowLen i))
  rw [hb, hb, YoungDiagram.rowLen_transpose]

lemma partsEntropy_change_total {A B : ℝ} (hA : 0 < A) (hB : 0 < B) (L : List ℕ) :
    partsEntropy B L = partsEntropy A L + (L.sum : ℝ) * Real.log (B / A) := by
  induction L with
  | nil => simp [partsEntropy]
  | cons a L ih =>
    have ht : (a : ℝ) * Real.log (B / a) =
        (a : ℝ) * Real.log (A / a) + (a : ℝ) * Real.log (B / A) := by
      by_cases ha : a = 0
      · simp [ha]
      · have ha' : (a : ℝ) ≠ 0 := by exact_mod_cast ha
        rw [Real.log_div hB.ne' ha', Real.log_div hA.ne' ha', Real.log_div hB.ne' hA.ne']
        ring
    simp only [partsEntropy, List.map_cons, List.sum_cons] at ih ⊢
    rw [ht, ih, Nat.cast_add]
    ring

lemma partsEntropy_partition_empty (lam : Partition 0) (A : ℝ) :
    partsEntropy A lam.1.rowLens = 0 := by
  have hz : lam.1.rowLens = [] := List.eq_nil_iff_forall_not_mem.mpr (by
    intro a ha
    exact (not_lt_of_ge (row_part_le_size lam ha)) (lam.1.pos_of_mem_rowLens a ha))
  simp [partsEntropy, hz]

lemma signedEntropy_change_total {u v n : ℕ} (hn : 0 < n)
    (α : Partition u) (β : Partition v) :
    partsEntropy n α.1.rowLens + partsEntropy n β.1.rowLens =
      signedEntropy α β + ((u : ℝ) + v) * Real.log ((n : ℝ) / ((u : ℝ) + v)) := by
  by_cases hz : u + v = 0
  · have hu : u = 0 := by omega
    have hv : v = 0 := by omega
    subst u; subst v
    simp only [partsEntropy_partition_empty, signedEntropy_empty, Nat.cast_zero,
      zero_mul, add_zero]
  · have hp : (0 : ℝ) < (u : ℝ) + v := by
      exact_mod_cast Nat.pos_of_ne_zero hz
    rw [partsEntropy_change_total (B := (n : ℝ)) hp (by exact_mod_cast hn) α.1.rowLens,
      partsEntropy_change_total (B := (n : ℝ)) hp (by exact_mod_cast hn) β.1.rowLens]
    have he : signedEntropy α β =
        partsEntropy ((u : ℝ) + v) α.1.rowLens + partsEntropy ((u : ℝ) + v) β.1.rowLens := by
      simp only [signedEntropy, partsEntropy, List.map_append, List.sum_append]
    rw [he, partition_rowLens_sum, partition_rowLens_sum]
    ring

lemma split_entropy_le_remainder {N L n : ℝ} (hN : 0 ≤ N) (hL : 0 ≤ L)
    (hn : 0 < n) (hs : N + L = n) :
    N * Real.log (n / N) ≤ L := by
  rcases eq_or_lt_of_le hN with hz | hp
  · simp only [← hz, zero_mul]; exact hL
  · have ht := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos (div_pos hn hp)) hp.le
    have hcan : N * (n / N - 1) = L := by field_simp; nlinarith
    exact ht.trans_eq hcan

lemma signedOccurrence_dimension {u v l n : ℕ} {h : u + v + l = n}
    {α : Partition u} {β : Partition v} {γ : Partition l} {lam : Partition n}
    (hn : 0 < n) (ho : SignedOccurrence h α β γ lam) :
    (spechtDimension lam : ℝ) ≤
      Real.exp (signedEntropy α β + (l : ℝ) * Real.log ((n : ℝ) / l) + l) *
        spechtDimension γ := by
  classical
  let _ := specht_irreducible lam
  obtain ⟨f, hf, hstable⟩ := signedOccurrence_colorCarrier ho
  have he := finrank_le_coloring_entropy (spechtRepresentation lam) f hf
    (blockColoring h α.rowIndex β.transpose.colIndex) hstable
    (signedColorProbability α β l n) (signedColorProbability_nonneg α β l n)
    (signedColorProbability_sum h hn α β) (signedColorProbability_used_pos h hn α β)
  rw [signedColorProbability_entropy h α β, signedEntropy_change_total hn α β] at he
  apply he.trans
  apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg (spechtDimension γ))
  apply Real.exp_le_exp.mpr
  have hs : (u : ℝ) + v + l = (n : ℝ) := by exact_mod_cast h
  have ht := split_entropy_le_remainder (N := (u : ℝ) + v) (by positivity)
    (Nat.cast_nonneg l) (by exact_mod_cast hn) hs
  linarith

lemma spechtDimension_le_factorial {n : ℕ} (lam : Partition n) :
    spechtDimension lam ≤ n.factorial := by
  classical
  have hb := Submodule.finrank_le (spechtSubrepresentation lam).toSubmodule
  change spechtDimension lam ≤ finrank ℂ (EuclideanSpace ℂ (SymmetricGroup n)) at hb
  simpa only [finrank_euclideanSpace, SymmetricGroup, Fintype.card_perm, Fintype.card_fin] using hb

lemma spechtDimension_le_exp_size_log_size {n : ℕ} (lam : Partition n) :
    (spechtDimension lam : ℝ) ≤ Real.exp ((n : ℝ) * Real.log n) := by
  by_cases hn : n = 0
  · subst n
    simp only [spechtDimension_empty, Nat.cast_one, Nat.cast_zero, zero_mul, Real.exp_zero, le_refl]
  · rw [Real.exp_nat_mul, Real.exp_log (by exact_mod_cast Nat.pos_of_ne_zero hn)]
    exact_mod_cast (spechtDimension_le_factorial lam).trans (Nat.factorial_le_pow n)

lemma signedOccurrence_log_dimension {u v l n : ℕ} {h : u + v + l = n}
    {α : Partition u} {β : Partition v} {γ : Partition l} {lam : Partition n}
    (hn : 0 < n) (ho : SignedOccurrence h α β γ lam) :
    Real.log (spechtDimension lam : ℝ) ≤ signedEntropy α β + (l : ℝ) * Real.log n + l := by
  have hb := signedOccurrence_dimension hn ho
  have hc := mul_le_mul_of_nonneg_left (spechtDimension_le_exp_size_log_size γ)
    (Real.exp_pos (signedEntropy α β + (l : ℝ) * Real.log ((n : ℝ) / l) + l)).le
  have he : signedEntropy α β + (l : ℝ) * Real.log ((n : ℝ) / l) + l +
      (l : ℝ) * Real.log l = signedEntropy α β + (l : ℝ) * Real.log n + l := by
    by_cases hl : l = 0
    · simp [hl]
    · rw [Real.log_div (by exact_mod_cast hn.ne') (by exact_mod_cast hl)]
      ring
  have ht := hb.trans hc
  rw [← Real.exp_add, he] at ht
  exact (Real.log_le_iff_le_exp (by exact_mod_cast spechtDimension_pos lam)).mpr ht

end SignedSweeps
end

end OAI
