import OAI.Probability.SignedSweeps.ShiftedRows

namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators Classical

def boxHook (lam : YoungDiagram) (i j : ℕ) : ℕ :=
  lam.rowLen i - j + (lam.colLen j - i) - 1

lemma boxHook_pos (lam : YoungDiagram) {i j : ℕ} (h : (i,j) ∈ lam) :
    0 < boxHook lam i j := by
  have hr := YoungDiagram.mem_iff_lt_rowLen.mp h
  have hc := YoungDiagram.mem_iff_lt_colLen.mp h
  unfold boxHook
  omega

def columnEndNode (q : ℕ) (lam : YoungDiagram) (j : ℕ) : ℕ :=
  j + (q - lam.colLen j)

lemma columnEndNode_strictMono (q : ℕ) (lam : YoungDiagram) :
    StrictMono (columnEndNode q lam) := by
  intro a b hab
  have h := lam.colLen_anti a b hab.le
  unfold columnEndNode
  omega

lemma columnEndNode_lt_shiftedRow {q : ℕ} (lam : YoungDiagram)
    (hq : lam.colLen 0 ≤ q) (i : Fin q) {j : ℕ} (hj : j < lam.rowLen i) :
    columnEndNode q lam j < shiftedRowNodes q lam i := by
  have hm : (i.val,j) ∈ lam := YoungDiagram.mem_iff_lt_rowLen.mpr hj
  have hc := YoungDiagram.mem_iff_lt_colLen.mp hm
  have hqj := (lam.colLen_anti 0 j (Nat.zero_le j)).trans hq
  unfold columnEndNode shiftedRowNodes
  omega

lemma columnEndNode_ne_shiftedRow {q : ℕ} (lam : YoungDiagram)
    (hq : lam.colLen 0 ≤ q) (i : Fin q) (j : ℕ) :
    columnEndNode q lam j ≠ shiftedRowNodes q lam i := by
  by_cases hj : j < lam.rowLen i
  · exact ne_of_lt (columnEndNode_lt_shiftedRow lam hq i hj)
  · have hc : lam.colLen j ≤ i.val := by
      by_contra h
      have hm : (i.val,j) ∈ lam := YoungDiagram.mem_iff_lt_colLen.mpr (Nat.lt_of_not_ge h)
      exact hj (YoungDiagram.mem_iff_lt_rowLen.mp hm)
    unfold columnEndNode shiftedRowNodes
    omega

lemma shiftedRow_sub_columnEnd_hook {q : ℕ} (lam : YoungDiagram)
    (hq : lam.colLen 0 ≤ q) (i : Fin q) {j : ℕ} (hj : j < lam.rowLen i) :
    shiftedRowNodes q lam i - columnEndNode q lam j = boxHook lam i j := by
  have hc : i.val < lam.colLen j := YoungDiagram.mem_iff_lt_colLen.mp
    (YoungDiagram.mem_iff_lt_rowLen.mpr hj)
  have hqj := (lam.colLen_anti 0 j (Nat.zero_le j)).trans hq
  unfold shiftedRowNodes columnEndNode boxHook
  omega

lemma shiftedRow_range_decomposition {q : ℕ} (lam : YoungDiagram)
    (hq : lam.colLen 0 ≤ q) (i : Fin q) :
    Finset.range (shiftedRowNodes q lam i) =
      (Finset.range (lam.rowLen i)).image (columnEndNode q lam) ∪
        (Finset.Ioi i).image (shiftedRowNodes q lam) := by
  have hd : Disjoint ((Finset.range (lam.rowLen i)).image (columnEndNode q lam))
      ((Finset.Ioi i).image (shiftedRowNodes q lam)) := by
    rw [Finset.disjoint_left]
    intro x hx hy
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨b, hb, he⟩ := Finset.mem_image.mp hy
    exact columnEndNode_ne_shiftedRow lam hq b a he.symm
  symm
  apply Finset.eq_of_subset_of_card_le
  · intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
      exact Finset.mem_range.mpr (columnEndNode_lt_shiftedRow lam hq i (Finset.mem_range.mp hj))
    · obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hx
      exact Finset.mem_range.mpr ((shiftedRowNodes_strictAnti q lam) (Finset.mem_Ioi.mp hk))
  · rw [Finset.card_range, Finset.card_union_of_disjoint hd,
      Finset.card_image_of_injective _ (columnEndNode_strictMono q lam).injective,
      Finset.card_image_of_injective _ (shiftedRowNodes_strictAnti q lam).injective,
      Finset.card_range, Fin.card_Ioi]
    exact le_rfl

theorem row_hook_beta_factorial {q : ℕ} (lam : YoungDiagram)
    (hq : lam.colLen 0 ≤ q) (i : Fin q) :
    (∏ j ∈ Finset.range (lam.rowLen i), boxHook lam i j) *
      (∏ k ∈ (Finset.Ioi i : Finset (Fin q)), (shiftedRowNodes q lam i - shiftedRowNodes q lam k)) =
        (shiftedRowNodes q lam i).factorial := by
  have hd : Disjoint ((Finset.range (lam.rowLen i)).image (columnEndNode q lam))
      ((Finset.Ioi i).image (shiftedRowNodes q lam)) := by
    rw [Finset.disjoint_left]
    intro x hx hy
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨b, hb, he⟩ := Finset.mem_image.mp hy
    exact columnEndNode_ne_shiftedRow lam hq b a he.symm
  have hp : (shiftedRowNodes q lam i).factorial =
      ∏ t ∈ Finset.range (shiftedRowNodes q lam i), (shiftedRowNodes q lam i - t) := by
    rw [← Nat.descFactorial_eq_prod_range, Nat.descFactorial_self]
  rw [hp, shiftedRow_range_decomposition lam hq i, Finset.prod_union hd,
    Finset.prod_image (columnEndNode_strictMono q lam).injective.injOn,
    Finset.prod_image (shiftedRowNodes_strictAnti q lam).injective.injOn]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  exact (shiftedRow_sub_columnEnd_hook lam hq i (Finset.mem_range.mp hj)).symm

def diagramHookProduct (q : ℕ) (lam : YoungDiagram) : ℕ :=
  ∏ i : Fin q, ∏ j ∈ Finset.range (lam.rowLen i), boxHook lam i j

lemma diagramHookProduct_pos (q : ℕ) (lam : YoungDiagram) :
    0 < diagramHookProduct q lam := by
  exact Finset.prod_pos (fun i _ => Finset.prod_pos (fun j hj =>
    boxHook_pos lam (YoungDiagram.mem_iff_lt_rowLen.mpr (Finset.mem_range.mp hj))))

theorem hookProduct_vandermonde {q : ℕ} (lam : YoungDiagram)
    (hq : lam.colLen 0 ≤ q) :
    (diagramHookProduct q lam : ℝ) *
      nodeVandermonde (fun i => (shiftedRowNodes q lam i : ℝ)) =
        ∏ i : Fin q, ((shiftedRowNodes q lam i).factorial : ℝ) := by
  have ht (i : Fin q) : (∏ k : Fin q,
      if i < k then (shiftedRowNodes q lam i : ℝ) - shiftedRowNodes q lam k else 1) =
      ((∏ k ∈ (Finset.Ioi i : Finset (Fin q)), (shiftedRowNodes q lam i - shiftedRowNodes q lam k) : ℕ) : ℝ) := by
    rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.filter_lt_eq_Ioi, Nat.cast_prod]
    apply Finset.prod_congr rfl
    intro k hk
    rw [Nat.cast_sub ((shiftedRowNodes_strictAnti q lam) (Finset.mem_Ioi.mp hk)).le]
  unfold diagramHookProduct nodeVandermonde
  rw [Nat.cast_prod, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  rw [ht, ← Nat.cast_mul, row_hook_beta_factorial lam hq i]

end SignedSweeps
end

end OAI
