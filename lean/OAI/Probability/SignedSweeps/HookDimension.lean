import OAI.Probability.SignedSweeps.ExactRowDimension
import OAI.Probability.SignedSweeps.BetaNumbers

namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators Classical

def cellHookProduct (lam : YoungDiagram) : ℕ :=
  ∏ c ∈ lam.cells, boxHook lam c.1 c.2

lemma prod_cells_by_rows {M : Type*} [CommMonoid M] (lam : YoungDiagram)
    (f : ℕ → ℕ → M) :
    (∏ c ∈ lam.cells, f c.1 c.2) =
      ∏ i : Fin (lam.colLen 0), ∏ j ∈ Finset.range (lam.rowLen i), f i j := by
  let μ : Partition lam.card := ⟨lam, rfl⟩
  rw [← Finset.prod_coe_sort]
  have ht := Fintype.prod_equiv μ.tableau (fun c => f c.1.1 c.1.2)
    (fun x => f (μ.rowOf x) (μ.colOf x)) (by intro c; simp [Partition.rowOf, Partition.colOf])
  rw [ht, ← μ.rowEquiv.prod_comp, Fintype.prod_sigma]
  simp only [Partition.rowOf_rowEquiv, Partition.colOf_rowEquiv]
  apply Finset.prod_congr rfl
  intro i _
  exact Fin.prod_univ_eq_prod_range (f i) _

lemma cellHookProduct_eq_rows (lam : YoungDiagram) :
    cellHookProduct lam = diagramHookProduct (lam.colLen 0) lam := by
  exact prod_cells_by_rows lam (boxHook lam)

lemma cellHookProduct_pos (lam : YoungDiagram) : 0 < cellHookProduct lam := by
  rw [cellHookProduct_eq_rows]
  exact diagramHookProduct_pos _ _

theorem factorial_le_dimension_mul_hooks {n : ℕ} (lam : Partition n) :
    (Nat.factorial n : ℝ) ≤ (spechtDimension lam : ℝ) * cellHookProduct lam.1 := by
  let q := lam.1.colLen 0
  have hd := tableauDegree_le_dimension n q lam le_rfl
  have hp := hookProduct_vandermonde lam.1 (le_refl q)
  have hv := nodeVandermonde_pos _ (shiftedRealRows_strictAnti q lam.1)
  have hh := diagramHookProduct_pos q lam.1
  unfold tableauDegree at hd
  rw [← hp] at hd
  have he : (Nat.factorial n : ℝ) *
      nodeVandermonde (fun i : Fin q => (shiftedRowNodes q lam.1 i : ℝ)) /
      ((diagramHookProduct q lam.1 : ℝ) *
        nodeVandermonde (fun i : Fin q => (shiftedRowNodes q lam.1 i : ℝ))) =
      (Nat.factorial n : ℝ) / diagramHookProduct q lam.1 := by
    field_simp
  rw [he, div_le_iff₀ (by exact_mod_cast hh)] at hd
  simpa only [cellHookProduct_eq_rows] using hd

lemma boxHook_transpose (lam : YoungDiagram) (i j : ℕ) :
    boxHook lam.transpose i j = boxHook lam j i := by
  simp only [boxHook, YoungDiagram.rowLen_transpose, YoungDiagram.colLen_transpose]
  omega

lemma cellHookProduct_transpose (lam : YoungDiagram) :
    cellHookProduct lam.transpose = cellHookProduct lam := by
  change (∏ c ∈ lam.transpose.cells, boxHook lam.transpose c.1 c.2) = _
  rw [show lam.transpose.cells = lam.cells.map (Equiv.prodComm ℕ ℕ).toEmbedding from rfl,
    Finset.prod_map]
  simp only [Equiv.coe_toEmbedding, Equiv.prodComm_apply, Prod.swap,
    boxHook_transpose, cellHookProduct]

end SignedSweeps
end

end OAI
