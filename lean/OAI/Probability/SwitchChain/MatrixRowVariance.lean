import OAI.Probability.SwitchChain.ForcedColumns
import OAI.Probability.SwitchChain.BalancedBlockVariance

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace Problem315.MatrixRowVariance

variable {C : Type*} [Fintype C]

def positive (k : C → ℕ) (r : Fin 3 → ℕ) (i : Fin 3) : ℕ :=
  (r i - ForcedColumns.offset k) - Fintype.card (ForcedColumns.Two k)

def negative (k : C → ℕ) (r : Fin 3 → ℕ) (i : Fin 3) : ℕ :=
  Fintype.card (ForcedColumns.Two k) - (r i - ForcedColumns.offset k)

theorem offset_separated (k : C → ℕ) (r : Fin 3 → ℕ) (i : Fin 3) :
    positive k r i = 0 ∨ negative k r i = 0 := by
  unfold positive negative
  omega

theorem coloring_constraints_iff (k : C → ℕ) (r : Fin 3 → ℕ)
    (c : (ForcedColumns.One k → Fin 3) × (ForcedColumns.Two k → Fin 3)) :
    (∀ i, (FixedBlock.row c.1 i).card + Fintype.card (ForcedColumns.Two k) =
      (r i - ForcedColumns.offset k) + (FixedBlock.row c.2 i).card) ↔
    (∀ i, (FixedBlock.row c.1 i).card + negative k r i =
      (FixedBlock.row c.2 i).card + positive k r i) := by
  constructor <;> intro h i
  · have hi := h i
    unfold positive negative
    omega
  · have hi := h i
    unfold positive negative at hi
    omega

def coloringsBalanceEquiv (k : C → ℕ) (r : Fin 3 → ℕ) :
    ForcedColumns.Colorings k r ≃
      BalancedBlockVariance.Balanced (ForcedColumns.One k) (ForcedColumns.Two k)
        (positive k r) (negative k r) :=
  Equiv.subtypeEquivRight (coloring_constraints_iff k r)

def fullBalanceEquiv (k : C → ℕ) (r : Fin 3 → ℕ)
    (h : Nonempty (ForcedColumns.FullMargins k r)) :
    ForcedColumns.FullMargins k r ≃
      BalancedBlockVariance.Balanced (ForcedColumns.One k) (ForcedColumns.Two k)
        (positive k r) (negative k r) :=
  (ForcedColumns.coloringEquiv k r h).trans (coloringsBalanceEquiv k r)

theorem fullBalance_row_eq_iff (k : C → ℕ) (r : Fin 3 → ℕ)
    (h : Nonempty (ForcedColumns.FullMargins k r))
    (M N : ForcedColumns.FullMargins k r) (i : Fin 3) :
    M.val i = N.val i ↔
      FixedBlock.row (fullBalanceEquiv k r h M).val.1 i =
        FixedBlock.row (fullBalanceEquiv k r h N).val.1 i ∧
      FixedBlock.row (fullBalanceEquiv k r h M).val.2 i =
        FixedBlock.row (fullBalanceEquiv k r h N).val.2 i := by
  exact ForcedColumns.coloring_row_eq_iff k r h M N i

theorem row_variance_bound (k : C → ℕ) (r : Fin 3 → ℕ)
    (h : Nonempty (ForcedColumns.FullMargins k r))
    (f : Fin 3 → ForcedColumns.FullMargins k r → ℝ)
    (hf : ∀ i M N, M.val i = N.val i → f i M = f i N) :
    FiniteVariance.variance (fun M => ∑ i, f i M) ≤
      2 * ∑ i, FiniteVariance.variance (f i) := by
  let B := BalancedBlockVariance.Balanced (ForcedColumns.One k) (ForcedColumns.Two k)
    (positive k r) (negative k r)
  let e : ForcedColumns.FullMargins k r ≃ B := fullBalanceEquiv k r h
  let : Nonempty B := h.map e
  let key (i : Fin 3) (c : B) :=
    (FixedBlock.row c.val.1 i, FixedBlock.row c.val.2 i)
  have hfac (i : Fin 3) :
      Function.FactorsThrough (fun c : B => f i (e.symm c)) (key i) := by
    intro c d hcd
    apply hf i
    apply (fullBalance_row_eq_iff k r h (e.symm c) (e.symm d) i).mpr
    change FixedBlock.row (e (e.symm c)).val.1 i =
      FixedBlock.row (e (e.symm d)).val.1 i ∧
      FixedBlock.row (e (e.symm c)).val.2 i =
      FixedBlock.row (e (e.symm d)).val.2 i
    rw [e.apply_symm_apply, e.apply_symm_apply]
    exact ⟨congrArg Prod.fst hcd, congrArg Prod.snd hcd⟩
  obtain ⟨g, hg⟩ : ∃ g : Fin 3 →
      (Finset (ForcedColumns.One k) × Finset (ForcedColumns.Two k)) → ℝ,
      ∀ i c, f i (e.symm c) = g i (key i c) := by
    have he (i : Fin 3) := (Function.factorsThrough_iff (fun c : B => f i (e.symm c))).mp
      (hfac i)
    choose g hg using he
    exact ⟨g, fun i c => congrFun (hg i) c⟩
  have hv := BalancedBlockVariance.row_variance_bound
    (positive k r) (negative k r) (offset_separated k r)
    (fun i s t => g i (s, t))
  have heq (F : ForcedColumns.FullMargins k r → ℝ) :
      FiniteVariance.variance (fun c : B => F (e.symm c)) = FiniteVariance.variance F :=
    FiniteVariance.variance_equiv e.symm F
  rw [← heq (fun M => ∑ i, f i M)]
  simp_rw [← heq (f _)]
  simp_rw [hg]
  exact hv

end Problem315.MatrixRowVariance

end

end OAI
