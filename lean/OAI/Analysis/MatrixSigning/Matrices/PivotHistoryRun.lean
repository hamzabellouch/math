import Mathlib
import OAI.Analysis.MatrixSigning.Matrices.DenseRatMatrix
import OAI.Analysis.MatrixSigning.Matrices.PivotHistory

namespace OAI

section

namespace KS.W07

structure PivotSnapshot (N : ℕ) where
  selectedCount : ℕ
  remainingCount : ℕ
  selected : Fin selectedCount → Fin N
  remaining : Fin remainingCount → Fin N
  matrix : DenseRatMatrix remainingCount

def initialPivotSnapshot {N : ℕ} (A : DenseRatMatrix N) : PivotSnapshot N :=
  ⟨0, N, (fun i => Fin.elim0 i), id, A⟩

def nextPivotSnapshot {N : ℕ} : PivotSnapshot N → PivotSnapshot N
  | ⟨k, 0, p, r, A⟩ => ⟨k, 0, p, r, A⟩
  | ⟨k, t + 1, p, r, A⟩ =>
    let S := DenseRatMatrix.decode A
    let B := DenseRatMatrix.ofMatrix (KS.W17.schurTail S)
    if S 0 0 = 0 then
      ⟨k, t, p, (fun i => r i.succ), B⟩
    else
      ⟨k + 1, t, Fin.snoc p (r 0), (fun i => r i.succ), B⟩

def ldlHistory {N : ℕ} (A : DenseRatMatrix N) : ℕ → PivotSnapshot N
  | 0 => initialPivotSnapshot A
  | s + 1 => nextPivotSnapshot (ldlHistory A s)

def SnapshotValid {N : ℕ} (M : Matrix (Fin N) (Fin N) ℚ) (s : PivotSnapshot N) : Prop :=
  PivotTrace M s.selected s.remaining (DenseRatMatrix.decode s.matrix)

theorem SnapshotValid.next {N : ℕ} {M : Matrix (Fin N) (Fin N) ℚ}
    {s : PivotSnapshot N} (h : SnapshotValid M s)
    (hM : (M.map (fun q : ℚ => (q : ℝ))).PosSemidef) :
    SnapshotValid M (nextPivotSnapshot s) := by
  rcases s with ⟨k, t, p, r, A⟩
  cases t with
  | zero => exact h
  | succ t =>
    change PivotTrace M p r (DenseRatMatrix.decode A) at h
    simp only [nextPivotSnapshot]
    split_ifs with hz
    · simpa only [SnapshotValid,DenseRatMatrix.decode_ofMatrix] using PivotTrace.zero h hz
    · have hS := h.state_posSemidef hM
      have ha0 : 0 ≤ DenseRatMatrix.decode A 0 0 := by
        have hdiag := hS.diag_nonneg (i := (0 : Fin (t + 1)))
        simp only [Matrix.map_apply] at hdiag
        exact_mod_cast hdiag
      have hpos : 0 < DenseRatMatrix.decode A 0 0 := lt_of_le_of_ne ha0 (Ne.symm hz)
      simpa only [SnapshotValid,DenseRatMatrix.decode_ofMatrix] using PivotTrace.positive h hpos

theorem ldlHistory_valid {N : ℕ} (A : DenseRatMatrix N)
    (hA : ((DenseRatMatrix.decode A).map (fun q : ℚ => (q : ℝ))).PosSemidef)
    (steps : ℕ) : SnapshotValid (DenseRatMatrix.decode A) (ldlHistory A steps) := by
  induction steps with
  | zero => exact PivotTrace.initial
  | succ steps ih => exact ih.next hA

theorem ldlHistory_originalSchur {N : ℕ} (A : DenseRatMatrix N)
    (hA : ((DenseRatMatrix.decode A).map (fun q : ℚ => (q : ℝ))).PosSemidef)
    (steps : ℕ) :
    let s := ldlHistory A steps
    ((DenseRatMatrix.decode A).submatrix s.selected s.selected).det ≠ 0 ∧
      DenseRatMatrix.decode s.matrix =
        selectedSchur (DenseRatMatrix.decode A) s.selected s.remaining := by
  exact (ldlHistory_valid A hA steps : PivotTrace (DenseRatMatrix.decode A)
    (ldlHistory A steps).selected (ldlHistory A steps).remaining
    (DenseRatMatrix.decode (ldlHistory A steps).matrix)).originalSchur

theorem ldlHistory_size_bound {N : ℕ} (A : DenseRatMatrix N)
    (hA : ((DenseRatMatrix.decode A).map (fun q : ℚ => (q : ℝ))).PosSemidef)
    (steps : ℕ) :
    (ldlHistory A steps).selectedCount + (ldlHistory A steps).remainingCount ≤ N := by
  exact (ldlHistory_valid A hA steps : PivotTrace (DenseRatMatrix.decode A)
    (ldlHistory A steps).selected (ldlHistory A steps).remaining
    (DenseRatMatrix.decode (ldlHistory A steps).matrix)).size_bound

theorem ldlHistory_entry_minor_ratio {N : ℕ} (A : DenseRatMatrix N)
    (hA : ((DenseRatMatrix.decode A).map (fun q : ℚ => (q : ℝ))).PosSemidef)
    (steps : ℕ) (i j : Fin (ldlHistory A steps).remainingCount) :
    let s := ldlHistory A steps
    DenseRatMatrix.decode s.matrix i j =
      ((DenseRatMatrix.decode A).submatrix (Fin.snoc s.selected (s.remaining i))
        (Fin.snoc s.selected (s.remaining j))).det /
      ((DenseRatMatrix.decode A).submatrix s.selected s.selected).det := by
  exact (ldlHistory_valid A hA steps : PivotTrace (DenseRatMatrix.decode A)
    (ldlHistory A steps).selected (ldlHistory A steps).remaining
    (DenseRatMatrix.decode (ldlHistory A steps).matrix)).entry_minor_ratio i j

end KS.W07

end

end OAI
