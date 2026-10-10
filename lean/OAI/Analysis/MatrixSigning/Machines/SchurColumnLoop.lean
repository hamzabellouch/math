import Mathlib
import OAI.Analysis.MatrixSigning.Complexity.SchurCellCost
import OAI.Analysis.MatrixSigning.Machines.SchurTableInvariant
import OAI.Analysis.MatrixSigning.Potential.SchurLoopState

namespace OAI

section

namespace KS.W07.SchurLoopState
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators

def columnBudget (n B : ℕ) : ℕ := 4096*(n+2)^2*(B+1) +
  SchurCellMachine.cellBudget B + 200*(n+B+3)

theorem columnTicks_le {n : ℕ} (M : DenseRatMatrix (n+1)) (B : ℕ)
    (hnum : ∀ i j, (DenseRatMatrix.decode M i j).num.natAbs ≤ 2^B)
    (hden : ∀ i j, (DenseRatMatrix.decode M i j).den ≤ 2^B)
    (i j : Fin n) (rows cols : ℕ) : columnTicks M B i j rows cols ≤ columnBudget n B := by
  have hlen (q : ℚ) (hn : q.num.natAbs ≤ 2^B) (hd : q.den ≤ 2^B) :
      KS.W01.ratLength q ≤ 4*B+7 := by
    have h := KS.W01.ratLength_le_of_parts q B B hn hd
    omega
  have lx := hlen _ (hnum i.succ j.succ) (hden i.succ j.succ)
  have la := hlen _ (hnum i.succ 0) (hden i.succ 0)
  have lb := hlen _ (hnum 0 j.succ) (hden 0 j.succ)
  have lc := hlen _ (hnum 0 0) (hden 0 0)
  have hs := SchurCellMachine.ticks_le_cellBudget
    (DenseRatMatrix.decode M i.succ j.succ) (DenseRatMatrix.decode M i.succ 0)
    (DenseRatMatrix.decode M 0 j.succ) (DenseRatMatrix.decode M 0 0) B
    ⟨hnum i.succ j.succ,hden i.succ j.succ⟩ ⟨hnum i.succ 0,hden i.succ 0⟩
    ⟨hnum 0 j.succ,hden 0 j.succ⟩ ⟨hnum 0 0,hden 0 0⟩
  have hq := SchurTable.entry_parts_le M B hnum hden i j
  have lq := KS.W01.ratLength_le_of_parts _ (4*B+3) (4*B+3) hq.1 hq.2
  have rawLength (t : ℕ) : (Computability.encodeNat t).length ≤ t := by
    change KS.W01.natPayloadLength t ≤ t
    rw [KS.W01.natPayloadLength_eq_size]
    exact Nat.size_le.mpr Nat.lt_two_pow_self
  have ln := rawLength (n+1)
  have li : (Computability.encodeNat (i.val+1)).length ≤ n+1 :=
    (rawLength (i.val+1)).trans (by omega)
  have lj : (Computability.encodeNat (j.val+1)).length ≤ n+1 :=
    (rawLength (j.val+1)).trans (by omega)
  have hread : 4096*(n+2)^2*(B+1) = 4*(1024*(n+2)^2*(B+1)) := by ring
  unfold columnTicks SchurOperands.readBudget SchurReadStage.prepareTicks columnBudget
  rw [hread]
  simp only [columnState,SchurReadStage.rowSource,SchurReadStage.colSource,
    Bool.false_eq_true,ite_false,ite_true,Fin.isValue,Fin.reduceEq,List.length_nil]
  omega

theorem column_body_polynomial {n : ℕ} (M : DenseRatMatrix (n+1)) (B : ℕ)
    (hnum : ∀ i j, (DenseRatMatrix.decode M i j).num.natAbs ≤ 2^B)
    (hden : ∀ i j, (DenseRatMatrix.decode M i j).den ≤ 2^B)
    (i j : Fin n) (rows cols : ℕ) :
    RunSpec SchurTableMachine.columnBody (columnState M i.val j.val rows cols)
      (columnState M i.val (j.val+1) rows cols) (columnBudget n B) :=
  (column_body_spec M B hnum hden i j rows cols).mono (columnTicks_le M B hnum hden i j rows cols)

theorem run_columns {n : ℕ} (M : DenseRatMatrix (n+1)) (B : ℕ)
    (hnum : ∀ i j, (DenseRatMatrix.decode M i j).num.natAbs ≤ 2^B)
    (hden : ∀ i j, (DenseRatMatrix.decode M i j).den ≤ 2^B)
    (i : Fin n) (rows start count : ℕ) (hcount : start+count=n)
    (bits : List Bool) (hlen : count*(columnBudget n B+1)+1 ≤ bits.length) :
    SchurTableMachine.columnLoop.toMachine.run
      ⟨some SchurTableMachine.columnLoop.initial,columnState M i.val start rows count⟩ bits =
      ⟨none,columnState M i.val n rows 0⟩ := by
  induction count generalizing start bits with
  | zero =>
    have hstart : start=n := by omega
    subst start
    cases bits with
    | nil => simp at hlen
    | cons coin rest =>
      have hg : SchurTableMachine.columnLoop.toMachine.step
          ⟨some SchurTableMachine.columnLoop.initial,columnState M i.val n rows 0⟩ coin =
          ⟨none,columnState M i.val n rows 0⟩ := by
        simpa only [SchurTableMachine.columnLoop,KS.W29.FixedLoop.loop_initial] using
          SchurTableMachine.guard_empty SchurTableMachine.columnBody 25
            (columnState M i.val n rows 0) rfl coin
      rw [Machine.run,hg,Machine.run_halted _ _ rfl]
  | succ count ih =>
    have hstart : start<n := by omega
    let j : Fin n := ⟨start,hstart⟩
    cases bits with
    | nil => simp at hlen
    | cons coin rest =>
      have hb := column_body_polynomial M B hnum hden i j rows count
      have hr : columnBudget n B ≤ rest.length := by
        simp only [List.length_cons,Nat.succ_mul] at hlen
        omega
      obtain ⟨remaining,hremaining,hreturn⟩ := hb.loop_body_then
        (SchurTableMachine.guard 25) rest hr
      have hstep := SchurTableMachine.guard_cons SchurTableMachine.columnBody 25
        (columnState M i.val start rows (count+1)) (List.replicate count true)
        (by simp [columnState,List.replicate_succ]) coin
      rw [column_pop] at hstep
      simp only [SchurTableMachine.columnLoop,KS.W29.FixedLoop.loop_initial]
      rw [Machine.run,hstep,hreturn]
      have hnext : (start+1)+count=n := by omega
      have hnextlen : count*(columnBudget n B+1)+1 ≤ remaining.length := by
        simp only [List.length_cons,Nat.succ_mul] at hlen
        omega
      simpa only [SchurTableMachine.columnLoop,KS.W29.FixedLoop.loop_initial] using
        ih (start+1) hnext remaining hnextlen

theorem columns_spec {n : ℕ} (M : DenseRatMatrix (n+1)) (B : ℕ)
    (hnum : ∀ i j, (DenseRatMatrix.decode M i j).num.natAbs ≤ 2^B)
    (hden : ∀ i j, (DenseRatMatrix.decode M i j).den ≤ 2^B) (i : Fin n) (rows : ℕ) :
    RunSpec SchurTableMachine.columnLoop (columnState M i.val 0 rows n)
      (columnState M i.val n rows 0) (n*(columnBudget n B+1)+1) := by
  intro bits hbits
  exact run_columns M B hnum hden i rows 0 n (by omega) bits hbits.ge

end KS.W07.SchurLoopState

end

end OAI
