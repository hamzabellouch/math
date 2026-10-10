import Mathlib
import OAI.Analysis.MatrixSigning.Machines.SchurColumnLoop

namespace OAI

section

namespace KS.W07.SchurLoopState
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators

def rowTicks (n B i : ℕ) : ℕ := (4*n+6*(Computability.encodeNat n).length+4) +
  (1 + ((n*(columnBudget n B+1)+1) +
    (((Computability.encodeNat (n+1)).length+1) +
      (2*(Computability.encodeNat (i+1)).length+6))))

def rowBudget (n B : ℕ) : ℕ := n*(columnBudget n B+1)+20*(n+2)

theorem row_body_spec {n : ℕ} (M : DenseRatMatrix (n+1)) (B : ℕ)
    (hnum : ∀ i j, (DenseRatMatrix.decode M i j).num.natAbs ≤ 2^B)
    (hden : ∀ i j, (DenseRatMatrix.decode M i j).den ≤ 2^B)
    (i : Fin n) (rows : ℕ) :
    RunSpec SchurTableMachine.rowBody (rowState M i.val rows)
      (rowState M (i.val+1) rows) (rowTicks n B i.val) := by
  let s := rowState M i.val rows
  let u := Function.update s 25 (List.replicate n true)
  have hu := SchurDimension.unary_spec true s n rfl rfl rfl rfl rfl
  have hp := SchurCounters.push_spec (28 : Fin 32) true u
  have hone : Computability.encodeNat 1 = [true] := by decide
  have hstart : Function.update u 28 (true::u 28) = columnState M i.val 0 rows n := by
    funext k; fin_cases k <;> simp [u,s,columnState,rowState,hone]
  rw [hstart] at hp
  have hc := columns_spec M B hnum hden i rows
  let v := Function.update (columnState M i.val n rows 0) 28 []
  have hclear := KS.W15.RationalMultiply.clear_spec (28 : Fin 32)
    (columnState M i.val n rows 0)
  have hclearState : KS.W15.RationalMultiply.clearAfter 28
      (columnState M i.val n rows 0) = v := by
    funext k
    by_cases hk : k=28 <;> simp [KS.W15.RationalMultiply.clearAfter,v,hk]
  rw [hclearState] at hclear
  have hi := SchurCounters.increment_spec SchurTableMachine.rowIncrementPorts v
    (i.val+1) rfl rfl rfl
  have hout : Function.update v 27 (Computability.encodeNat (i.val+1+1)) =
      rowState M (i.val+1) rows := by
    funext k; fin_cases k <;> simp [v,columnState,rowState,Nat.add_mul]
  change RunSpec (SchurCounters.incrementProgram SchurTableMachine.rowIncrementPorts) v
    (Function.update v 27 (Computability.encodeNat (i.val+1+1))) _ at hi
  rw [hout] at hi
  exact hu.compose (hp.compose (hc.compose (hclear.compose hi)))

theorem rowTicks_le {n : ℕ} (B : ℕ) (i : Fin n) : rowTicks n B i.val ≤ rowBudget n B := by
  have rawLength (t : ℕ) : (Computability.encodeNat t).length ≤ t := by
    change KS.W01.natPayloadLength t ≤ t
    rw [KS.W01.natPayloadLength_eq_size]
    exact Nat.size_le.mpr Nat.lt_two_pow_self
  have ln := rawLength n
  have ln' := rawLength (n+1)
  have li : (Computability.encodeNat (i.val+1)).length ≤ n+1 :=
    (rawLength (i.val+1)).trans (by omega)
  unfold rowTicks rowBudget
  omega

theorem row_body_polynomial {n : ℕ} (M : DenseRatMatrix (n+1)) (B : ℕ)
    (hnum : ∀ i j, (DenseRatMatrix.decode M i j).num.natAbs ≤ 2^B)
    (hden : ∀ i j, (DenseRatMatrix.decode M i j).den ≤ 2^B)
    (i : Fin n) (rows : ℕ) :
    RunSpec SchurTableMachine.rowBody (rowState M i.val rows)
      (rowState M (i.val+1) rows) (rowBudget n B) :=
  (row_body_spec M B hnum hden i rows).mono (rowTicks_le B i)

theorem run_rows {n : ℕ} (M : DenseRatMatrix (n+1)) (B : ℕ)
    (hnum : ∀ i j, (DenseRatMatrix.decode M i j).num.natAbs ≤ 2^B)
    (hden : ∀ i j, (DenseRatMatrix.decode M i j).den ≤ 2^B)
    (start count : ℕ) (hcount : start+count=n) (bits : List Bool)
    (hlen : count*(rowBudget n B+1)+1 ≤ bits.length) :
    SchurTableMachine.rowLoop.toMachine.run
      ⟨some SchurTableMachine.rowLoop.initial,rowState M start count⟩ bits =
      ⟨none,rowState M n 0⟩ := by
  induction count generalizing start bits with
  | zero =>
    have hstart : start=n := by omega
    subst start
    cases bits with
    | nil => simp at hlen
    | cons coin rest =>
      have hg : SchurTableMachine.rowLoop.toMachine.step
          ⟨some SchurTableMachine.rowLoop.initial,rowState M n 0⟩ coin =
          ⟨none,rowState M n 0⟩ := by
        simpa only [SchurTableMachine.rowLoop,KS.W29.FixedLoop.loop_initial] using
          SchurTableMachine.guard_empty SchurTableMachine.rowBody 24
            (rowState M n 0) rfl coin
      rw [Machine.run,hg,Machine.run_halted _ _ rfl]
  | succ count ih =>
    have hstart : start<n := by omega
    let i : Fin n := ⟨start,hstart⟩
    cases bits with
    | nil => simp at hlen
    | cons coin rest =>
      have hb := row_body_polynomial M B hnum hden i count
      have hr : rowBudget n B ≤ rest.length := by
        simp only [List.length_cons,Nat.succ_mul] at hlen
        omega
      obtain ⟨remaining,hremaining,hreturn⟩ := hb.loop_body_then
        (SchurTableMachine.guard 24) rest hr
      have hstep := SchurTableMachine.guard_cons SchurTableMachine.rowBody 24
        (rowState M start (count+1)) (List.replicate count true)
        (by simp [rowState,List.replicate_succ]) coin
      rw [row_pop] at hstep
      simp only [SchurTableMachine.rowLoop,KS.W29.FixedLoop.loop_initial]
      rw [Machine.run,hstep,hreturn]
      have hnext : (start+1)+count=n := by omega
      have hnextlen : count*(rowBudget n B+1)+1 ≤ remaining.length := by
        simp only [List.length_cons,Nat.succ_mul] at hlen
        omega
      simpa only [SchurTableMachine.rowLoop,KS.W29.FixedLoop.loop_initial] using
        ih (start+1) hnext remaining hnextlen

theorem rows_spec {n : ℕ} (M : DenseRatMatrix (n+1)) (B : ℕ)
    (hnum : ∀ i j, (DenseRatMatrix.decode M i j).num.natAbs ≤ 2^B)
    (hden : ∀ i j, (DenseRatMatrix.decode M i j).den ≤ 2^B) :
    RunSpec SchurTableMachine.rowLoop (rowState M 0 n) (rowState M n 0)
      (n*(rowBudget n B+1)+1) := by
  intro bits hbits
  exact run_rows M B hnum hden 0 n (by omega) bits hbits.ge

end KS.W07.SchurLoopState

end

end OAI
