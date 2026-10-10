import Mathlib
import OAI.Analysis.MatrixSigning.Machines.SchurTableMachine

namespace OAI

section

namespace KS.W07.SchurLoopState
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators

def tailMatrix {n : ℕ} (M : DenseRatMatrix (n+1)) : DenseRatMatrix n :=
  DenseRatMatrix.ofMatrix (KS.W17.schurTail (DenseRatMatrix.decode M))

def «prefix» {n : ℕ} (M : DenseRatMatrix (n+1)) (s : ℕ) : List Bool :=
  ((KS.W08.denseMatrixPayloads (tailMatrix M)).take s).flatMap KS.W01.frame

@[simp] theorem prefix_zero {n : ℕ} (M : DenseRatMatrix (n+1)) : «prefix» M 0 = [] := by
  simp [«prefix»]

theorem prefix_complete {n : ℕ} (M : DenseRatMatrix (n+1)) :
    «prefix» M (n*n) = KS.W08.denseMatrixTape (tailMatrix M) := by
  simp only [«prefix»,KS.W08.denseMatrixTape]
  rw [List.take_of_length_le (KS.W08.denseMatrixPayloads_length (tailMatrix M)).le]

theorem prefix_step {n : ℕ} (M : DenseRatMatrix (n+1)) (i j : Fin n) :
    «prefix» M (i.val*n+j.val+1) = «prefix» M (i.val*n+j.val) ++
      KS.W01.frame (KS.W01.encodeRat (KS.W17.schurTail (DenseRatMatrix.decode M) i j)) := by
  unfold «prefix»
  rw [List.take_succ_eq_append_getElem (by
    rw [KS.W08.denseMatrixPayloads_length]
    exact KS.W08.matrixEntryIndex_lt i j),List.flatMap_append]
  rw [KS.W08.denseMatrixPayloads_get]
  simp [tailMatrix]

def columnState {n : ℕ} (M : DenseRatMatrix (n+1)) (r c rows cols : ℕ) : Fin 32 → List Bool :=
  fun j => if j=23 then («prefix» M (r*n+c)).reverse else
    if j=24 then List.replicate rows true else
    if j=25 then List.replicate cols true else
    if j=26 then Computability.encodeNat (n+1) else
    if j=27 then Computability.encodeNat (r+1) else
    if j=28 then Computability.encodeNat (c+1) else
    if j=30 then Computability.encodeNat n else
    if j=31 then KS.W08.denseMatrixTape M else []

def rowState {n : ℕ} (M : DenseRatMatrix (n+1)) (r rows : ℕ) : Fin 32 → List Bool :=
  fun j => if j=23 then («prefix» M (r*n)).reverse else
    if j=24 then List.replicate rows true else
    if j=26 then Computability.encodeNat (n+1) else
    if j=27 then Computability.encodeNat (r+1) else
    if j=30 then Computability.encodeNat n else
    if j=31 then KS.W08.denseMatrixTape M else []

theorem column_workClear {n : ℕ} (M : DenseRatMatrix (n+1)) (r c rows cols : ℕ) :
    SchurReadStage.WorkClear (columnState M r c rows cols) := by
  intro j hj
  have h23 : j≠23 := by intro h; subst j; omega
  have h24 : j≠24 := by intro h; subst j; omega
  have h25 : j≠25 := by intro h; subst j; omega
  have h26 : j≠26 := by intro h; subst j; omega
  have h27 : j≠27 := by intro h; subst j; omega
  have h28 : j≠28 := by intro h; subst j; omega
  have h30 : j≠30 := by intro h; subst j; omega
  have h31 : j≠31 := by intro h; subst j; omega
  simp [columnState,h23,h24,h25,h26,h27,h28,h30,h31]

def columnTicks {n : ℕ} (M : DenseRatMatrix (n+1)) (B : ℕ) (i j : Fin n) (rows cols : ℕ) : ℕ :=
  ((SchurOperands.readBudget M B i j (columnState M i.val j.val rows cols) +
    SchurCellMachine.ticks (DenseRatMatrix.decode M i.succ j.succ)
      (DenseRatMatrix.decode M i.succ 0) (DenseRatMatrix.decode M 0 j.succ)
      (DenseRatMatrix.decode M 0 0)) +
    (6*KS.W01.ratLength (KS.W17.schurTail (DenseRatMatrix.decode M) i j)+5)) +
    (2*(Computability.encodeNat (j.val+1)).length+6)

theorem column_body_spec {n : ℕ} (M : DenseRatMatrix (n+1)) (B : ℕ)
    (hnum : ∀ i j, (DenseRatMatrix.decode M i j).num.natAbs ≤ 2^B)
    (hden : ∀ i j, (DenseRatMatrix.decode M i j).den ≤ 2^B)
    (i j : Fin n) (rows cols : ℕ) :
    RunSpec SchurTableMachine.columnBody (columnState M i.val j.val rows cols)
      (columnState M i.val (j.val+1) rows cols) (columnTicks M B i j rows cols) := by
  let s := columnState M i.val j.val rows cols
  let wire := KS.W01.frame (KS.W01.encodeRat (KS.W17.schurTail (DenseRatMatrix.decode M) i j))
  have he := SchurEntryMachine.full_spec M B hnum hden i j s
    (column_workClear M _ _ _ _) rfl rfl rfl rfl rfl
    (by intro k; fin_cases k <;> rfl)
  let mid := Function.update s 23 (wire.reverse ++ s 23)
  have hinc := SchurCounters.increment_spec SchurTableMachine.columnIncrementPorts mid
    (j.val+1) rfl rfl rfl
  have hprefix : «prefix» M (i.val*n+(j.val+1)) =
      «prefix» M (i.val*n+j.val) ++ wire := by
    simpa only [Nat.add_assoc] using prefix_step M i j
  have hout : Function.update mid 28 (Computability.encodeNat (j.val+1+1)) =
      columnState M i.val (j.val+1) rows cols := by
    funext k
    fin_cases k <;> simp [mid,s,wire,columnState,hprefix,List.reverse_append,Nat.add_assoc]
  change RunSpec (SchurCounters.incrementProgram SchurTableMachine.columnIncrementPorts) mid
    (Function.update mid 28 (Computability.encodeNat (j.val+1+1))) _ at hinc
  rw [hout] at hinc
  exact he.compose hinc

theorem column_pop {n : ℕ} (M : DenseRatMatrix (n+1)) (r c rows cols : ℕ) :
    Function.update (columnState M r c rows (cols+1)) 25 (List.replicate cols true) =
      columnState M r c rows cols := by
  funext k; fin_cases k <;> rfl

theorem row_pop {n : ℕ} (M : DenseRatMatrix (n+1)) (r rows : ℕ) :
    Function.update (rowState M r (rows+1)) 24 (List.replicate rows true) = rowState M r rows := by
  funext k; fin_cases k <;> rfl

end KS.W07.SchurLoopState

end

end OAI
