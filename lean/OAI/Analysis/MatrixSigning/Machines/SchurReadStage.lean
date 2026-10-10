import Mathlib
import OAI.Analysis.MatrixSigning.Encoding.WireAppend
import OAI.Analysis.MatrixSigning.Machines.FixedCopySpec
import OAI.Analysis.MatrixSigning.Matrices.MatrixReadProgram

namespace OAI

section

namespace KS.W07.SchurReadStage
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators

def readPorts : Fin 8 ↪ Fin 32 := ⟨![0,1,2,3,4,5,6,31], by decide⟩
def reader : Program 32 := liftPorts KS.W08.MatrixRead.program readPorts

def WorkClear (before : Fin 32 → List Bool) : Prop := ∀ j, j.val < 19 → before j = []

def readPrepared (before : Fin 32 → List Bool) (col row dim : List Bool) : Fin 32 → List Bool :=
  Function.update (Function.update (Function.update before 2 dim) 1 row) 0 col

theorem reader_spec {n : ℕ} (M : DenseRatMatrix n) (B : ℕ)
    (hnum : ∀ i j, (DenseRatMatrix.decode M i j).num.natAbs ≤ 2^B)
    (hden : ∀ i j, (DenseRatMatrix.decode M i j).den ≤ 2^B)
    (i j : Fin n) (before : Fin 32 → List Bool) (hw : WorkClear before)
    (hm : before 31 = KS.W08.denseMatrixTape M) :
    RunSpec reader
      (readPrepared before (Computability.encodeNat j.val) (Computability.encodeNat i.val)
        (Computability.encodeNat n))
      (Function.update before 0 (KS.W01.encodeRat (DenseRatMatrix.decode M i j)))
      (1024*(n+1)^2*(B+1)) := by
  have hsmall : RunSpec KS.W08.MatrixRead.program
      (KS.W08.MatrixRead.workspace (KS.W08.denseMatrixTape M)
        (Computability.encodeNat j.val) (Computability.encodeNat i.val) (Computability.encodeNat n) [])
      (KS.W08.MatrixRead.workspace (KS.W08.denseMatrixTape M)
        (KS.W01.encodeRat (DenseRatMatrix.decode M i j)) [] [] [])
      (1024*(n+1)^2*(B+1)) := by
    intro bits hbits
    exact KS.W08.MatrixRead.run_matrix_read M B hnum hden i j bits hbits.ge
  have hw1 := hw 1 (by decide)
  have hw2 := hw 2 (by decide)
  have hw3 := hw 3 (by decide)
  have hw4 := hw 4 (by decide)
  have hw5 := hw 5 (by decide)
  have hw6 := hw 6 (by decide)
  apply KS.W01.FixedPortRunSpec.lift_runSpec _ readPorts _ _ _ _ _ hsmall
  · intro r
    fin_cases r <;> simp [readPorts, readPrepared, KS.W08.MatrixRead.workspace, hm, hw3, hw4, hw5, hw6]
  · intro r
    fin_cases r <;> simp [readPorts, KS.W08.MatrixRead.workspace, hm, hw1, hw2, hw3, hw4, hw5, hw6]
  · intro r hr
    have h0 := hr 0
    have h1 := hr 1
    have h2 := hr 2
    change r ≠ 0 at h0
    change r ≠ 1 at h1
    change r ≠ 2 at h2
    simp [readPrepared, Function.update_of_ne h0, Function.update_of_ne h1,
      Function.update_of_ne h2]

def copyPorts (source target : Fin 32) (hs : source ≠ target)
    (hc : source ≠ 16) (ht : target ≠ 16) : Fin 3 ↪ Fin 32 :=
  ⟨![source,target,16], by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all⟩

def copyProgram (source target : Fin 32) (hs : source ≠ target)
    (hc : source ≠ 16) (ht : target ≠ 16) : Program 32 :=
  KS.W01.FixedCopy.program (copyPorts source target hs hc ht)

theorem copy_spec (source target : Fin 32) (hs : source ≠ target)
    (hc : source ≠ 16) (ht : target ≠ 16) (before : Fin 32 → List Bool)
    (he : before target = []) (h16 : before 16 = []) :
    RunSpec (copyProgram source target hs hc ht) before
      (Function.update before target (before source)) (2*(before source).length+2) := by
  exact KS.W07.fixedCopy_spec (copyPorts source target hs hc ht)
    before (before source) rfl he h16

def rowSource (nonzero : Bool) : Fin 32 := if nonzero then 27 else 29
def colSource (nonzero : Bool) : Fin 32 := if nonzero then 28 else 29

def prepare (row col : Bool) : Program 32 :=
  compose (copyProgram 26 2 (by decide) (by decide) (by decide))
    (compose (copyProgram (rowSource row) 1 (by cases row <;> decide)
      (by cases row <;> decide) (by decide))
      (copyProgram (colSource col) 0 (by cases col <;> decide)
        (by cases col <;> decide) (by decide)))

def prepareTicks (before : Fin 32 → List Bool) (row col : Bool) : ℕ :=
  (2*(before 26).length+2) +
    ((2*(before (rowSource row)).length+2) + (2*(before (colSource col)).length+2))

theorem prepare_spec (before : Fin 32 → List Bool) (hw : WorkClear before) (row col : Bool) :
    RunSpec (prepare row col) before
      (readPrepared before (before (colSource col)) (before (rowSource row)) (before 26))
      (prepareTicks before row col) := by
  have h₁ := copy_spec 26 2 (by decide) (by decide) (by decide) before
    (hw _ (by decide)) (hw _ (by decide))
  have h₂ := copy_spec (rowSource row) 1 (by cases row <;> decide)
    (by cases row <;> decide) (by decide) (Function.update before 2 (before 26))
    (by simpa using hw 1 (by decide)) (by simpa using hw 16 (by decide))
  have h₃ := copy_spec (colSource col) 0 (by cases col <;> decide)
    (by cases col <;> decide) (by decide)
    (Function.update (Function.update before 2 (before 26)) 1 (before (rowSource row)))
    (by simpa using hw 0 (by decide)) (by simpa using hw 16 (by decide))
  have hrow : (Function.update before 2 (before 26)) (rowSource row) = before (rowSource row) := by
    cases row <;> rfl
  rw [hrow] at h₂
  have hcol : (Function.update (Function.update before 2 (before 26)) 1
      (before (rowSource row))) (colSource col) = before (colSource col) := by
    cases col <;> rfl
  rw [hcol] at h₃
  exact h₁.compose (h₂.compose h₃)

def destination (k : Fin 4) : Fin 32 := ⟨19+k.val, by omega⟩

theorem destination_ne_core (k : Fin 4) (j : Fin 32) (hj : j.val < 19) :
    destination k ≠ j := by
  intro h
  have he := congrArg Fin.val h
  change 19 + k.val = j.val at he
  omega

def program (row col : Bool) (k : Fin 4) : Program 32 :=
  compose (prepare row col) (compose reader (WireAppend.program 0 (destination k) 16))

theorem full_spec {n : ℕ} (M : DenseRatMatrix n) (B : ℕ)
    (hnum : ∀ i j, (DenseRatMatrix.decode M i j).num.natAbs ≤ 2^B)
    (hden : ∀ i j, (DenseRatMatrix.decode M i j).den ≤ 2^B)
    (i j : Fin n) (before : Fin 32 → List Bool) (hw : WorkClear before)
    (hm : before 31 = KS.W08.denseMatrixTape M) (hd : before 26 = Computability.encodeNat n)
    (row col : Bool) (hr : before (rowSource row) = Computability.encodeNat i.val)
    (hc : before (colSource col) = Computability.encodeNat j.val)
    (k : Fin 4) (hk : before (destination k) = []) :
    RunSpec (program row col k) before
      (Function.update before (destination k) (KS.W01.encodeRat (DenseRatMatrix.decode M i j)))
      (prepareTicks before row col + (1024*(n+1)^2*(B+1) +
        (2*KS.W01.ratLength (DenseRatMatrix.decode M i j)+2))) := by
  have hp := prepare_spec before hw row col
  rw [hr,hc,hd] at hp
  have hread := reader_spec M B hnum hden i j before hw hm
  have hmove := WireAppend.spec (0 : Fin 32) (destination k) 16
    (Ne.symm (destination_ne_core k 0 (by decide))) (by decide)
    (Ne.symm (destination_ne_core k 16 (by decide)))
    (Function.update before 0 (KS.W01.encodeRat (DenseRatMatrix.decode M i j)))
    (by simpa using hw 16 (by decide))
  have hout : WireAppend.after 0 (destination k)
      (Function.update before 0 (KS.W01.encodeRat (DenseRatMatrix.decode M i j))) =
      Function.update before (destination k) (KS.W01.encodeRat (DenseRatMatrix.decode M i j)) := by
    funext r
    have hd0 : destination k ≠ 0 := destination_ne_core k 0 (by decide)
    by_cases h0 : r=0
    · subst r
      simp [WireAppend.after, Ne.symm hd0, hw 0 (by decide)]
    · by_cases hdest : r=destination k
      · subst r
        simp [WireAppend.after, hd0, hk]
      · simp [WireAppend.after, h0, hdest]
  rw [hout] at hmove
  simp only [Function.update_self] at hmove
  exact hp.compose (hread.compose hmove)

end KS.W07.SchurReadStage

end

end OAI
