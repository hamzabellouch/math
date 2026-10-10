import Mathlib
import OAI.Analysis.MatrixSigning.Matrices.RationalElimination
import OAI.Analysis.MatrixSigning.Machines.SchurReadStage
import OAI.Analysis.MatrixSigning.Machines.SchurCellMachine

namespace OAI

namespace KS.W07.SchurOperands
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators
open SchurReadStage

def collect : Program 32 := compose (SchurReadStage.program true true 0)
  (compose (SchurReadStage.program true false 1)
    (compose (SchurReadStage.program false true 2) (SchurReadStage.program false false 3)))

def operands (s : Fin 32 → List Bool) (x a b c : List Bool) : Fin 32 → List Bool :=
  Function.update (Function.update (Function.update (Function.update s 19 x) 20 a) 21 b) 22 c

theorem workClear_update (s : Fin 32 → List Bool) (hs : WorkClear s)
    (k : Fin 4) (wire : List Bool) : WorkClear (Function.update s (destination k) wire) := by
  intro j hj
  have hne : j ≠ destination k := by intro h; have he := congrArg Fin.val h; simp [destination] at he; omega
  rw [Function.update_of_ne hne]
  exact hs j hj

def readBudget {n : ℕ} (M : DenseRatMatrix (n+1)) (B : ℕ) (i j : Fin n)
    (s : Fin 32 → List Bool) : ℕ :=
  let x := DenseRatMatrix.decode M i.succ j.succ
  let a := DenseRatMatrix.decode M i.succ 0
  let b := DenseRatMatrix.decode M 0 j.succ
  let c := DenseRatMatrix.decode M 0 0
  let t (row col : Bool) (q : ℚ) := prepareTicks s row col +
    (1024*(n+2)^2*(B+1) + (2*KS.W01.ratLength q+2))
  t true true x + (t true false a + (t false true b + t false false c))

theorem collect_spec {n : ℕ} (M : DenseRatMatrix (n+1)) (B : ℕ)
    (hnum : ∀ i j, (DenseRatMatrix.decode M i j).num.natAbs ≤ 2^B)
    (hden : ∀ i j, (DenseRatMatrix.decode M i j).den ≤ 2^B)
    (i j : Fin n) (s : Fin 32 → List Bool) (hw : WorkClear s)
    (hm : s 31 = KS.W08.denseMatrixTape M) (hd : s 26 = Computability.encodeNat (n+1))
    (hr : s 27 = Computability.encodeNat i.succ.val)
    (hc : s 28 = Computability.encodeNat j.succ.val)
    (hz : s 29 = []) (he : ∀ k : Fin 4, s (destination k) = []) :
    RunSpec collect s
      (operands s
        (KS.W01.encodeRat (DenseRatMatrix.decode M i.succ j.succ))
        (KS.W01.encodeRat (DenseRatMatrix.decode M i.succ 0))
        (KS.W01.encodeRat (DenseRatMatrix.decode M 0 j.succ))
        (KS.W01.encodeRat (DenseRatMatrix.decode M 0 0)))
      (readBudget M B i j s) := by
  let x := KS.W01.encodeRat (DenseRatMatrix.decode M i.succ j.succ)
  let a := KS.W01.encodeRat (DenseRatMatrix.decode M i.succ 0)
  let b := KS.W01.encodeRat (DenseRatMatrix.decode M 0 j.succ)
  let c := KS.W01.encodeRat (DenseRatMatrix.decode M 0 0)
  let s₁ := Function.update s (destination 0) x
  let s₂ := Function.update s₁ (destination 1) a
  let s₃ := Function.update s₂ (destination 2) b
  have hw₁ : WorkClear s₁ := workClear_update s hw 0 x
  have hw₂ : WorkClear s₂ := workClear_update s₁ hw₁ 1 a
  have hw₃ : WorkClear s₃ := workClear_update s₂ hw₂ 2 b
  have h₁ := SchurReadStage.full_spec M B hnum hden i.succ j.succ s hw hm hd
    true true hr hc 0 (he 0)
  have h₂ := SchurReadStage.full_spec M B hnum hden i.succ 0 s₁ hw₁
    (by simpa [s₁,destination] using hm) (by simpa [s₁,destination] using hd)
    true false (by simpa [s₁,destination,rowSource] using hr)
    (by simpa [s₁,destination,colSource,Computability.encodeNat,Computability.encodeNum] using hz) 1 (by simpa [s₁,destination] using he 1)
  have h₃ := SchurReadStage.full_spec M B hnum hden 0 j.succ s₂ hw₂
    (by simpa [s₂,s₁,destination] using hm) (by simpa [s₂,s₁,destination] using hd)
    false true (by simpa [s₂,s₁,destination,rowSource,Computability.encodeNat,Computability.encodeNum] using hz)
    (by simpa [s₂,s₁,destination,colSource] using hc) 2 (by simpa [s₂,s₁,destination] using he 2)
  have h₄ := SchurReadStage.full_spec M B hnum hden 0 0 s₃ hw₃
    (by simpa [s₃,s₂,s₁,destination] using hm) (by simpa [s₃,s₂,s₁,destination] using hd)
    false false (by simpa [s₃,s₂,s₁,destination,rowSource,Computability.encodeNat,Computability.encodeNum] using hz)
    (by simpa [s₃,s₂,s₁,destination,colSource,Computability.encodeNat,Computability.encodeNum] using hz) 3
    (by simpa [s₃,s₂,s₁,destination] using he 3)
  have h := h₁.compose (h₂.compose (h₃.compose h₄))
  simpa [collect,readBudget,prepareTicks,rowSource,colSource,s₁,s₂,s₃,destination,
    x,a,b,c,operands,Nat.add_assoc] using h

def scalarPorts : Fin 23 ↪ Fin 32 := Fin.castLEEmb (by decide)
def scalar : Program 32 := liftPorts SchurCellMachine.program scalarPorts

theorem scalar_spec (s : Fin 32 → List Bool) (hw : WorkClear s)
    (he : ∀ k : Fin 4, s (destination k) = []) (x a b c : ℚ) :
    RunSpec scalar (operands s (KS.W01.encodeRat x) (KS.W01.encodeRat a)
      (KS.W01.encodeRat b) (KS.W01.encodeRat c))
      (Function.update s 10 (KS.W01.encodeRat (x-a*b/c)))
      (SchurCellMachine.ticks x a b c) := by
  apply KS.W01.FixedPortRunSpec.lift_runSpec _ scalarPorts _ _ _ _ _
    (SchurCellMachine.full_spec x a b c)
  · intro k
    fin_cases k <;> simp [scalarPorts,operands,SchurCellMachine.workspace]
    all_goals exact hw _ (by decide)
  · intro k
    fin_cases k <;> simp [scalarPorts,SchurCellMachine.workspace]
    all_goals first | exact hw _ (by decide) | exact he 0 | exact he 1 | exact he 2 | exact he 3
  · intro k hk
    have hlt : ¬ k.val < 23 := by
      intro h
      exact hk ⟨k.val,h⟩ (Fin.ext rfl)
    have h10 : k ≠ 10 := by intro h; subst k; omega
    have h19 : k ≠ 19 := by intro h; subst k; omega
    have h20 : k ≠ 20 := by intro h; subst k; omega
    have h21 : k ≠ 21 := by intro h; subst k; omega
    have h22 : k ≠ 22 := by intro h; subst k; omega
    simp [operands,Function.update_of_ne,h10,h19,h20,h21,h22]

def program : Program 32 := compose collect scalar

theorem full_spec {n : ℕ} (M : DenseRatMatrix (n+1)) (B : ℕ)
    (hnum : ∀ i j, (DenseRatMatrix.decode M i j).num.natAbs ≤ 2^B)
    (hden : ∀ i j, (DenseRatMatrix.decode M i j).den ≤ 2^B)
    (i j : Fin n) (s : Fin 32 → List Bool) (hw : WorkClear s)
    (hm : s 31 = KS.W08.denseMatrixTape M) (hd : s 26 = Computability.encodeNat (n+1))
    (hr : s 27 = Computability.encodeNat i.succ.val)
    (hc : s 28 = Computability.encodeNat j.succ.val)
    (hz : s 29 = []) (he : ∀ k : Fin 4, s (destination k) = []) :
    RunSpec program s
      (Function.update s 10 (KS.W01.encodeRat (KS.W17.schurTail (DenseRatMatrix.decode M) i j)))
      (readBudget M B i j s + SchurCellMachine.ticks
        (DenseRatMatrix.decode M i.succ j.succ) (DenseRatMatrix.decode M i.succ 0)
        (DenseRatMatrix.decode M 0 j.succ) (DenseRatMatrix.decode M 0 0)) := by
  exact (collect_spec M B hnum hden i j s hw hm hd hr hc hz he).compose
    (scalar_spec s hw he _ _ _ _)

end KS.W07.SchurOperands

end OAI
