import Mathlib
import OAI.Analysis.MatrixSigning.Machines.SchurReadStage

namespace OAI

section

namespace KS.W19.TerminalReadStage
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators
open KS.W07

def ports : Fin 32 ↪ Fin 35 :=
  ⟨![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,30,33,29,27,31], by decide⟩
def sourceRow (diagonal : Bool) : Fin 35 := if diagonal then 30 else 29
def destination (diagonal : Bool) : Fin 35 := if diagonal then 19 else 20
def slot (diagonal : Bool) : Fin 4 := if diagonal then 0 else 1
def program (diagonal : Bool) : Program 35 :=
  liftPorts (SchurReadStage.program diagonal true (slot diagonal)) ports

def WorkClear (s : Fin 35 → List Bool) : Prop := ∀ j, j.val < 19 → s j = []
def readTicks {n : ℕ} (M : DenseRatMatrix n) (B : ℕ) (i j : Fin n)
    (s : Fin 35 → List Bool) (diagonal : Bool) : ℕ :=
  SchurReadStage.prepareTicks (fun k => s (ports k)) diagonal true +
    (1024*(n+1)^2*(B+1)+(2*KS.W01.ratLength (DenseRatMatrix.decode M i j)+2))

theorem read_spec {n : ℕ} (M : DenseRatMatrix n) (B : ℕ)
    (hnum : ∀ i j, (DenseRatMatrix.decode M i j).num.natAbs ≤ 2^B)
    (hden : ∀ i j, (DenseRatMatrix.decode M i j).den ≤ 2^B)
    (i j : Fin n) (s : Fin 35 → List Bool) (hw : WorkClear s)
    (hm : s 31 = KS.W08.denseMatrixTape M) (hd : s 26 = Computability.encodeNat n)
    (diagonal : Bool) (hr : s (sourceRow diagonal) = Computability.encodeNat i.val)
    (hc : s 33 = Computability.encodeNat j.val) (he : s (destination diagonal) = []) :
    RunSpec (program diagonal) s
      (Function.update s (destination diagonal) (KS.W01.encodeRat (DenseRatMatrix.decode M i j)))
      (readTicks M B i j s diagonal) := by
  have hwork : SchurReadStage.WorkClear (fun k => s (ports k)) := by
    intro k hk
    apply hw
    fin_cases k <;> simp_all [ports]
  have hrow : s (ports (SchurReadStage.rowSource diagonal)) = Computability.encodeNat i.val := by
    cases diagonal <;> simpa [ports,SchurReadStage.rowSource,sourceRow] using hr
  have hdest : ports (SchurReadStage.destination (slot diagonal)) = destination diagonal := by
    cases diagonal <;> rfl
  have h := SchurReadStage.full_spec M B hnum hden i j (fun k => s (ports k)) hwork
    hm hd diagonal true hrow hc (slot diagonal) (by
      exact (congrArg s hdest).trans he)
  apply KS.W01.FixedPortRunSpec.lift_runSpec _ ports _ _ _ _ _ h
  · intro k; rfl
  · intro k
    by_cases hk : k = SchurReadStage.destination (slot diagonal)
    · subst k
      simp only [Function.update_self]
      exact (congrArg (Function.update s (destination diagonal)
        (KS.W01.encodeRat (DenseRatMatrix.decode M i j))) hdest).trans
          (Function.update_self _ _ _)
    · have hne : ports k ≠ destination diagonal := by
        rw [← hdest]
        exact fun h => hk (ports.injective h)
      simp [Function.update_of_ne,hk,hne]
  · intro k hk
    have hne : k ≠ destination diagonal := by simpa only [hdest] using hk (SchurReadStage.destination (slot diagonal))
    simp [Function.update_of_ne,hne]

end KS.W19.TerminalReadStage

end

end OAI
