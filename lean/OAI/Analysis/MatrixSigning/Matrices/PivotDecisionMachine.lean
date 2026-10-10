import Mathlib
import OAI.Analysis.MatrixSigning.Matrices.PivotRowFinish

namespace OAI

namespace KS.W17.PivotDecision
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators KS.W07

def zeroProgram : Program 32 := compose (KS.W04.BinaryStackMoves.clearProgram 29)
  PivotRowLoop.completeProgram
def returnProgram : Program 32 := KS.W04.CleanRationalCompare.haltProgram 29

def select (heads : Fin 32 → Fin 3) (_coin : Bool) : KS.W29.FixedBranch.SelectInstruction 32 :=
  ⟨if (heads 29).val = 2 then .left else .right, Vector.ofFn (fun _ => .stay)⟩
def dispatch : Program 32 := KS.W29.FixedBranch.branch zeroProgram returnProgram 29 select

def program : Program 32 := compose PivotRowClassify.program dispatch

def result {n : ℕ} (M : DenseRatMatrix (n+1)) : Fin 32 → List Bool :=
  if DenseRatMatrix.decode M 0 0 = 0 then
    PivotRowLoop.finished M (PivotRowLoop.outcome M 1 n).index (PivotRowLoop.outcome M 1 n).found
  else Function.update (PivotRowLoop.initial M) 29
    (KS.W06.RationalSignClassifier.outputCode (DenseRatMatrix.decode M 0 0))

def rowTicks {n : ℕ} (M : DenseRatMatrix (n+1)) (b : ℕ) : ℕ :=
  PivotRowLoop.initializeTicks n + PivotRowLoop.ticks M b 1 n +
    PivotRowLoop.finishTicks (PivotRowLoop.outcome M 1 n).index (PivotRowLoop.outcome M 1 n).remaining

def ticks {n : ℕ} (M : DenseRatMatrix (n+1)) (b : ℕ) : ℕ :=
  PivotRowClassify.ticks M b 0 + if DenseRatMatrix.decode M 0 0 = 0 then 3+rowTicks M b else 2

theorem full_spec {n : ℕ} (M : DenseRatMatrix (n+1)) (b : ℕ)
    (hnum : ∀ i j, (DenseRatMatrix.decode M i j).num.natAbs ≤ 2^b)
    (hden : ∀ i j, (DenseRatMatrix.decode M i j).den ≤ 2^b) :
    RunSpec program (PivotRowLoop.initial M) (result M) (ticks M b) := by
  let s := PivotRowLoop.initial M
  let q := DenseRatMatrix.decode M 0 0
  let t := Function.update s 29 (KS.W06.RationalSignClassifier.outputCode q)
  have hw : KS.W07.SchurReadStage.WorkClear s := by
    intro j hj
    have h24 : j ≠ 24 := by intro h; subst j; omega
    have h25 : j ≠ 25 := by intro h; subst j; omega
    have h26 : j ≠ 26 := by intro h; subst j; omega
    have h28 : j ≠ 28 := by intro h; subst j; omega
    have h31 : j ≠ 31 := by intro h; subst j; omega
    simp [s,PivotRowLoop.initial,PivotRowLoop.state,h24,h25,h26,h28,h31]
  have hr := PivotRowClassify.full_spec M b hnum hden 0 s hw rfl rfl rfl rfl
  by_cases hz : q=0
  · have hc := KS.W04.CleanRationalCompare.clear_spec (29 : Fin 32) t
    have he : KS.W04.CleanRationalCompare.clearState 29 t = s := by
      funext j; fin_cases j <;> simp [KS.W04.CleanRationalCompare.clearState,t,s,
        PivotRowLoop.initial,PivotRowLoop.state]
    rw [he] at hc
    have hrow := PivotRowLoop.complete_spec M b hnum hden
    have hzrun := hc.compose hrow
    have hs : ∀ coin, select (observedHeads
        (⟨some (KS.W29.FixedBranch.start zeroProgram returnProgram),t⟩ :
          Config 32 (zeroProgram.states+returnProgram.states+1))) coin =
        ⟨.left,KS.W06.RationalCompare.stayActions 32⟩ := by
      intro coin; simp [select,t,hz,KS.W06.RationalSignClassifier.outputCode,observedHeads,
        KS.W29.topCode,KS.W06.RationalCompare.stayActions]
    have hd := KS.W06.RationalCompare.branch_spec_left zeroProgram returnProgram 29 select _ _ _ hs hzrun
    have h := hr.compose hd
    convert h using 1 <;> (try rfl) <;>
      simp [result,ticks,hz,q,t,rowTicks,KS.W06.RationalSignClassifier.outputCode]
    omega
  · have hret := KS.W04.CleanRationalCompare.halt_spec (29 : Fin 32) t
    have hs : ∀ coin, select (observedHeads
        (⟨some (KS.W29.FixedBranch.start zeroProgram returnProgram),t⟩ :
          Config 32 (zeroProgram.states+returnProgram.states+1))) coin =
        ⟨.right,KS.W06.RationalCompare.stayActions 32⟩ := by
      intro coin
      by_cases hn : q<0 <;> simp [select,t,hz,hn,KS.W06.RationalSignClassifier.outputCode,observedHeads,
        KS.W29.topCode,KS.W06.RationalCompare.stayActions]
    have hd := KS.W06.RationalCompare.branch_spec_right zeroProgram returnProgram 29 select _ _ _ hs hret
    have h := hr.compose hd
    simp [program,result,ticks,hz,q,t] at h ⊢
    exact h

end KS.W17.PivotDecision

end OAI
