import Mathlib
import OAI.Analysis.MatrixSigning.Machines.SchurCounters
import OAI.Analysis.MatrixSigning.Matrices.PivotRowClassify

namespace OAI

section

namespace KS.W17.PivotRowBody
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators KS.W07
open KS.W07.SchurReadStage

def incrementPorts : Fin 3 ↪ Fin 32 := ⟨![0,28,1], by decide⟩
def zeroProgram : Program 32 := compose (KS.W04.BinaryStackMoves.clearProgram 29)
  (SchurCounters.incrementProgram incrementPorts)
def foundProgram : Program 32 := compose (KS.W04.BinaryStackMoves.clearProgram 29)
  (SchurCounters.pushProgram 24 true)
def select (heads : Fin 32 → Fin 3) (_coin : Bool) : KS.W29.FixedBranch.SelectInstruction 32 :=
  ⟨if (heads 29).val = 2 then .left else .right, Vector.ofFn (fun _ => .stay)⟩
def branch : Program 32 := KS.W29.FixedBranch.branch zeroProgram foundProgram 24 select

def after (before : Fin 32 → List Bool) (q : ℚ) (idx : ℕ) : Fin 32 → List Bool :=
  if q = 0 then Function.update before 28 (Computability.encodeNat (idx+1))
  else Function.update before 24 [true]

theorem branch_spec (before : Fin 32 → List Bool) (q : ℚ) (idx : ℕ)
    (h0 : before 0 = []) (h1 : before 1 = []) (hf : before 24 = [])
    (hj : before 28 = Computability.encodeNat idx) (h29 : before 29 = []) :
    RunSpec branch (Function.update before 29 (KS.W06.RationalSignClassifier.outputCode q))
      (after before q idx) (2*(Computability.encodeNat idx).length+10) := by
  let s := Function.update before 29 (KS.W06.RationalSignClassifier.outputCode q)
  have hc := KS.W04.CleanRationalCompare.clear_spec (29 : Fin 32) s
  have he : KS.W04.CleanRationalCompare.clearState 29 s = before := by
    funext j
    by_cases hjj : j = 29 <;> simp [KS.W04.CleanRationalCompare.clearState, s, hjj, h29]
  rw [he] at hc
  by_cases hz : q = 0
  · have hinc := SchurCounters.increment_spec incrementPorts before idx h0 hj h1
    have hb := hc.compose hinc
    have hs : ∀ coin, select (observedHeads (Config.mk (some (KS.W29.FixedBranch.start zeroProgram foundProgram)) s)) coin =
        ⟨.left, Vector.ofFn (fun _ => .stay)⟩ := by
      intro coin
      subst q
      simp [select, s, KS.W06.RationalSignClassifier.outputCode, observedHeads, KS.W29.topCode]
    have hbranch := KS.W06.RationalCompare.branch_spec_left zeroProgram foundProgram 24 select s _ _ hs hb
    change RunSpec branch s (after before q idx) _
    rw [after, ite_eq_left hz]
    apply hbranch.mono
    simp [s, hz, KS.W06.RationalSignClassifier.outputCode]
    omega
  · have hp := SchurCounters.push_spec (24 : Fin 32) true before
    rw [hf] at hp
    have hb := hc.compose hp
    have hs : ∀ coin, select (observedHeads (Config.mk (some (KS.W29.FixedBranch.start zeroProgram foundProgram)) s)) coin =
        ⟨.right, Vector.ofFn (fun _ => .stay)⟩ := by
      intro coin
      by_cases hn : q < 0 <;>
        simp [select, s, KS.W06.RationalSignClassifier.outputCode, hn, hz, observedHeads, KS.W29.topCode]
    have hbranch := KS.W06.RationalCompare.branch_spec_right zeroProgram foundProgram 24 select s _ _ hs hb
    simp only [after, hz, ite_false]
    change RunSpec branch s (Function.update before 24 [true]) _
    apply hbranch.mono
    by_cases hn : q < 0 <;> simp [s, KS.W06.RationalSignClassifier.outputCode, hn, hz]

def program : Program 32 := compose PivotRowClassify.program branch

def ticks {n : ℕ} (M : DenseRatMatrix (n+1)) (b : ℕ) (j : Fin (n+1)) : ℕ :=
  PivotRowClassify.ticks M b j + (2*(Computability.encodeNat j.val).length+10)

theorem full_spec {n : ℕ} (M : DenseRatMatrix (n+1)) (b : ℕ)
    (hnum : ∀ i j, (DenseRatMatrix.decode M i j).num.natAbs ≤ 2^b)
    (hden : ∀ i j, (DenseRatMatrix.decode M i j).den ≤ 2^b)
    (j : Fin (n+1)) (before : Fin 32 → List Bool) (hw : WorkClear before)
    (hm : before 31 = KS.W08.denseMatrixTape M) (hd : before 26 = Computability.encodeNat (n+1))
    (hj : before 28 = Computability.encodeNat j.val) (hf : before 24 = []) (h29 : before 29 = []) :
    RunSpec program before (after before (DenseRatMatrix.decode M 0 j) j.val) (ticks M b j) :=
  (PivotRowClassify.full_spec M b hnum hden j before hw hm hd hj h29).compose
    (branch_spec before (DenseRatMatrix.decode M 0 j) j.val (hw 0 (by decide)) (hw 1 (by decide)) hf hj h29)

end KS.W17.PivotRowBody

end

end OAI
