import Mathlib
import OAI.Analysis.MatrixSigning.Machines.SchurOperands

namespace OAI

section

namespace KS.W07.SchurEntryMachine
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators

def framePorts : Fin 3 ↪ Fin 32 := ⟨![0,10,1], by decide⟩
def appendProgram : Program 32 := compose (KS.W11.FrameWireCodec.frameProgram framePorts)
  (KS.W04.BinaryStackMoves.moveProgram 10 23)

theorem append_spec (s : Fin 32 → List Bool) (h0 : s 0 = []) (h1 : s 1 = [])
    (h10 : s 10 = []) (q : ℚ) :
    RunSpec appendProgram (Function.update s 10 (KS.W01.encodeRat q))
      (Function.update s 23 ((KS.W01.frame (KS.W01.encodeRat q)).reverse ++ s 23))
      (6*KS.W01.ratLength q+5) := by
  have hf := KS.W11.FrameWireCodec.frame_rat_spec framePorts s q
  have hi : KS.W28.FixedPositiveSerializer.registers framePorts s [] (KS.W01.encodeRat q) [] =
      Function.update s 10 (KS.W01.encodeRat q) := by
    funext j; fin_cases j <;> simp [framePorts,KS.W28.FixedPositiveSerializer.registers,h0,h1]
  have ho : KS.W28.FixedPositiveSerializer.registers framePorts s []
      (KS.W01.frame (KS.W01.encodeRat q)) [] =
      Function.update s 10 (KS.W01.frame (KS.W01.encodeRat q)) := by
    funext j; fin_cases j <;> simp [framePorts,KS.W28.FixedPositiveSerializer.registers,h0,h1]
  rw [hi,ho] at hf
  have hm := KS.W15.RationalMultiply.move_spec (10 : Fin 32) 23 (by decide)
    (Function.update s 10 (KS.W01.frame (KS.W01.encodeRat q)))
  have hout : KS.W15.RationalMultiply.moveAfter 10 23
      (Function.update s 10 (KS.W01.frame (KS.W01.encodeRat q))) =
      Function.update s 23 ((KS.W01.frame (KS.W01.encodeRat q)).reverse ++ s 23) := by
    funext j; fin_cases j <;> simp [KS.W15.RationalMultiply.moveAfter,h10]
  rw [hout] at hm
  have h := hf.compose hm
  have ht : (4*(KS.W01.encodeRat q).length+3) +
      (KS.W01.frame (KS.W01.encodeRat q)).length+1 = 6*KS.W01.ratLength q+5 := by
    rw [KS.W01.length_frame]; unfold KS.W01.ratLength; omega
  simpa only [appendProgram,Function.update_self,←Nat.add_assoc,ht] using h

def program : Program 32 := compose SchurOperands.program appendProgram

theorem full_spec {n : ℕ} (M : DenseRatMatrix (n+1)) (B : ℕ)
    (hnum : ∀ i j, (DenseRatMatrix.decode M i j).num.natAbs ≤ 2^B)
    (hden : ∀ i j, (DenseRatMatrix.decode M i j).den ≤ 2^B)
    (i j : Fin n) (s : Fin 32 → List Bool) (hw : SchurReadStage.WorkClear s)
    (hm : s 31 = KS.W08.denseMatrixTape M) (hd : s 26 = Computability.encodeNat (n+1))
    (hr : s 27 = Computability.encodeNat i.succ.val)
    (hc : s 28 = Computability.encodeNat j.succ.val)
    (hz : s 29 = []) (he : ∀ k : Fin 4, s (SchurReadStage.destination k) = []) :
    RunSpec program s
      (Function.update s 23
        ((KS.W01.frame (KS.W01.encodeRat (KS.W17.schurTail (DenseRatMatrix.decode M) i j))).reverse ++ s 23))
      ((SchurOperands.readBudget M B i j s + SchurCellMachine.ticks
        (DenseRatMatrix.decode M i.succ j.succ) (DenseRatMatrix.decode M i.succ 0)
        (DenseRatMatrix.decode M 0 j.succ) (DenseRatMatrix.decode M 0 0)) +
        (6*KS.W01.ratLength (KS.W17.schurTail (DenseRatMatrix.decode M) i j)+5)) :=
  (SchurOperands.full_spec M B hnum hden i j s hw hm hd hr hc hz he).compose
    (append_spec s (hw _ (by decide)) (hw _ (by decide)) (hw _ (by decide)) _)

theorem append_reverse_prefix («prefix» wire : List Bool) :
    wire.reverse ++ «prefix».reverse = («prefix» ++ wire).reverse := by simp

def finishProgram : Program 32 := compose (KS.W04.BinaryStackMoves.moveProgram 23 0)
  (WireAppend.program 0 23 16)

theorem finish_spec (s : Fin 32 → List Bool) (wire : List Bool)
    (h23 : s 23 = wire.reverse) (h0 : s 0 = []) (h16 : s 16 = []) :
    RunSpec finishProgram s (Function.update s 23 wire) (3*wire.length+3) := by
  have hm := KS.W15.RationalMultiply.move_spec (23 : Fin 32) 0 (by decide) s
  let mid := KS.W15.RationalMultiply.moveAfter 23 0 s
  have hm0 : mid 0 = wire := by simp [mid,KS.W15.RationalMultiply.moveAfter,h23,h0]
  have hm23 : mid 23 = [] := by rfl
  have hm16 : mid 16 = [] := by simpa [mid,KS.W15.RationalMultiply.moveAfter] using h16
  have ha := WireAppend.spec (0 : Fin 32) 23 16 (by decide) (by decide) (by decide) mid hm16
  have hout : WireAppend.after 0 23 mid = Function.update s 23 wire := by
    funext j; fin_cases j <;> simp [WireAppend.after,mid,KS.W15.RationalMultiply.moveAfter,h23,h0]
  rw [hout,hm0] at ha
  have h := hm.compose ha
  have ht : (s 23).length+1+(2*wire.length+2) = 3*wire.length+3 := by
    rw [h23,List.length_reverse]; omega
  simpa only [finishProgram,ht] using h

end KS.W07.SchurEntryMachine

end

end OAI
