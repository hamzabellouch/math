import Mathlib
import OAI.Analysis.MatrixSigning.Arithmetic.RationalAddCorrect
import OAI.Analysis.MatrixSigning.Arithmetic.ComplexScalarNodes

namespace OAI

section

namespace KS.W15.ComplexMachine
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators
open KS.W15.WireProgram KS.W01

def negativeOneWire : List Bool := [true,true,false,true,true]
theorem negativeOneWire_eq : negativeOneWire = encodeRat (-1) := by decide

def negNode (a dest : Fin 28) (ha : 16 ≤ a.val) : Program 28 :=
  compose (compose (compose
    (copyProgram a 0 1 (stored_ne_core a ha 0) (stored_ne_core a ha 1) (by decide))
    (literalProgram 0 negativeOneWire)) mulProgram) (storeProgram dest)

def negNodeTicks (q : ℚ) : Nat :=
  (2 * ratLength q + 2 + 6) + RationalMultiply.totalTicks (-1) q + (2 * ratLength (-q) + 2)

theorem negNode_spec (a dest : Fin 28) (ha : 16 ≤ a.val) (hd : 16 ≤ dest.val)
    (before : Registers) (hclear : CoreEmpty before) (q : ℚ)
    (hq : before a = encodeRat q) (hempty : before dest = []) :
    RunSpec (negNode a dest ha) before
      (Function.update before dest (encodeRat (-q))) (negNodeTicks q) := by
  have hc := copy_spec a (0 : Fin 28) 1 (stored_ne_core a ha 0) (stored_ne_core a ha 1)
    (by decide) before (hclear 0) (hclear 1)
  rw [hq] at hc
  have hp : RunSpec (literalProgram (0 : Fin 28) negativeOneWire)
      (Function.update before 0 (encodeRat q))
      (Function.update before 0 (encodeRat (-1) ++ encodeRat q)) 6 := by
    have h := literal_spec (0 : Fin 28) negativeOneWire (Function.update before 0 (encodeRat q))
    have he : negativeOneWire.length + 1 = 6 := rfl
    rw [he] at h
    simpa only [Function.update_self,Function.update_idem,negativeOneWire_eq] using h
  have hm : RunSpec mulProgram (Function.update before 0 (encodeRat (-1) ++ encodeRat q))
      (Function.update before 10 (encodeRat (-q))) (RationalMultiply.totalTicks (-1) q) := by
    simpa only [neg_one_mul] using scalar_multiplication_spec before hclear (-1) q
  exact ((hc.compose hp).compose hm).compose (store_spec before hclear dest hd hempty _)

theorem mulNodeTicks_le (q r : ℚ) :
    mulNodeTicks q r ≤ 4096 * (ratLength q + ratLength r + 1) ^ 3 := by
  have ht := RationalMultiply.totalTicks_le_polynomial q r
  have hs := ratLength_mul_le q r
  have hp : ratLength q + ratLength r + 1 ≤ (ratLength q + ratLength r + 1)^3 :=
    Nat.le_self_pow (by decide) _
  simp only [RationalMultiply.inputBits,List.length_append] at ht
  change RationalMultiply.totalTicks q r ≤ 2048 * (ratLength q + ratLength r + 1)^3 at ht
  change 4 * ratLength q + 2 * ratLength r + 6 + RationalMultiply.totalTicks q r +
    (2 * ratLength (q*r) + 2) ≤ _
  omega

theorem addNodeTicks_le (q r : ℚ) :
    addNodeTicks q r ≤ 4096 * (ratLength q + ratLength r + 1) ^ 3 := by
  have ht := KS.W13.RationalAdd.totalTicks_le_polynomial q r
  have hs := ratLength_add_le q r
  have hp : ratLength q + ratLength r + 1 ≤ (ratLength q + ratLength r + 1)^3 :=
    Nat.le_self_pow (by decide) _
  simp only [List.length_append] at ht
  change KS.W13.RationalAdd.totalTicks q r ≤ 1000 * (ratLength q + ratLength r + 1)^3 at ht
  change 4 * ratLength q + 2 * ratLength r + 6 + KS.W13.RationalAdd.totalTicks q r +
    (2 * ratLength (q+r) + 2) ≤ _
  omega

theorem negNodeTicks_le (q : ℚ) : negNodeTicks q ≤ 1048576 * (ratLength q + 1)^3 := by
  have ht := RationalMultiply.totalTicks_le_polynomial (-1) q
  simp only [RationalMultiply.inputBits,List.length_append] at ht
  have hlen : ratLength (-1) = 5 := by decide
  have hs := ratLength_neg_le q
  have hp : ratLength q + 1 ≤ (ratLength q + 1)^3 := Nat.le_self_pow (by decide) _
  have hbase : ratLength (-1) + ratLength q + 1 ≤ 6 * (ratLength q + 1) := by omega
  have hpower := Nat.mul_le_mul_left 2048 (Nat.pow_le_pow_left hbase 3)
  have ht' : RationalMultiply.totalTicks (-1) q ≤ 442368 * (ratLength q + 1)^3 := by
    change RationalMultiply.totalTicks (-1) q ≤ 2048 * (ratLength (-1) + ratLength q + 1)^3 at ht
    exact ht.trans (by nlinarith [hpower])
  unfold negNodeTicks
  omega

end KS.W15.ComplexMachine

end

end OAI
