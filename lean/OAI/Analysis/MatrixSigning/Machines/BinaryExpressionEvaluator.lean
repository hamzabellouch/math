import Mathlib
import OAI.Analysis.MatrixSigning.Arithmetic.RationalExpressionHeight
import OAI.Analysis.MatrixSigning.Arithmetic.BinaryRationalCanonical

namespace OAI

section

namespace KS.W17
open KS.W30.BinaryRational

def binaryNegate (x : RatBits) : RatBits := multiplyRat (encodeMagnitude (-1)) x

def binarySubtract (x y : RatBits) : RatBits := addRat x (binaryNegate y)
def binaryDivide (x y : RatBits) : RatBits := multiplyRat x (inverseRat y)

@[simp] theorem binaryNegate_canonical (q : ℚ) :
    binaryNegate (encodeMagnitude q) = encodeMagnitude (-q) := by
  simp [binaryNegate]

@[simp] theorem binarySubtract_canonical (q r : ℚ) :
    binarySubtract (encodeMagnitude q) (encodeMagnitude r) = encodeMagnitude (q - r) := by
  simp [binarySubtract, sub_eq_add_neg]

@[simp] theorem binaryDivide_canonical (q r : ℚ) :
    binaryDivide (encodeMagnitude q) (encodeMagnitude r) = encodeMagnitude (q / r) := by
  simp [binaryDivide, div_eq_mul_inv]

def RationalExpr.evalBinary : RationalExpr → RatBits
  | .value q => encodeMagnitude q
  | .add x y => addRat x.evalBinary y.evalBinary
  | .sub x y => binarySubtract x.evalBinary y.evalBinary
  | .mul x y => multiplyRat x.evalBinary y.evalBinary
  | .div x y => binaryDivide x.evalBinary y.evalBinary
  | .neg x => binaryNegate x.evalBinary

@[simp] theorem RationalExpr.evalBinary_canonical (e : RationalExpr) :
    e.evalBinary = encodeMagnitude e.eval := by
  induction e <;> simp_all [RationalExpr.evalBinary, RationalExpr.eval]

@[simp] theorem RationalExpr.evalBinary_value (e : RationalExpr) :
    e.evalBinary.value = e.eval := by simp

theorem encodeMagnitude_length (q : ℚ) :
    (encodeMagnitude q).length = Nat.size q.num.natAbs + Nat.size q.den + 1 := by
  simp [encodeMagnitude, RatBits.length, KS.W19.encodeNat_length_eq_size]

theorem encodeMagnitude_length_le (q : ℚ) (E : ℕ)
    (hn : q.num.natAbs ≤ 2 ^ E) (hd : q.den ≤ 2 ^ E) :
    (encodeMagnitude q).length ≤ 2 * E + 3 := by
  have hp : 2 ^ E < 2 ^ (E + 1) := by
    rw [pow_succ]
    have hh : 0 < 2 ^ E := pow_pos (by decide) _
    omega
  have hns := Nat.size_le.mpr (hn.trans_lt hp)
  have hds := Nat.size_le.mpr (hd.trans_lt hp)
  rw [encodeMagnitude_length]
  omega

def RationalExpr.binaryWork : RationalExpr → ℕ
  | .value q => (encodeMagnitude q).length
  | .add x y => x.binaryWork + y.binaryWork + addRatWork x.evalBinary y.evalBinary
  | .sub x y => x.binaryWork + y.binaryWork +
      multiplyRatWork (encodeMagnitude (-1)) y.evalBinary +
      addRatWork x.evalBinary (binaryNegate y.evalBinary)
  | .mul x y => x.binaryWork + y.binaryWork + multiplyRatWork x.evalBinary y.evalBinary
  | .div x y => x.binaryWork + y.binaryWork + inverseRatWork y.evalBinary +
      multiplyRatWork x.evalBinary (inverseRat y.evalBinary)
  | .neg x => x.binaryWork + multiplyRatWork (encodeMagnitude (-1)) x.evalBinary

theorem RationalExpr.IsSubexpression.evalBinary_length_le {e root : RationalExpr}
    (h : e.IsSubexpression root) (B : ℕ) (hb : root.inputsBounded B) :
    e.evalBinary.length ≤ 2 * ((root.operations + 1) * (B + 1)) + 3 := by
  have hp := h.eval_parts_le B hb
  rw [RationalExpr.evalBinary_canonical]
  exact encodeMagnitude_length_le e.eval _ hp.1 hp.2

end KS.W17

end

end OAI
