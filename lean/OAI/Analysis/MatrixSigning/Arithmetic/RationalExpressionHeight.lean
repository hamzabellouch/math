import Mathlib
import OAI.Analysis.MatrixSigning.Arithmetic.RationalArithmeticMeter
import OAI.Analysis.MatrixSigning.Arithmetic.ArithmeticBounds

namespace OAI

namespace KS.W17

def RationalExpr.leaves : RationalExpr → ℕ
  | .value _ => 1
  | .add x y | .sub x y | .mul x y | .div x y => x.leaves + y.leaves
  | .neg x => x.leaves

def RationalExpr.inputsBounded (B : ℕ) : RationalExpr → Prop
  | .value q => q.num.natAbs ≤ 2 ^ B ∧ q.den ≤ 2 ^ B
  | .add x y | .sub x y | .mul x y | .div x y => x.inputsBounded B ∧ y.inputsBounded B
  | .neg x => x.inputsBounded B

theorem RationalExpr.leaves_le_operations_add_one (e : RationalExpr) :
    e.leaves ≤ e.operations + 1 := by
  induction e <;> simp_all [RationalExpr.leaves, RationalExpr.operations] <;> omega

theorem RationalExpr.eval_parts_le (e : RationalExpr) (B : ℕ)
    (h : e.inputsBounded B) :
    e.eval.num.natAbs ≤ 2 ^ (e.leaves * B + e.operations) ∧
      e.eval.den ≤ 2 ^ (e.leaves * B + e.operations) := by
  induction e with
  | value q => simpa [RationalExpr.eval, RationalExpr.leaves, RationalExpr.operations, RationalExpr.inputsBounded] using h
  | add x y ihx ihy =>
      have hx := ihx h.1
      have hy := ihy h.2
      have ha := KS.W30.add_parts_le_two_pow x.eval y.eval
        (x.leaves * B + x.operations) (y.leaves * B + y.operations)
        hx.1 hx.2 hy.1 hy.2
      have he : (x.leaves * B + x.operations) + (y.leaves * B + y.operations) + 1 =
          (x.leaves + y.leaves) * B + (x.operations + y.operations + 1) := by ring
      refine ⟨?_, ?_⟩
      · simpa [RationalExpr.eval, RationalExpr.leaves, RationalExpr.operations, he] using ha.1
      · apply ha.2.trans
        apply Nat.pow_le_pow_right (by decide : 0 < 2)
        simp only [RationalExpr.leaves, RationalExpr.operations]
        nlinarith
  | sub x y ihx ihy =>
      have hx := ihx h.1
      have hy := ihy h.2
      have hn : (-y.eval).num.natAbs ≤ 2 ^ (y.leaves * B + y.operations) ∧
          (-y.eval).den ≤ 2 ^ (y.leaves * B + y.operations) := by simpa using hy
      have ha := KS.W30.add_parts_le_two_pow x.eval (-y.eval)
        (x.leaves * B + x.operations) (y.leaves * B + y.operations)
        hx.1 hx.2 hn.1 hn.2
      have he : (x.leaves * B + x.operations) + (y.leaves * B + y.operations) + 1 =
          (x.leaves + y.leaves) * B + (x.operations + y.operations + 1) := by ring
      refine ⟨?_, ?_⟩
      · simpa [RationalExpr.eval, RationalExpr.leaves, RationalExpr.operations,
          sub_eq_add_neg, he] using ha.1
      · change (x.eval - y.eval).den ≤ _
        rw [sub_eq_add_neg]
        apply ha.2.trans
        apply Nat.pow_le_pow_right (by decide : 0 < 2)
        simp only [RationalExpr.leaves, RationalExpr.operations]
        nlinarith
  | mul x y ihx ihy =>
      have hx := ihx h.1
      have hy := ihy h.2
      have hm := KS.W30.mul_parts_le_two_pow x.eval y.eval
        (x.leaves * B + x.operations) (y.leaves * B + y.operations)
        hx.1 hx.2 hy.1 hy.2
      have hp : 2 ^ ((x.leaves * B + x.operations) + (y.leaves * B + y.operations)) ≤
          2 ^ ((RationalExpr.mul x y).leaves * B + (RationalExpr.mul x y).operations) := by
        apply Nat.pow_le_pow_right (by decide : 0 < 2)
        simp only [RationalExpr.leaves, RationalExpr.operations]
        nlinarith
      exact ⟨hm.1.trans hp, hm.2.trans hp⟩
  | div x y ihx ihy =>
      have hx := ihx h.1
      have hy := ihy h.2
      have hd := KS.W30.div_parts_le_two_pow x.eval y.eval
        (x.leaves * B + x.operations) (y.leaves * B + y.operations)
        hx.1 hx.2 hy.1 hy.2
      have hp : 2 ^ ((x.leaves * B + x.operations) + (y.leaves * B + y.operations)) ≤
          2 ^ ((RationalExpr.div x y).leaves * B + (RationalExpr.div x y).operations) := by
        apply Nat.pow_le_pow_right (by decide : 0 < 2)
        simp only [RationalExpr.leaves, RationalExpr.operations]
        nlinarith
      exact ⟨hd.1.trans hp, hd.2.trans hp⟩
  | neg x ih =>
      have hx := ih h
      have hp : 2 ^ (x.leaves * B + x.operations) ≤
          2 ^ ((RationalExpr.neg x).leaves * B + (RationalExpr.neg x).operations) := by
        apply Nat.pow_le_pow_right (by decide : 0 < 2)
        simp [RationalExpr.leaves, RationalExpr.operations]
      simpa [RationalExpr.eval] using And.intro (hx.1.trans hp) (hx.2.trans hp)

theorem RationalExpr.eval_parts_le_of_operations (e : RationalExpr) (B : ℕ)
    (h : e.inputsBounded B) :
    e.eval.num.natAbs ≤ 2 ^ ((e.operations + 1) * (B + 1)) ∧
      e.eval.den ≤ 2 ^ ((e.operations + 1) * (B + 1)) := by
  have hparts := e.eval_parts_le B h
  have hleaves := e.leaves_le_operations_add_one
  have hp : 2 ^ (e.leaves * B + e.operations) ≤ 2 ^ ((e.operations + 1) * (B + 1)) := by
    apply Nat.pow_le_pow_right (by decide : 0 < 2)
    nlinarith [Nat.mul_le_mul_right B hleaves]
  exact ⟨hparts.1.trans hp, hparts.2.trans hp⟩

inductive RationalExpr.IsSubexpression : RationalExpr → RationalExpr → Prop
  | refl (e) : IsSubexpression e e
  | add_left {e x y} : IsSubexpression e x → IsSubexpression e (.add x y)
  | add_right {e x y} : IsSubexpression e y → IsSubexpression e (.add x y)
  | sub_left {e x y} : IsSubexpression e x → IsSubexpression e (.sub x y)
  | sub_right {e x y} : IsSubexpression e y → IsSubexpression e (.sub x y)
  | mul_left {e x y} : IsSubexpression e x → IsSubexpression e (.mul x y)
  | mul_right {e x y} : IsSubexpression e y → IsSubexpression e (.mul x y)
  | div_left {e x y} : IsSubexpression e x → IsSubexpression e (.div x y)
  | div_right {e x y} : IsSubexpression e y → IsSubexpression e (.div x y)
  | neg {e x} : IsSubexpression e x → IsSubexpression e (.neg x)

theorem RationalExpr.IsSubexpression.inputsBounded {e root : RationalExpr}
    (h : e.IsSubexpression root) (B : ℕ) (hb : root.inputsBounded B) : e.inputsBounded B := by
  induction h with
  | refl => exact hb
  | add_left h ih | sub_left h ih | mul_left h ih | div_left h ih => exact ih hb.1
  | add_right h ih | sub_right h ih | mul_right h ih | div_right h ih => exact ih hb.2
  | neg h ih => exact ih hb

theorem RationalExpr.IsSubexpression.operations_le {e root : RationalExpr}
    (h : e.IsSubexpression root) : e.operations ≤ root.operations := by
  induction h <;> simp_all [RationalExpr.operations] <;> omega

theorem RationalExpr.IsSubexpression.eval_parts_le {e root : RationalExpr}
    (h : e.IsSubexpression root) (B : ℕ) (hb : root.inputsBounded B) :
    e.eval.num.natAbs ≤ 2 ^ ((root.operations + 1) * (B + 1)) ∧
      e.eval.den ≤ 2 ^ ((root.operations + 1) * (B + 1)) := by
  have he := e.eval_parts_le_of_operations B (h.inputsBounded B hb)
  have hp : 2 ^ ((e.operations + 1) * (B + 1)) ≤
      2 ^ ((root.operations + 1) * (B + 1)) := by
    apply Nat.pow_le_pow_right (by decide : 0 < 2)
    exact Nat.mul_le_mul_right _ (Nat.add_le_add_right h.operations_le 1)
  exact ⟨he.1.trans hp, he.2.trans hp⟩

end KS.W17

end OAI
