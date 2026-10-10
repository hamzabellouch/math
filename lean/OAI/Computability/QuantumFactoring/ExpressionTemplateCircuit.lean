import Mathlib
import OAI.Computability.QuantumFactoring.WordResize
import OAI.Computability.QuantumFactoring.NaturalExpressionCircuit

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring
open BooleanNetwork BitArithmetic
namespace NatExpr
variable {v : Type*}

def maxConst : NatExpr v → ℕ
  | .var _ => 0
  | .const c => c
  | .add a b | .mul a b | .sub a b | .div a b | .mod a b => max a.maxConst b.maxConst
  | .iteLe a b c d => max (max a.maxConst b.maxConst) (max c.maxConst d.maxConst)

lemma constOK_of_maxConst_lt (e : NatExpr v) {B : ℕ} (h : e.maxConst < B) : e.constOK B := by
  induction e with
  | var i => trivial
  | const c => exact h
  | add a b ia ib | mul a b ia ib | sub a b ia ib | div a b ia ib | mod a b ia ib =>
    exact ⟨ia (lt_of_le_of_lt (le_max_left _ _) h),ib (lt_of_le_of_lt (le_max_right _ _) h)⟩
  | iteLe a b c d ia ib ic id =>
    have h₁ : max a.maxConst b.maxConst < B := lt_of_le_of_lt (le_max_left _ _) h
    have h₂ : max c.maxConst d.maxConst < B := lt_of_le_of_lt (le_max_right _ _) h
    exact ⟨ia (lt_of_le_of_lt (le_max_left _ _) h₁),ib (lt_of_le_of_lt (le_max_right _ _) h₁),
      ic (lt_of_le_of_lt (le_max_left _ _) h₂),id (lt_of_le_of_lt (le_max_right _ _) h₂)⟩

def templateWidth (e : NatExpr v) (b : ℕ) : ℕ := (b+e.maxConst.size+1)*e.size
lemma le_templateWidth (e : NatExpr v) (b : ℕ) : b ≤ e.templateWidth b := by
  have h := Nat.le_mul_of_pos_right (b+e.maxConst.size+1) e.size_pos
  dsimp [templateWidth]
  omega

def template {k b : ℕ} (e : NatExpr v) (vars : v → BooleanNetwork k b) :
    BooleanNetwork k (e.templateWidth b) :=
  e.compile (fun i => (vars i).comp (resizeWord b (e.templateWidth b)))

lemma template_value {k b : ℕ} (e : NatExpr v) (vars : v → BooleanNetwork k b) (x : Basis k) :
    (bitsValue ((e.template vars).eval x)).toNat =
      e.eval (fun i => (bitsValue ((vars i).eval x)).toNat) := by
  have hv : (fun i => (bitsValue (((vars i).comp (resizeWord b (e.templateWidth b))).eval x)).toNat)=
      (fun i => (bitsValue ((vars i).eval x)).toNat) := by
    funext i
    rw [eval_comp,resizeWord_toNat (le_templateWidth e b)]
  unfold template
  rw [compile_value,hv]
  rw [hv]
  apply fits_bits (by omega : 1 ≤ b+e.maxConst.size+1)
  · intro i
    exact (bitsValue ((vars i).eval x)).isLt.trans_le (Nat.pow_le_pow_right (by omega) (by omega))
  · apply e.constOK_of_maxConst_lt
    exact (Nat.lt_size_self e.maxConst).trans_le
      (Nat.pow_le_pow_right (by omega) (by omega))

lemma template_count {k b c : ℕ} (e : NatExpr v) (vars : v → BooleanNetwork k b)
    (hc : ∀ i, (vars i).net.count ≤ c) :
    (e.template vars).net.count ≤
      e.cost*(operationBound (e.templateWidth b)+c+e.templateWidth b) := by
  unfold template
  have hh := e.compile_count (fun i => (vars i).comp (resizeWord b (e.templateWidth b)))
    (c:=c+e.templateWidth b) (by
      intro i
      rw [count_comp]
      exact Nat.add_le_add (hc i) (resizeWord_count _ _))
  simpa only [Nat.add_assoc] using hh

end NatExpr
end ExactQuantumFactoring


end

end OAI
