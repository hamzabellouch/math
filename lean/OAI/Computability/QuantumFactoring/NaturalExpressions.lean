import Mathlib

namespace OAI

section
open scoped BigOperators


/-! A finite straight-line expression language for the exact rational formulas
in the manuscript. All values are natural numbers, not unit-cost hidden gates.
The following compiler will realize these operations with actual bit networks. -/
namespace ExactQuantumFactoring

inductive NatExpr (v : Type*) where
  | var : v → NatExpr v
  | const : ℕ → NatExpr v
  | add : NatExpr v → NatExpr v → NatExpr v
  | mul : NatExpr v → NatExpr v → NatExpr v
  | sub : NatExpr v → NatExpr v → NatExpr v
  | div : NatExpr v → NatExpr v → NatExpr v
  | mod : NatExpr v → NatExpr v → NatExpr v
  | iteLe : NatExpr v → NatExpr v → NatExpr v → NatExpr v → NatExpr v
  deriving Inhabited

namespace NatExpr
variable {v : Type*}

def eval (x : v → ℕ) : NatExpr v → ℕ
  | .var i => x i
  | .const c => c
  | .add a b => eval x a+eval x b
  | .mul a b => eval x a*eval x b
  | .sub a b => eval x a-eval x b
  | .div a b => eval x a/eval x b
  | .mod a b => eval x a%eval x b
  | .iteLe a b c d => if eval x a ≤ eval x b then eval x c else eval x d

def size : NatExpr v → ℕ
  | .var _ | .const _ => 1
  | .add a b | .mul a b | .sub a b | .div a b | .mod a b => size a+size b+1
  | .iteLe a b c d => size a+size b+size c+size d+1

def constOK (B : ℕ) : NatExpr v → Prop
  | .var _ => True
  | .const c => c < B
  | .add a b | .mul a b | .sub a b | .div a b | .mod a b => constOK B a ∧ constOK B b
  | .iteLe a b c d => constOK B a ∧ constOK B b ∧ constOK B c ∧ constOK B d

lemma size_pos (e : NatExpr v) : 0 < e.size := by cases e <;> simp [size]

lemma value_bound (B : ℕ) (hB : 2 ≤ B) (x : v → ℕ) (hx : ∀ i, x i < B)
    (e : NatExpr v) (hc : e.constOK B) : e.eval x < B^e.size := by
  induction e with
  | var i => simpa [eval,size] using hx i
  | const c => simpa [eval,size,constOK] using hc
  | add a b ia ib =>
    have ha := ia hc.1
    have hb := ib hc.2
    have h₁ : a.eval x+b.eval x+1 ≤ (a.eval x+1)*(b.eval x+1) := by nlinarith
    have h₂ := Nat.mul_le_mul (Nat.succ_le_of_lt ha) (Nat.succ_le_of_lt hb)
    have h₃ : B^(a.size+b.size) ≤ B^(a.size+b.size+1) := Nat.pow_le_pow_right (by omega) (by omega)
    simp only [eval,size]
    rw [← pow_add] at h₂
    simp only [Nat.succ_eq_add_one] at h₂
    omega
  | mul a b ia ib =>
    have ha := ia hc.1
    have hb := ib hc.2
    have h₁ : a.eval x*b.eval x+1 ≤ (a.eval x+1)*(b.eval x+1) := by nlinarith
    have h₂ := Nat.mul_le_mul (Nat.succ_le_of_lt ha) (Nat.succ_le_of_lt hb)
    have h₃ : B^(a.size+b.size) ≤ B^(a.size+b.size+1) := Nat.pow_le_pow_right (by omega) (by omega)
    simp only [eval,size]
    rw [← pow_add] at h₂
    simp only [Nat.succ_eq_add_one] at h₂
    omega
  | sub a b ia _ =>
    exact (Nat.sub_le _ _).trans_lt ((ia hc.1).trans_le
      (Nat.pow_le_pow_right (by omega) (by simp [size]; omega)))
  | div a b ia _ =>
    exact (Nat.div_le_self _ _).trans_lt ((ia hc.1).trans_le
      (Nat.pow_le_pow_right (by omega) (by simp [size]; omega)))
  | mod a b ia _ =>
    exact (Nat.mod_le _ _).trans_lt ((ia hc.1).trans_le
      (Nat.pow_le_pow_right (by omega) (by simp [size]; omega)))
  | iteLe a b c d _ _ ic id =>
    simp only [eval]
    split_ifs
    · exact (ic hc.2.2.1).trans_le (Nat.pow_le_pow_right (by omega) (by simp [size]; omega))
    · exact (id hc.2.2.2).trans_le (Nat.pow_le_pow_right (by omega) (by simp [size]; omega))

/-- Every intermediate value fits, not merely the eventual answer. -/
def Fits (B : ℕ) (x : v → ℕ) (e : NatExpr v) : Prop :=
  e.eval x < B ∧ match e with
    | .var _ | .const _ => True
    | .add a b | .mul a b | .sub a b | .div a b | .mod a b => Fits B x a ∧ Fits B x b
    | .iteLe a b c d => Fits B x a ∧ Fits B x b ∧ Fits B x c ∧ Fits B x d

lemma Fits.mono {B C : ℕ} (hBC : B ≤ C) {x : v → ℕ} {e : NatExpr v}
    (h : Fits B x e) : Fits C x e := by
  induction e with
  | var _ | const _ => exact ⟨h.1.trans_le hBC,trivial⟩
  | add a b ia ib | mul a b ia ib | sub a b ia ib | div a b ia ib | mod a b ia ib =>
    exact ⟨h.1.trans_le hBC,ia h.2.1,ib h.2.2⟩
  | iteLe a b c d ia ib ic id =>
    exact ⟨h.1.trans_le hBC,ia h.2.1,ib h.2.2.1,ic h.2.2.2.1,id h.2.2.2.2⟩

lemma fits_bound (B : ℕ) (hB : 2 ≤ B) (x : v → ℕ) (hx : ∀ i, x i < B)
    (e : NatExpr v) (hc : e.constOK B) : Fits (B^e.size) x e := by
  induction e with
  | var i | const i => exact ⟨value_bound B hB x hx _ hc,trivial⟩
  | add a b ia ib | mul a b ia ib | sub a b ia ib | div a b ia ib | mod a b ia ib =>
    refine ⟨value_bound B hB x hx _ hc,?_,?_⟩
    · exact (ia hc.1).mono (Nat.pow_le_pow_right (by omega) (by simp [size]; omega))
    · exact (ib hc.2).mono (Nat.pow_le_pow_right (by omega) (by simp [size]; omega))
  | iteLe a b c d ia ib ic id =>
    refine ⟨value_bound B hB x hx _ hc,?_,?_,?_,?_⟩
    · exact (ia hc.1).mono (Nat.pow_le_pow_right (by omega) (by simp [size]; omega))
    · exact (ib hc.2.1).mono (Nat.pow_le_pow_right (by omega) (by simp [size]; omega))
    · exact (ic hc.2.2.1).mono (Nat.pow_le_pow_right (by omega) (by simp [size]; omega))
    · exact (id hc.2.2.2).mono (Nat.pow_le_pow_right (by omega) (by simp [size]; omega))

lemma fits_bits {b : ℕ} (hb : 1 ≤ b) (x : v → ℕ) (hx : ∀ i, x i < 2^b)
    (e : NatExpr v) (hc : e.constOK (2^b)) : Fits (2^(b*e.size)) x e := by
  rw [pow_mul]
  exact fits_bound (2^b) (Nat.one_lt_two_pow (by omega)) x hx e hc

end NatExpr
end ExactQuantumFactoring


end

end OAI
