import OAI.Combinatorics.EditApproximation.Binary.BinaryAffineGuard

namespace OAI

/-! A structural polynomial bound for finite Boolean arithmetic loops.
The expression language includes only operations whose magnitude is bounded
by a fixed power of a common input bound. -/

namespace EditApproximation

inductive FiniteBitPolynomial (ι : Type*) where
  | input (i : ι)
  | constant (n : ℕ)
  | add (a b : FiniteBitPolynomial ι)
  | mul (a b : FiniteBitPolynomial ι)
  | pow (a : FiniteBitPolynomial ι) (n : ℕ)
  | maximum (a b : FiniteBitPolynomial ι)
  | minimum (a b : FiniteBitPolynomial ι)
  | bitLength (a : FiniteBitPolynomial ι)

namespace FiniteBitPolynomial

instance {ι : Type*} (n : ℕ) : OfNat (FiniteBitPolynomial ι) n := ⟨.constant n⟩
instance {ι : Type*} : Add (FiniteBitPolynomial ι) := ⟨.add⟩
instance {ι : Type*} : Mul (FiniteBitPolynomial ι) := ⟨.mul⟩
instance {ι : Type*} : Pow (FiniteBitPolynomial ι) ℕ := ⟨.pow⟩

def eval {ι : Type*} (env : ι → ℕ) : FiniteBitPolynomial ι → ℕ
  | .input i => env i
  | .constant n => n
  | .add a b => a.eval env + b.eval env
  | .mul a b => a.eval env * b.eval env
  | .pow a n => a.eval env ^ n
  | .maximum a b => max (a.eval env) (b.eval env)
  | .minimum a b => min (a.eval env) (b.eval env)
  | .bitLength a => Nat.size (a.eval env)

def degree {ι : Type*} : FiniteBitPolynomial ι → ℕ
  | .input _ => 1
  | .constant n => Nat.size n
  | .add a b => max a.degree b.degree + 1
  | .mul a b => a.degree + b.degree
  | .pow a n => a.degree * n
  | .maximum a b => max a.degree b.degree
  | .minimum a b => max a.degree b.degree
  | .bitLength a => a.degree

theorem eval_le_pow {ι : Type*} (p : FiniteBitPolynomial ι) (env : ι → ℕ)
    (S : ℕ) (hS : 2 ≤ S) (henv : ∀ i, env i ≤ S) :
    p.eval env ≤ S ^ p.degree := by
  induction p with
  | input i => simpa only [eval, degree, pow_one] using henv i
  | constant n =>
    exact (Nat.lt_size_self n).le.trans (Nat.pow_le_pow_left hS _)
  | add a b ha hb =>
    have ha' := ha.trans (Nat.pow_le_pow_right (by omega : 0 < S) (Nat.le_max_left a.degree b.degree))
    have hb' := hb.trans (Nat.pow_le_pow_right (by omega : 0 < S) (Nat.le_max_right a.degree b.degree))
    change a.eval env + b.eval env ≤ S ^ (max a.degree b.degree + 1)
    calc
      _ ≤ 2 * S ^ max a.degree b.degree := by omega
      _ ≤ S * S ^ max a.degree b.degree := Nat.mul_le_mul_right _ hS
      _ = _ := (pow_succ' S _).symm
  | mul a b ha hb =>
    exact (Nat.mul_le_mul ha hb).trans_eq (pow_add S a.degree b.degree).symm
  | pow a n ha =>
    exact (Nat.pow_le_pow_left ha n).trans_eq (pow_mul S a.degree n).symm
  | maximum a b ha hb =>
    exact max_le
      (ha.trans (Nat.pow_le_pow_right (by omega) (Nat.le_max_left a.degree b.degree)))
      (hb.trans (Nat.pow_le_pow_right (by omega) (Nat.le_max_right a.degree b.degree)))
  | minimum a b ha _ =>
    exact (Nat.min_le_left _ _).trans
      (ha.trans (Nat.pow_le_pow_right (by omega) (Nat.le_max_left a.degree b.degree)))
  | bitLength a ha =>
    exact (Nat.size_le.mpr Nat.lt_two_pow_self).trans ha

end FiniteBitPolynomial
end EditApproximation

end OAI
