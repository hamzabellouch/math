import Mathlib

namespace OAI

section

namespace KS.W23

inductive NaturalPolynomial where
  | constant : ℕ → NaturalPolynomial
  | variable : NaturalPolynomial
  | add : NaturalPolynomial → NaturalPolynomial → NaturalPolynomial
  | mul : NaturalPolynomial → NaturalPolynomial → NaturalPolynomial
  | power : NaturalPolynomial → ℕ → NaturalPolynomial
  deriving Repr

namespace NaturalPolynomial
instance (value : ℕ) : OfNat NaturalPolynomial value := ⟨constant value⟩
instance : Add NaturalPolynomial := ⟨add⟩
instance : Mul NaturalPolynomial := ⟨mul⟩
instance : Pow NaturalPolynomial ℕ := ⟨power⟩

def eval : NaturalPolynomial → ℕ → ℕ
  | .constant c, _ => c
  | .variable, x => x
  | .add p q, x => p.eval x + q.eval x
  | .mul p q, x => p.eval x * q.eval x
  | .power p k, x => p.eval x ^ k

def degree : NaturalPolynomial → ℕ
  | .constant _ => 0
  | .variable => 1
  | .add p q => max p.degree q.degree
  | .mul p q => p.degree + q.degree
  | .power p k => p.degree * k

def coefficient (p : NaturalPolynomial) : ℕ := p.eval 1

@[simp] theorem eval_constant (c x : ℕ) : (constant c).eval x = c := rfl
@[simp] theorem eval_variable (x : ℕ) : variable.eval x = x := rfl
@[simp] theorem eval_add (p q : NaturalPolynomial) (x : ℕ) :
    (p + q).eval x = p.eval x + q.eval x := rfl
@[simp] theorem eval_mul (p q : NaturalPolynomial) (x : ℕ) :
    (p * q).eval x = p.eval x * q.eval x := rfl
@[simp] theorem eval_power (p : NaturalPolynomial) (k x : ℕ) :
    (p ^ k).eval x = p.eval x ^ k := rfl
@[simp] theorem eval_numeral (n x : ℕ) : (OfNat.ofNat n : NaturalPolynomial).eval x = n := rfl

theorem eval_mono (p : NaturalPolynomial) : Monotone p.eval := by
  intro x y hxy
  induction p with
  | constant c => exact le_rfl
  | «variable» => exact hxy
  | add p q hp hq => exact Nat.add_le_add hp hq
  | mul p q hp hq => exact Nat.mul_le_mul hp hq
  | power p k hp => exact Nat.pow_le_pow_left hp k

theorem eval_le_coefficient_mul_pow (p : NaturalPolynomial) {x M : ℕ}
    (hM : 1 ≤ M) (hx : x ≤ M) : p.eval x ≤ p.coefficient * M ^ p.degree := by
  induction p with
  | constant c => simp [coefficient, eval, degree]
  | «variable» => simpa [coefficient, eval, degree] using hx
  | add p q hp hq =>
      have hp' := hp.trans (Nat.mul_le_mul_left p.coefficient
        (Nat.pow_le_pow_right hM (Nat.le_max_left p.degree q.degree)))
      have hq' := hq.trans (Nat.mul_le_mul_left q.coefficient
        (Nat.pow_le_pow_right hM (Nat.le_max_right p.degree q.degree)))
      simpa [coefficient, eval, degree, Nat.add_mul] using Nat.add_le_add hp' hq'
  | mul p q hp hq =>
      have h := Nat.mul_le_mul hp hq
      simpa [coefficient, eval, degree, pow_add, Nat.mul_assoc, Nat.mul_left_comm,
        Nat.mul_comm] using h
  | power p k hp =>
      have h := Nat.pow_le_pow_left hp k
      simpa [coefficient, eval, degree, mul_pow, pow_mul] using h

theorem eval_le_input_polynomial (p : NaturalPolynomial) (L : ℕ) :
    p.eval L ≤ p.coefficient * (L + 1) ^ p.degree :=
  p.eval_le_coefficient_mul_pow (Nat.succ_le_succ (Nat.zero_le L)) (Nat.le_succ L)

theorem eval_le_of_size_bound (p : NaturalPolynomial) {x L A e : ℕ}
    (hA : 1 ≤ A) (hx : x ≤ A * (L + 1) ^ e) :
    p.eval x ≤ p.coefficient * A ^ p.degree * (L + 1) ^ (e * p.degree) := by
  have hbase : 1 ≤ A * (L + 1) ^ e :=
    by simpa using Nat.mul_le_mul hA (Nat.one_le_pow' e L)
  have h := p.eval_le_coefficient_mul_pow hbase hx
  simpa only [mul_pow, ← pow_mul, Nat.mul_assoc] using h

end NaturalPolynomial
end KS.W23

end

end OAI
