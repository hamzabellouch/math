import Mathlib

namespace OAI

namespace PolynomialVacuumAlgebra

inductive Spin | zero | plus | minus
  deriving DecidableEq

instance : Fintype Spin := ⟨{Spin.zero, Spin.plus, Spin.minus}, by
  intro s; cases s <;> simp⟩

def charge : Spin → ℤ | .zero => 0 | .plus => 1 | .minus => -1

noncomputable def q : ℂ := Complex.exp (Complex.I * (Real.pi / 8))
noncomputable def t : ℂ := q^2
noncomputable def T : ℂ := t^3
noncomputable def zeta : ℂ := t^2
noncomputable def xStar : ℂ := ((Real.sqrt (2 + Real.sqrt 2))⁻¹ : ℝ)
noncomputable def nZero : ℂ := (Real.sqrt 2 : ℝ) - 1

abbrev Pair := Spin × Spin

noncomputable def cup (ab : Pair) : ℂ :=
  if charge ab.1 + charge ab.2 = 0 then q ^ (5 * charge ab.1) else 0

noncomputable def insertion (ab : Pair) (h : Spin) : ℂ :=
  if charge ab.1 + charge ab.2 ≠ charge h then 0 else
  match ab with
  | (.zero,.zero) => 1
  | (.zero,b) => xStar * q ^ (-charge b)
  | (a,.zero) => xStar * q ^ charge a
  | (a,_) => xStar * q ^ (4 * charge a)

noncomputable def Pzero : Matrix Pair Pair ℂ := fun a b => -cup a * cup b / nZero
noncomputable def Pone : Matrix Pair Pair ℂ := fun a b =>
  (∑ h : Spin, insertion a h * insertion b h) / nZero
noncomputable def Ptwo : Matrix Pair Pair ℂ := 1 - Pone - Pzero

 
noncomputable def exchangeDenominator (x y : ℂ) : ℂ := (t^2*x-y)*(T*x-y)
noncomputable def exchangeNumerator (x y : ℂ) : Matrix Pair Pair ℂ :=
  ((t^2*y-x)*(T*x-y)) • Pzero +
  ((T*y-x)*(t^2*x-y)) • Pone +
  ((t^2*y-x)*(T*y-x)) • Ptwo

abbrev State (N : ℕ) := (Fin N → Spin) → MvPolynomial (Fin N) ℂ
abbrev Family := (N : ℕ) → State N

 
def pairLeft {n : ℕ} (i : Fin (n+1)) : Fin (n+2) := i.castSucc
def pairRight {n : ℕ} (i : Fin (n+1)) : Fin (n+2) := i.succ

def omitPair {n : ℕ} (i : Fin (n+1)) (j : Fin n) : Fin (n+2) :=
  ⟨if j.val < i.val then j.val else j.val+2, by split_ifs <;> omega⟩

noncomputable def fusionScalar {n : ℕ} (a : ℂ) (Y : Fin n → ℂ) : ℂ :=
  (1+T)*a * ∏ j, (Y j-t^5*a)*(Y j-t^6*a)

 
def IsPolynomialVacuum (ψ : Family) : Prop :=
  (∀ s : Fin 0 → Spin, ψ 0 s = 1) ∧
  (∀ s : Fin 1 → Spin, ψ 1 s = if s 0 = Spin.zero then 1 else 0) ∧
  (∀ N s, (∑ i, charge (s i)) ≠ 0 → ψ N s = 0) ∧
  (∀ N s, (ψ N s).IsHomogeneous (N.choose 2)) ∧
  (∀ N s i, (ψ N s).degreeOf i ≤ N-1) ∧
  (∀ N s i, s i = Spin.plus → (ψ N s).degreeOf i ≤ N-2) ∧
  (∀ N s i (X : Fin N → ℂ), s i = Spin.minus → X i = 0 →
    MvPolynomial.eval X (ψ N s) = 0) ∧
  (∀ n (i : Fin (n+1)) (s : Fin (n+2) → Spin) (X : Fin (n+2) → ℂ),
    (∑ ab : Pair,
      exchangeNumerator (X (pairLeft i)) (X (pairRight i))
        (s (pairLeft i),s (pairRight i)) ab *
      MvPolynomial.eval X (ψ (n+2)
        (Function.update (Function.update s (pairLeft i) ab.1) (pairRight i) ab.2))) =
    exchangeDenominator (X (pairLeft i)) (X (pairRight i)) *
      MvPolynomial.eval (X ∘ Equiv.swap (pairLeft i) (pairRight i)) (ψ (n+2) s)) ∧
  (∀ n (s : Fin (n+1) → Spin) (X : Fin (n+1) → ℂ),
    zeta ^ charge (s 0) * MvPolynomial.eval X (ψ (n+1) (s ∘ finRotate (n+1))) =
      MvPolynomial.eval (X ∘ (finRotate (n+1)).symm) (ψ (n+1) s)) ∧
  (∀ n (i : Fin (n+1)) (s : Fin (n+2) → Spin) (X : Fin (n+2) → ℂ),
    X (pairRight i) = T * X (pairLeft i) →
    MvPolynomial.eval X (ψ (n+2) s) =
      fusionScalar (X (pairLeft i)) (X ∘ omitPair i) *
      cup (s (pairLeft i),s (pairRight i)) *
      MvPolynomial.eval (X ∘ omitPair i) (ψ n (s ∘ omitPair i))) ∧
  (∀ n (s : Fin (n+1) → Spin) (X : Fin (n+1) → ℂ),
    s (Fin.last n) = Spin.zero → X (Fin.last n) = 0 →
    MvPolynomial.eval X (ψ (n+1) s) =
      (∏ j : Fin n, X j.castSucc) *
      MvPolynomial.eval (X ∘ Fin.castSucc) (ψ n (s ∘ Fin.castSucc)))

def PolynomialVacuumExists : Prop := ∃ ψ : Family, IsPolynomialVacuum ψ

end PolynomialVacuumAlgebra

end OAI
