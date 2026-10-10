import OAI.Combinatorics.ContingencyTables.Transport.RationalWalks
import OAI.Combinatorics.MatchingCount.Complexity.TreePolynomialSums

namespace OAI

/-! # Integer propagation tabulates adaptive finite laws without random tapes -/

namespace ContingencyTables.IntegerPropagation
open ResidualMixture FirstSuccess
open scoped BigOperators Classical

variable {A : Type*} [Fintype A] [DecidableEq A]
variable (B : A → A → ℕ) (Q : ℕ)

def numerators (start : A) : ℕ → A → ℕ
  | 0,y => if y=start then 1 else 0
  | n+1,y => ∑ x,numerators start n x*B x y

lemma numerators_total (hrow : ∀ x,∑ y,B x y=Q) (start : A) (n : ℕ) :
    ∑ y,numerators B start n y=Q^n := by
  induction n with
  | zero => simp [numerators]
  | succ n ih =>
    simp only [numerators]
    rw [Finset.sum_comm]
    simp_rw [←Finset.mul_sum,hrow]
    rw [←Finset.sum_mul,ih,pow_succ]

lemma numerator_le (hrow : ∀ x,∑ y,B x y=Q) (start : A) (n : ℕ) (y : A) :
    numerators B start n y≤Q^n := by
  rw [←numerators_total B Q hrow start n]
  exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ y)

/-- One row of a dyadic transition table, viewed as an exact rational law. -/
def kernel (hQ : 0<Q) (hrow : ∀ x,∑ y,B x y=Q) (x : A) : RationalLaw A where
  mass y := (B x y:ℚ)/Q
  nonnegative y := by positivity
  total := by
    rw [←Finset.sum_div,←Nat.cast_sum,hrow]
    exact div_self (by exact_mod_cast hQ.ne')

/-- Matrix/vector propagation accounts for all adaptive paths with one
integer per state; its denominator exponent grows only with the steps. -/
theorem numerators_walkLaw (hQ : 0<Q) (hrow : ∀ x,∑ y,B x y=Q)
    (start : A) (n : ℕ) (y : A) :
    (numerators B start n y:ℚ)/(Q:ℚ)^n=(walkLaw (kernel B Q hQ hrow) start n).mass y := by
  induction n generalizing y with
  | zero => simp [numerators,walkLaw,pointLaw]
  | succ n ih =>
    simp only [numerators,Nat.cast_sum,Nat.cast_mul,walkLaw,bindLaw,kernel,pow_succ]
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro x _
    rw [←ih x]
    exact (div_mul_div_comm _ _ _ _).symm

end ContingencyTables.IntegerPropagation

end OAI
