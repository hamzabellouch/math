import Mathlib
import OAI.Computability.MaxCut.Model

namespace OAI

/-!
# Separation of polynomial parity classes

The genericity argument uses monomials with distinct squarefree
exponent vectors. Polynomial coefficients in the original «variables» become
polynomials in squares after adjoining their square roots. The lemmas below
prove the resulting coefficient separation directly, without assuming an
algebraic independence witness.
-/

namespace MaxCutGames.Quadratic

open MvPolynomial
open scoped BigOperators

variable {σ ι R : Type*} [CommSemiring R]

/-- Exponents zero or one represent parity classes. -/
def SquarefreeExponent (a : σ →₀ ℕ) : Prop := ∀ k, a k < 2

/-- Two different squarefree shifts have disjoint expanded supports. -/
theorem coeff_expand_mul_monomial_of_ne
    (p : MvPolynomial σ R) (a b n : σ →₀ ℕ)
    (ha : SquarefreeExponent a) (hb : SquarefreeExponent b) (hab : a ≠ b) :
    (expand 2 p * monomial b 1).coeff (2 • n + a) = 0 := by
  classical
  rw [coeff_mul_monomial']
  split_ifs with hle
  · obtain ⟨k, hk⟩ : ∃ k, a k ≠ b k := by
      by_contra h
      push Not at h
      exact hab (Finsupp.ext h)
    have hcoeff : (expand 2 p).coeff (2 • n + a - b) = 0 := by
      apply coeff_expand_of_not_dvd (i := k)
      intro hdiv
      obtain ⟨m, hm⟩ := hdiv
      have hle' := hle k
      have ha' := ha k
      have hb' := hb k
      simp only [Finsupp.tsub_apply, Finsupp.add_apply, Finsupp.smul_apply,
        smul_eq_mul] at hm hle'
      omega
    simp [hcoeff]
  · rfl

/-- Within one parity class coefficient extraction recovers the coefficient
before expansion. -/
theorem coeff_expand_mul_monomial_self
    (p : MvPolynomial σ R) (a n : σ →₀ ℕ) :
    (expand 2 p * monomial a 1).coeff (2 • n + a) = p.coeff n := by
  rw [coeff_mul_monomial, coeff_expand_smul 2 (by decide), mul_one]

/-- Extraction from a finite sum isolates its unique parity class. -/
theorem coeff_sum_expand_mul_monomial [Fintype ι]
    (e : ι → σ →₀ ℕ) (he : ∀ i, SquarefreeExponent (e i))
    (hinj : Function.Injective e) (p : ι → MvPolynomial σ R)
    (i : ι) (n : σ →₀ ℕ) :
    (∑ j, expand 2 (p j) * monomial (e j) 1).coeff (2 • n + e i) =
      (p i).coeff n := by
  classical
  rw [coeff_sum]
  rw [Finset.sum_eq_single i]
  · exact coeff_expand_mul_monomial_self _ _ _
  · intro j _ hji
    exact coeff_expand_mul_monomial_of_ne _ _ _ _ (he i) (he j)
      (fun h => hji (hinj h).symm)
  · simp

/-- A polynomial dependence between distinct squarefree parity classes is
trivial, even when each coefficient is itself an arbitrary polynomial in the
squared «variables». -/
theorem sum_expand_mul_monomial_eq_zero_iff [Fintype ι]
    (e : ι → σ →₀ ℕ) (he : ∀ i, SquarefreeExponent (e i))
    (hinj : Function.Injective e) (p : ι → MvPolynomial σ R) :
    (∑ i, expand 2 (p i) * monomial (e i) 1) = 0 ↔ ∀ i, p i = 0 := by
  constructor
  · intro h i
    ext n
    have hc := congrArg (fun q : MvPolynomial σ R => q.coeff (2 • n + e i)) h
    simpa only [coeff_sum_expand_mul_monomial e he hinj,
      AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] using hc
  · intro h
    simp [h]

noncomputable def blockExponent {κ J : Type*} [Finite κ] [Finite J]
    (v : κ → J) : (κ × J) →₀ ℕ := by
  classical
  exact Finsupp.equivFunOnFinite.symm (fun x => if x.2 = v x.1 then 1 else 0)

@[simp] theorem blockExponent_apply {κ J : Type*} [Finite κ] [Finite J] [DecidableEq J]
    (v : κ → J) (x : κ × J) :
    blockExponent v x = if x.2 = v x.1 then 1 else 0 := by
  classical
  by_cases h : x.2 = v x.1 <;> simp [blockExponent, h]

theorem blockExponent_squarefree {κ J : Type*} [Finite κ] [Finite J]
    (v : κ → J) : SquarefreeExponent (blockExponent v) := by
  classical
  intro x
  simp only [blockExponent_apply]
  split_ifs <;> decide

theorem blockExponent_injective {κ J : Type*} [Finite κ] [Finite J] :
    Function.Injective (blockExponent (κ := κ) (J := J)) := by
  classical
  intro v w h
  funext i
  have hc := congrArg (fun e : (κ × J) →₀ ℕ => e (i, v i)) h
  by_contra hne
  simp [hne] at hc

theorem blockExponent_eq_sum {κ J : Type*} [Fintype κ] [Finite J]
    (v : κ → J) :
    blockExponent v = ∑ i, Finsupp.single (i, v i) 1 := by
  classical
  ext x
  rw [blockExponent_apply, Finsupp.finsetSum_apply]
  symm
  rw [Finset.sum_eq_single x.1]
  · simp [Finsupp.single_apply, Prod.ext_iff, eq_comm]
  · intro i _ hi
    have hix : (i, v i) ≠ x := fun h => hi (congrArg Prod.fst h)
    simp [hix]
  · simp

theorem monomial_blockExponent {κ J : Type*} [Fintype κ] [Finite J]
    (v : κ → J) :
    (monomial (blockExponent v) 1 : MvPolynomial (κ × J) R) =
      ∏ i, X (i, v i) := by
  rw [blockExponent_eq_sum, monomial_sum_one]
  rfl

/-- In particular the three-block monomials have independent polynomial
coefficients after squaring the «variables». -/
theorem sum_expand_mul_blockMonomial_eq_zero_iff {J : Type*} [Fintype J]
    (p : (Fin 3 → J) → MvPolynomial (Fin 3 × J) R) :
    (∑ v, expand 2 (p v) * monomial (blockExponent v) 1) = 0 ↔
      ∀ v, p v = 0 :=
  sum_expand_mul_monomial_eq_zero_iff blockExponent blockExponent_squarefree
    blockExponent_injective p

end MaxCutGames.Quadratic

end OAI
