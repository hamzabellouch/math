import Mathlib

namespace OAI

noncomputable section
open scoped BigOperators
namespace Problem335

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

/-- The product of coordinate factorials of an exponent vector. -/
def multiFactorial (d : σ →₀ ℕ) : ℕ := ∏ i, (d i).factorial

omit [DecidableEq σ] in
lemma multiFactorial_pos (d : σ →₀ ℕ) : 0 < multiFactorial d := by
  exact Finset.prod_pos (fun i _ => Nat.factorial_pos (d i))

lemma multiFactorial_add_single (d : σ →₀ ℕ) (i : σ) :
    multiFactorial (d + Finsupp.single i 1) = (d i + 1) * multiFactorial d := by
  unfold multiFactorial
  calc
    ∏ j, ((d + Finsupp.single i 1 : σ →₀ ℕ) j).factorial =
        ∏ j, (if i = j then d i + 1 else 1) * (d j).factorial := by
      apply Finset.prod_congr rfl
      intro j _
      by_cases h : i = j
      · subst j
        simp [Nat.factorial_succ]
      · simp [h]
    _ = (d i + 1) * ∏ j, (d j).factorial := by
      rw [Finset.prod_mul_distrib]
      simp

/-- A factorial-normalized real monomial, the algebraic part of the
Bargmann--Fock basis used in the moment calculation. -/
def fockMonomial (d : σ →₀ ℕ) : MvPolynomial σ ℝ :=
  MvPolynomial.monomial d (Real.sqrt (multiFactorial d : ℝ))⁻¹

omit [DecidableEq σ] in
lemma sqrt_multiFactorial_pos (d : σ →₀ ℕ) :
    0 < Real.sqrt (multiFactorial d : ℝ) := by
  exact Real.sqrt_pos.2 (by exact_mod_cast multiFactorial_pos d)

lemma sqrt_multiFactorial_add_single (d : σ →₀ ℕ) (i : σ) :
    Real.sqrt (multiFactorial (d + Finsupp.single i 1) : ℝ) =
      Real.sqrt ((d i : ℝ) + 1) * Real.sqrt (multiFactorial d : ℝ) := by
  rw [multiFactorial_add_single, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
    Real.sqrt_mul (by positivity)]

lemma X_mul_fockMonomial (d : σ →₀ ℕ) (i : σ) :
    MvPolynomial.X i * fockMonomial d =
      Real.sqrt ((d i : ℝ) + 1) • fockMonomial (d + Finsupp.single i 1) := by
  rw [fockMonomial, fockMonomial, MvPolynomial.X, MvPolynomial.monomial_mul_monomial,
    MvPolynomial.smul_monomial]
  rw [add_comm (Finsupp.single i 1) d]
  congr 1
  rw [one_mul, smul_eq_mul, sqrt_multiFactorial_add_single]
  have h : Real.sqrt ((d i : ℝ) + 1) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by positivity))
  field_simp

lemma pderiv_fockMonomial_add_single (d : σ →₀ ℕ) (i : σ) :
    MvPolynomial.pderiv i (fockMonomial (d + Finsupp.single i 1)) =
      Real.sqrt ((d i : ℝ) + 1) • fockMonomial d := by
  rw [fockMonomial, fockMonomial, MvPolynomial.pderiv_monomial,
    MvPolynomial.smul_monomial]
  simp only [add_tsub_cancel_right, Finsupp.add_apply, Finsupp.single_eq_same,
    Nat.cast_add, Nat.cast_one, smul_eq_mul]
  congr 1
  rw [sqrt_multiFactorial_add_single]
  have h₁ := Real.sq_sqrt (show 0 ≤ (d i : ℝ) + 1 by positivity)
  have h₂ : Real.sqrt ((d i : ℝ) + 1) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by positivity))
  have h₃ := (sqrt_multiFactorial_pos d).ne'
  field_simp
  nlinarith

lemma pderiv_fockMonomial (d : σ →₀ ℕ) (i : σ) :
    MvPolynomial.pderiv i (fockMonomial d) =
      Real.sqrt (d i : ℝ) • fockMonomial (d - Finsupp.single i 1) := by
  by_cases h : d i = 0
  · simp [fockMonomial, MvPolynomial.pderiv_monomial, h]
  · have hd := Finsupp.sub_add_single_one_cancel h
    have hc : ((d - Finsupp.single i 1 : σ →₀ ℕ) i : ℝ) + 1 = (d i : ℝ) := by
      have : (d - Finsupp.single i 1 : σ →₀ ℕ) i + 1 = d i := by
        simpa using congrArg (fun a : σ →₀ ℕ => a i) hd
      exact_mod_cast this
    have heq := pderiv_fockMonomial_add_single (σ := σ) (d - Finsupp.single i 1) i
    rw [hd, hc] at heq
    exact heq

/-- The normalized monomials form a basis, by rescaling the monomial basis
with nonzero coefficients. -/
def fockBasis : Module.Basis (σ →₀ ℕ) ℝ (MvPolynomial σ ℝ) :=
  (MvPolynomial.basisMonomials σ ℝ).isUnitSMul
    (fun d => IsUnit.mk0 (Real.sqrt (multiFactorial d : ℝ))⁻¹
      (inv_ne_zero (sqrt_multiFactorial_pos d).ne'))

omit [DecidableEq σ] in
lemma fockBasis_apply (d : σ →₀ ℕ) : fockBasis d = fockMonomial d := by
  simp [fockBasis, Module.Basis.isUnitSMul_apply, fockMonomial,
    MvPolynomial.smul_monomial]

/-- Complex normalized monomials are obtained by coefficient extension. -/
def complexFockMonomial (d : σ →₀ ℕ) : MvPolynomial σ ℂ :=
  MvPolynomial.map (algebraMap ℝ ℂ) (fockMonomial d)

omit [DecidableEq σ] in
lemma complexFockMonomial_eq (d : σ →₀ ℕ) :
    complexFockMonomial d = MvPolynomial.monomial d
      ((Real.sqrt (multiFactorial d : ℝ))⁻¹ : ℂ) := by
  simp [complexFockMonomial, fockMonomial]

lemma X_mul_complexFockMonomial (d : σ →₀ ℕ) (i : σ) :
    MvPolynomial.X i * complexFockMonomial d =
      (Real.sqrt ((d i : ℝ) + 1) : ℂ) • complexFockMonomial (d + Finsupp.single i 1) := by
  have h := congrArg (MvPolynomial.map (algebraMap ℝ ℂ)) (X_mul_fockMonomial d i)
  simpa [complexFockMonomial, fockMonomial, MvPolynomial.smul_monomial] using h

lemma pderiv_complexFockMonomial (d : σ →₀ ℕ) (i : σ) :
    MvPolynomial.pderiv i (complexFockMonomial d) =
      (Real.sqrt (d i : ℝ) : ℂ) • complexFockMonomial (d - Finsupp.single i 1) := by
  have h := congrArg (MvPolynomial.map (algebraMap ℝ ℂ)) (pderiv_fockMonomial d i)
  rw [complexFockMonomial, MvPolynomial.pderiv_map]
  simpa [complexFockMonomial, fockMonomial, MvPolynomial.smul_monomial] using h

/-- Complex version of the normalized monomial basis. -/
def complexFockBasis : Module.Basis (σ →₀ ℕ) ℂ (MvPolynomial σ ℂ) :=
  (MvPolynomial.basisMonomials σ ℂ).isUnitSMul
    (fun d => IsUnit.mk0 (((Real.sqrt (multiFactorial d : ℝ))⁻¹ : ℝ) : ℂ)
      (Complex.ofReal_ne_zero.mpr (inv_ne_zero (sqrt_multiFactorial_pos d).ne')))

omit [DecidableEq σ] in
lemma complexFockBasis_apply (d : σ →₀ ℕ) :
    complexFockBasis d = complexFockMonomial d := by
  simp [complexFockBasis, Module.Basis.isUnitSMul_apply, complexFockMonomial_eq,
    MvPolynomial.smul_monomial]

omit [DecidableEq σ] in
lemma complexFockBasis_repr (p : MvPolynomial σ ℂ) (d : σ →₀ ℕ) :
    complexFockBasis.repr p d =
      (Real.sqrt (multiFactorial d : ℝ) : ℂ) * p.coeff d := by
  simp only [complexFockBasis, Module.Basis.repr_isUnitSMul, Units.smul_def,
    IsUnit.unit_spec, Units.val_inv_eq_inv_val, Complex.ofReal_inv, inv_inv]
  rfl

end Problem335

end

end OAI
