import OAI.Algebra.DepthFive.BidegreeBasis
import OAI.Algebra.DepthFive.FockMonomials
import OAI.Algebra.DepthFive.MatrixNormalization

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem335

variable {σ : Type*}

/-- Exponent vectors at a fixed derivative/multiplication bidegree. -/
abbrev BidegreeIndex (isV : σ → Bool) (a b : ℕ) :=
  {d : σ →₀ ℕ // Finsupp.weight (bidegreeWeight isV) d = (a, b)}

section Normalized

variable [Fintype σ]

/-- The real factorial-normalized monomial basis at fixed bidegree. -/
def bidegreeFockBasis (isV : σ → Bool) (a b : ℕ) :
    Module.Basis (BidegreeIndex isV a b) ℝ (bidegreeSubmodule (K := ℝ) isV a b) :=
  (bidegreeMonomialBasis ℝ isV a b).isUnitSMul
    (fun d => IsUnit.mk0 (Real.sqrt (multiFactorial d.1 : ℝ))⁻¹
      (inv_ne_zero (sqrt_multiFactorial_pos d.1).ne'))

@[simp] theorem bidegreeFockBasis_apply (isV : σ → Bool) (a b : ℕ)
    (d : BidegreeIndex isV a b) :
    ((bidegreeFockBasis isV a b d : bidegreeSubmodule (K := ℝ) isV a b) :
      MvPolynomial σ ℝ) = fockMonomial d.1 := by
  simp [bidegreeFockBasis, Module.Basis.isUnitSMul_apply,
    bidegreeMonomialBasis_apply, fockMonomial, MvPolynomial.smul_monomial]

@[simp] theorem bidegreeFockBasis_repr (isV : σ → Bool) (a b : ℕ)
    (p : bidegreeSubmodule (K := ℝ) isV a b) (d : BidegreeIndex isV a b) :
    (bidegreeFockBasis isV a b).repr p d =
      Real.sqrt (multiFactorial d.1 : ℝ) * p.1.coeff d.1 := by
  simp only [bidegreeFockBasis, Module.Basis.repr_isUnitSMul, Units.smul_def,
    IsUnit.unit_spec, Units.val_inv_eq_inv_val, inv_inv, bidegreeMonomialBasis_repr,
    smul_eq_mul]

/-- The complex factorial-normalized monomial basis at fixed bidegree. -/
def bidegreeComplexFockBasis (isV : σ → Bool) (a b : ℕ) :
    Module.Basis (BidegreeIndex isV a b) ℂ (bidegreeSubmodule (K := ℂ) isV a b) :=
  (bidegreeMonomialBasis ℂ isV a b).isUnitSMul
    (fun d => IsUnit.mk0 (((Real.sqrt (multiFactorial d.1 : ℝ))⁻¹ : ℝ) : ℂ)
      (Complex.ofReal_ne_zero.mpr (inv_ne_zero (sqrt_multiFactorial_pos d.1).ne')))

@[simp] theorem bidegreeComplexFockBasis_apply (isV : σ → Bool) (a b : ℕ)
    (d : BidegreeIndex isV a b) :
    ((bidegreeComplexFockBasis isV a b d : bidegreeSubmodule (K := ℂ) isV a b) :
      MvPolynomial σ ℂ) = complexFockMonomial d.1 := by
  simp [bidegreeComplexFockBasis, Module.Basis.isUnitSMul_apply,
    bidegreeMonomialBasis_apply, complexFockMonomial_eq, MvPolynomial.smul_monomial]

@[simp] theorem bidegreeComplexFockBasis_repr (isV : σ → Bool) (a b : ℕ)
    (p : bidegreeSubmodule (K := ℂ) isV a b) (d : BidegreeIndex isV a b) :
    (bidegreeComplexFockBasis isV a b).repr p d =
      (Real.sqrt (multiFactorial d.1 : ℝ) : ℂ) * p.1.coeff d.1 := by
  simp only [bidegreeComplexFockBasis, Module.Basis.repr_isUnitSMul, Units.smul_def,
    IsUnit.unit_spec, Units.val_inv_eq_inv_val, Complex.ofReal_inv, inv_inv,
    bidegreeMonomialBasis_repr, smul_eq_mul]

variable [DecidableEq σ]

/-- The finite Fock-basis matrix is precisely the square-root diagonal
normalization of the ordinary monomial-basis matrix. -/
theorem toMatrix_bidegreeComplexFockBasis_apply (isV : σ → Bool)
    (a b c d : ℕ)
    (f : bidegreeSubmodule (K := ℂ) isV a b →ₗ[ℂ]
      bidegreeSubmodule (K := ℂ) isV c d)
    (i : BidegreeIndex isV c d) (j : BidegreeIndex isV a b) :
    LinearMap.toMatrix (bidegreeComplexFockBasis isV a b)
      (bidegreeComplexFockBasis isV c d) f i j =
      (Real.sqrt (multiFactorial i.1 : ℝ) : ℂ) *
        LinearMap.toMatrix (bidegreeMonomialBasis ℂ isV a b)
          (bidegreeMonomialBasis ℂ isV c d) f i j /
        (Real.sqrt (multiFactorial j.1 : ℝ) : ℂ) := by
  classical
  rw [LinearMap.toMatrix_apply, bidegreeComplexFockBasis_repr]
  simp only [bidegreeComplexFockBasis, Module.Basis.isUnitSMul_apply, map_smul,
    SetLike.val_smul, MvPolynomial.coeff_smul, smul_eq_mul,
    LinearMap.toMatrix_apply, bidegreeMonomialBasis_repr, Complex.ofReal_inv]
  ring

/-- Finite Fock normalization leaves the rank of the restricted operator unchanged. -/
theorem rank_toMatrix_bidegreeComplexFockBasis (isV : σ → Bool)
    (a b c d : ℕ)
    (f : bidegreeSubmodule (K := ℂ) isV a b →ₗ[ℂ]
      bidegreeSubmodule (K := ℂ) isV c d) :
    (LinearMap.toMatrix (bidegreeComplexFockBasis isV a b)
      (bidegreeComplexFockBasis isV c d) f).rank =
    (LinearMap.toMatrix (bidegreeMonomialBasis ℂ isV a b)
      (bidegreeMonomialBasis ℂ isV c d) f).rank := by
  classical
  have heq : LinearMap.toMatrix (bidegreeComplexFockBasis isV a b)
      (bidegreeComplexFockBasis isV c d) f =
      fun i j => (Real.sqrt (multiFactorial i.1 : ℝ) : ℂ) *
        LinearMap.toMatrix (bidegreeMonomialBasis ℂ isV a b)
          (bidegreeMonomialBasis ℂ isV c d) f i j /
        (Real.sqrt (multiFactorial j.1 : ℝ) : ℂ) := by
    ext i j
    exact toMatrix_bidegreeComplexFockBasis_apply isV a b c d f i j
  rw [heq]
  apply rank_sqrt_normalization
  · intro i
    exact_mod_cast multiFactorial_pos i.1
  · intro j
    exact_mod_cast multiFactorial_pos j.1

end Normalized

end Problem335

end

end OAI
