import Mathlib

namespace OAI

noncomputable section

namespace Problem335

universe u v w

/-- Degree-exact exponent vectors are multisets of the indicated cardinality. -/
def degreeExponentsEquivSym (σ : Type u) (d : ℕ) :
    { m : σ →₀ ℕ // m.degree = d } ≃ Sym σ d := by
  classical
  exact (Sym.equivNatSum σ d).symm

/-- The number of monomials of total degree `d`. -/
theorem card_degree_exponents (σ : Type u) [Fintype σ] (d : ℕ) :
    Nat.card { m : σ →₀ ℕ // m.degree = d } =
      Nat.multichoose (Fintype.card σ) d := by
  rw [Nat.card_congr (degreeExponentsEquivSym σ d)]
  simpa only [Nat.card_eq_fintype_card] using Sym.natCard_sym_eq_multichoose (α := σ) d

/-- Homogeneous polynomial spaces in finitely many variables are finite modules. -/
instance homogeneousSubmodule_finite (K : Type u) [CommSemiring K]
    (σ : Type v) [Finite σ] (d : ℕ) :
    Module.Finite K (MvPolynomial.homogeneousSubmodule σ K d) :=
  Module.Finite.of_fg (MvPolynomial.homogeneousSubmodule_fg σ K d)

/-- Exact dimension of the homogeneous polynomial space. -/
theorem homogeneousSubmodule_finrank (K : Type u) [Field K]
    (σ : Type v) [Fintype σ] (d : ℕ) :
    Module.finrank K (MvPolynomial.homogeneousSubmodule σ K d) =
      Nat.multichoose (Fintype.card σ) d := by
  rw [MvPolynomial.homogeneousSubmodule_eq_finsupp_supported]
  change Module.finrank K (MvPolynomial.restrictSupport K {m : σ →₀ ℕ | m.degree = d}) = _
  rw [Module.finrank_eq_nat_card_basis (MvPolynomial.basisRestrictSupport K _)]
  exact card_degree_exponents σ d

/-- The usual stars-and-bars presentation of homogeneous dimension. -/
theorem homogeneousSubmodule_finrank_choose (K : Type u) [Field K]
    (σ : Type v) [Fintype σ] (d : ℕ) :
    Module.finrank K (MvPolynomial.homogeneousSubmodule σ K d) =
      Nat.choose (Fintype.card σ + d - 1) d := by
  rw [homogeneousSubmodule_finrank, Nat.multichoose_eq]

/-- Dimension of the separate-variable source/intermediate spaces used by the rank measure. -/
theorem homogeneousTensor_finrank (K : Type u) [Field K]
    (σ : Type v) [Fintype σ] (τ : Type w) [Fintype τ] (a b : ℕ) :
    Module.finrank K (TensorProduct K
      (MvPolynomial.homogeneousSubmodule σ K a)
      (MvPolynomial.homogeneousSubmodule τ K b)) =
      Nat.choose (Fintype.card σ + a - 1) a *
      Nat.choose (Fintype.card τ + b - 1) b := by
  rw [Module.finrank_tensorProduct, homogeneousSubmodule_finrank_choose,
    homogeneousSubmodule_finrank_choose]

end Problem335

end

end OAI
