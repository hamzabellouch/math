import OAI.Algebra.DepthFive.OperatorRank

namespace OAI

noncomputable section

namespace Problem335

universe u v

/-- Ordinary monomial basis of a fixed bidegree subspace. -/
def bidegreeMonomialBasis (K : Type u) [CommSemiring K]
    {σ : Type v} (side : σ → Bool) (a b : ℕ) :
    Module.Basis {m : σ →₀ ℕ // Finsupp.weight (bidegreeWeight side) m = (a, b)} K
      (bidegreeSubmodule (K := K) side a b) :=
  (MvPolynomial.basisRestrictSupport K
    {m : σ →₀ ℕ | Finsupp.weight (bidegreeWeight side) m = (a, b)}).map
      (LinearEquiv.ofEq _ _
        (MvPolynomial.weightedHomogeneousSubmodule_eq_finsupp_supported
          K (bidegreeWeight side) (a, b)).symm)

@[simp] theorem bidegreeMonomialBasis_repr (K : Type u) [CommSemiring K]
    {σ : Type v} (side : σ → Bool) (a b : ℕ)
    (p : bidegreeSubmodule (K := K) side a b)
    (d : {m : σ →₀ ℕ // Finsupp.weight (bidegreeWeight side) m = (a, b)}) :
    (bidegreeMonomialBasis K side a b).repr p d = p.1.coeff d.1 := by
  rfl

@[simp] theorem bidegreeMonomialBasis_apply (K : Type u) [CommSemiring K]
    {σ : Type v} (side : σ → Bool) (a b : ℕ)
    (d : {m : σ →₀ ℕ // Finsupp.weight (bidegreeWeight side) m = (a, b)}) :
    ((bidegreeMonomialBasis K side a b) d : MvPolynomial σ K) =
      MvPolynomial.monomial d.1 1 := by
  classical
  have hm : MvPolynomial.monomial d.1 (1 : K) ∈
      bidegreeSubmodule (K := K) side a b := by
    exact MvPolynomial.isWeightedHomogeneous_monomial (bidegreeWeight side) d.1 1 d.2
  have he : (bidegreeMonomialBasis K side a b) d =
      ⟨MvPolynomial.monomial d.1 1, hm⟩ := by
    apply (bidegreeMonomialBasis K side a b).repr.injective
    ext j
    rw [Module.Basis.repr_self, bidegreeMonomialBasis_repr]
    simp [MvPolynomial.coeff_monomial, Finsupp.single_apply, Subtype.ext_iff]
  exact congrArg Subtype.val he

/-- Finite monomial indexing for bidegree spaces over a finite variable set. -/
instance bidegreeMonomialFintype {σ : Type v} [Finite σ]
    (side : σ → Bool) (a b : ℕ) :
    Fintype {m : σ →₀ ℕ // Finsupp.weight (bidegreeWeight side) m = (a, b)} :=
  (finite_bidegreeMonomials side a b).fintype

/-- Matrix entries in the ordinary bidegree monomial bases are polynomial coefficients. -/
theorem bidegree_toMatrix_apply (K : Type u) [CommSemiring K]
    {σ : Type v} [Finite σ] [DecidableEq σ] (side : σ → Bool) (a b c d : ℕ)
    (F : bidegreeSubmodule (K := K) side a b →ₗ[K]
      bidegreeSubmodule (K := K) side c d)
    (i : {m : σ →₀ ℕ // Finsupp.weight (bidegreeWeight side) m = (c, d)})
    (j : {m : σ →₀ ℕ // Finsupp.weight (bidegreeWeight side) m = (a, b)}) :
    (LinearMap.toMatrix (bidegreeMonomialBasis K side a b)
      (bidegreeMonomialBasis K side c d) F) i j =
      (F ⟨MvPolynomial.monomial j.1 1,
        MvPolynomial.isWeightedHomogeneous_monomial (bidegreeWeight side) j.1 1 j.2⟩).1.coeff i.1 := by
  classical
  have hb : (bidegreeMonomialBasis K side a b) j =
      ⟨MvPolynomial.monomial j.1 1,
        MvPolynomial.isWeightedHomogeneous_monomial (bidegreeWeight side) j.1 1 j.2⟩ :=
    Subtype.ext (bidegreeMonomialBasis_apply K side a b j)
  rw [LinearMap.toMatrix_apply, bidegreeMonomialBasis_repr, hb]

end Problem335

end

end OAI
