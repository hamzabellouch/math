import OAI.Algebra.DepthFive.OperatorRank

namespace OAI

noncomputable section

namespace Problem335

/-- One variable on each side gives an explicit monomial of every bidegree. -/
theorem exists_bidegree_exponent {σ : Type*} (isV : σ → Bool)
    (v u : σ) (hv : isV v = true) (hu : isV u = false) (a b : ℕ) :
    ∃ d : σ →₀ ℕ, Finsupp.weight (bidegreeWeight isV) d = (a, b) := by
  refine ⟨Finsupp.single v a + Finsupp.single u b, ?_⟩
  simp [map_add, Finsupp.weight_single, bidegreeWeight, hv, hu]

/-- The finite exponent-index subtype used by restricted operator matrices is inhabited. -/
theorem nonempty_bidegree_exponents {σ : Type*} (isV : σ → Bool)
    (v u : σ) (hv : isV v = true) (hu : isV u = false) (a b : ℕ) :
    Nonempty {d : σ →₀ ℕ // Finsupp.weight (bidegreeWeight isV) d = (a, b)} := by
  obtain ⟨d, hd⟩ := exists_bidegree_exponent isV v u hv hu a b
  exact ⟨⟨d, hd⟩⟩

/-- The bidegree submodule contains a nonzero polynomial whenever both groups
contain a variable. -/
theorem exists_ne_zero_mem_bidegree {σ K : Type*} [CommSemiring K] [Nontrivial K]
    (isV : σ → Bool) (v u : σ) (hv : isV v = true) (hu : isV u = false)
    (a b : ℕ) :
    ∃ p : MvPolynomial σ K, p ∈ bidegreeSubmodule isV a b ∧ p ≠ 0 := by
  obtain ⟨d, hd⟩ := exists_bidegree_exponent isV v u hv hu a b
  refine ⟨MvPolynomial.monomial d 1, ?_, ?_⟩
  · exact MvPolynomial.isWeightedHomogeneous_monomial (bidegreeWeight isV) d 1 hd
  · simp

/-- Nontriviality of the source and target homogeneous spaces. -/
theorem bidegreeSubmodule_nontrivial {σ K : Type*} [CommSemiring K] [Nontrivial K]
    (isV : σ → Bool) (v u : σ) (hv : isV v = true) (hu : isV u = false)
    (a b : ℕ) : Nontrivial (bidegreeSubmodule (K := K) isV a b) := by
  obtain ⟨p, hp, hne⟩ := exists_ne_zero_mem_bidegree (K := K) isV v u hv hu a b
  refine ⟨⟨⟨p, hp⟩, 0, ?_⟩⟩
  intro heq
  exact hne (congrArg Subtype.val heq)

/-- The source dimension cancelled in the rank comparison is strictly positive. -/
theorem bidegreeSubmodule_finrank_pos {σ K : Type*} [Finite σ] [Field K]
    (isV : σ → Bool) (v u : σ) (hv : isV v = true) (hu : isV u = false)
    (a b : ℕ) : 0 < Module.finrank K (bidegreeSubmodule (K := K) isV a b) := by
  let := bidegreeSubmodule_nontrivial (K := K) isV v u hv hu a b
  exact Module.finrank_pos

end Problem335

end

end OAI
