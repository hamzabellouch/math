import OAI.Algebra.DepthFive.OperatorRank
import OAI.Algebra.DepthFive.HomogeneousSpaceDimension

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem335

universe u v

/-- Split a finite exponent vector into its derivative and multiplication coordinates. -/
def splitBidegreeExponents {σ : Type u} [Fintype σ] (side : σ → Bool) :
    (σ →₀ ℕ) ≃ ({i : σ // side i = true} →₀ ℕ) ×
      ({i : σ // side i = false} →₀ ℕ) := by
  classical
  refine {
    toFun := fun m => (m.subtypeDomain (fun i => side i = true),
      m.subtypeDomain (fun i => side i = false))
    invFun := fun p => Finsupp.equivFunOnFinite.symm (fun i =>
      if h : side i = true then p.1 ⟨i, h⟩ else p.2 ⟨i, by simpa using h⟩)
    left_inv := ?_
    right_inv := ?_ }
  · intro m
    ext i
    simp only [Finsupp.coe_equivFunOnFinite_symm]
    split <;> rfl
  · intro p
    apply Prod.ext
    · ext i
      simp [i.property]
    · ext i
      simp [i.property]

/-- The bidegree is the pair of total degrees of the restricted exponent vectors. -/
theorem weight_splitBidegreeExponents {σ : Type u} [Fintype σ]
    (side : σ → Bool) (m : σ →₀ ℕ) :
    Finsupp.weight (bidegreeWeight side) m =
      ((splitBidegreeExponents side m).1.degree,
       (splitBidegreeExponents side m).2.degree) := by
  classical
  have hs (p : σ → Prop) [DecidablePred p] :
      (∑ i : Subtype p, m i) = ∑ i, if p i then m i else 0 := by
    rw [← Finset.sum_filter]
    exact (Finset.sum_subtype _ (by simp) _).symm
  apply Prod.ext
  · simp [Finsupp.weight_apply, Finsupp.sum_fintype, Finsupp.degree_eq_sum,
      splitBidegreeExponents, bidegreeWeight, Prod.fst_sum, hs]
    apply Finset.sum_congr rfl
    intro i _
    cases side i <;> simp
  · simp [Finsupp.weight_apply, Finsupp.sum_fintype, Finsupp.degree_eq_sum,
      splitBidegreeExponents, bidegreeWeight, Prod.snd_sum, hs]
    apply Finset.sum_congr rfl
    intro i _
    cases side i <;> simp

/-- A fixed bidegree fiber is the product of two ordinary degree fibers. -/
def bidegreeFinsuppExponentsEquiv {σ : Type u} [Fintype σ] (side : σ → Bool) (a b : ℕ) :
    {m : σ →₀ ℕ // Finsupp.weight (bidegreeWeight side) m = (a, b)} ≃
      {m : {i : σ // side i = true} →₀ ℕ // m.degree = a} ×
      {m : {i : σ // side i = false} →₀ ℕ // m.degree = b} :=
  ((splitBidegreeExponents side).subtypeEquiv
    (p := fun m => Finsupp.weight (bidegreeWeight side) m = (a, b))
    (q := fun p : ({i : σ // side i = true} →₀ ℕ) ×
      ({i : σ // side i = false} →₀ ℕ) => p.1.degree = a ∧ p.2.degree = b)
    (by
      intro m
      constructor
      · intro h
        exact Prod.mk.inj ((weight_splitBidegreeExponents side m).symm.trans h)
      · rintro ⟨h1, h2⟩
        exact (weight_splitBidegreeExponents side m).trans (Prod.ext h1 h2))).trans
      (Equiv.subtypeProdEquivProd
        (p := fun m : {i : σ // side i = true} →₀ ℕ => m.degree = a)
        (q := fun m : {i : σ // side i = false} →₀ ℕ => m.degree = b))

/-- Counting bidegree monomials separates into the two variable groups. -/
theorem card_bidegree_finsupp_exponents {σ : Type u} [Fintype σ]
    (side : σ → Bool) (a b : ℕ) :
    Nat.card {m : σ →₀ ℕ // Finsupp.weight (bidegreeWeight side) m = (a, b)} =
      Nat.multichoose (Fintype.card {i : σ // side i = true}) a *
      Nat.multichoose (Fintype.card {i : σ // side i = false}) b := by
  rw [Nat.card_congr (bidegreeFinsuppExponentsEquiv side a b), Nat.card_prod,
    card_degree_exponents, card_degree_exponents]

/-- Exact finite dimension of the polynomial subspace used by the mixed operator. -/
theorem bidegreeSubmodule_finrank (K : Type u) [Field K]
    {σ : Type v} [Fintype σ] (side : σ → Bool) (a b : ℕ) :
    Module.finrank K (bidegreeSubmodule (K := K) side a b) =
      Nat.multichoose (Fintype.card {i : σ // side i = true}) a *
      Nat.multichoose (Fintype.card {i : σ // side i = false}) b := by
  unfold bidegreeSubmodule
  rw [MvPolynomial.weightedHomogeneousSubmodule_eq_finsupp_supported]
  change Module.finrank K (MvPolynomial.restrictSupport K
    {m : σ →₀ ℕ | Finsupp.weight (bidegreeWeight side) m = (a, b)}) = _
  rw [Module.finrank_eq_nat_card_basis (MvPolynomial.basisRestrictSupport K _)]
  exact card_bidegree_finsupp_exponents side a b

/-- Stars-and-bars form, with no nonemptiness hypothesis needed. -/
theorem bidegreeSubmodule_finrank_choose (K : Type u) [Field K]
    {σ : Type v} [Fintype σ] (side : σ → Bool) (a b : ℕ) :
    Module.finrank K (bidegreeSubmodule (K := K) side a b) =
      Nat.choose (Fintype.card {i : σ // side i = true} + a - 1) a *
      Nat.choose (Fintype.card {i : σ // side i = false} + b - 1) b := by
  rw [bidegreeSubmodule_finrank, Nat.multichoose_eq, Nat.multichoose_eq]

end Problem335

end

end OAI
