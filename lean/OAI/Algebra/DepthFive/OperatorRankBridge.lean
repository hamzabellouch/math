import OAI.Algebra.DepthFive.BidegreeBridge
import OAI.Algebra.DepthFive.FiniteOperator
import OAI.Algebra.DepthFive.IntermediateFactorization

namespace OAI

/-! Equality of the finite-source APIs used by the product bound and the trace bound. -/
noncomputable section

namespace Problem335

variable {σ K : Type*} [Field K]

/-- The independently useful source-only constructions define the same linear family. -/
theorem sourceMixedOperator_eq_rawOperatorFamily (side : σ → Bool) (a b : ℕ) :
    sourceMixedOperator (K := K) side a b = rawOperatorFamily side a b := by
  ext q p
  rfl

/-- The canonical rank is the source-only rank of the paired projection. -/
theorem bidegreeRank_eq_source_measure (side : σ → Bool) (a b k m : ℕ)
    (q : MvPolynomial σ K) :
    bidegreeRank side a b k m q =
      RankMeasure.measure (sourceMixedOperator side a b) (bidegreeComponent side k m q) := by
  rw [sourceMixedOperator_eq_rawOperatorFamily]
  rfl

/-- For a homogeneous defining polynomial, the indicator projection suffices. -/
theorem bidegreeRank_eq_source_component (side : σ → Bool) (a b k m : ℕ)
    {q : MvPolynomial σ K} (hq : q.IsHomogeneous (k + m)) :
    bidegreeRank side a b k m q =
      RankMeasure.measure (sourceMixedOperator side a b) (Bidegree.component side k q) := by
  rw [bidegreeRank_eq_source_measure, bidegreeComponent_eq_component side k m hq]

/-- The rank used in finite-matrix moment estimates equals the source-only rank. -/
theorem finiteMixedOperator_rank_eq_source_measure (side : σ → Bool) (a b k m : ℕ)
    (q : MvPolynomial σ K) :
    RankMeasure.mapRank (finiteMixedOperator side a b k m q) =
      RankMeasure.measure (sourceMixedOperator side a b) (bidegreeComponent side k m q) := by
  rw [finiteMixedOperator_rank, bidegreeRank_eq_source_measure]

/-- When projection is redundant, no conversion of defining polynomials is needed. -/
theorem finiteMixedOperator_rank_eq_source_of_mem (side : σ → Bool) (a b k m : ℕ)
    {q : MvPolynomial σ K} (hq : q ∈ bidegreeSubmodule side k m) :
    RankMeasure.mapRank (finiteMixedOperator side a b k m q) =
      RankMeasure.mapRank (sourceMixedOperator side a b q) := by
  rw [finiteMixedOperator_rank_eq_source_measure, bidegreeComponent_eq_self hq]
  rfl

end Problem335

end

end OAI
