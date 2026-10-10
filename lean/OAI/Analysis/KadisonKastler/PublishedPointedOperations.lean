import OAI.Analysis.KadisonKastler.PointedMatrixProduct

namespace OAI

/-! # Pointed-product construction and its canonical identifications

Blackadar, *Operator Algebras*, III.3.1.1--2 (pp.293--294), defines the
pointed Hilbert product as the completion of the finite-support tensors,
with their product inner products. A weight-preserving reindexing is
therefore an isometry on those tensors and extends to the completion.
Splitting the index set into two parts gives the usual Hilbert tensor
product and the generated spatial algebra.

These inputs retain only the lambda-only construction and the sum and
reindex identifications. The two-ratio absorption statement is proved
from the explicit even/odd bijection, rather than included here.
-/

namespace KadisonKastler

open UnitalTomsWinter

noncomputable section

universe u

/-- The three elementary pointed-product facts used in the absorption
argument. All coordinates carry the actual finite matrix-state moments. -/
structure PublishedPointedMatrixOperations : Prop where
  powers : Nonempty (PointedMatrixProduct.{u} (fun _ : ℕ => fixedProductLambda))
  sum : ∀ (I J : Type) [Countable I] [Countable J]
    (H K : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (M : VonNeumannAlgebra H) (N : VonNeumannAlgebra K) (Ω : H) (ξ : K)
    (ν : I → ℝ) (η : J → ℝ),
    PointedMatrixSites M Ω ν → PointedMatrixSites N ξ η →
    Nonempty (PointedMatrixSites (spatialProductAlgebra M N) (tensorVector ξ Ω)
      (Sum.elim ν η))
  reindex : ∀ (I J : Type) [Countable I] [Countable J]
    (H K : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (M : VonNeumannAlgebra H) (N : VonNeumannAlgebra K) (Ω : H) (ξ : K)
    (ν : I → ℝ) (η : J → ℝ),
    PointedMatrixSites M Ω ν → PointedMatrixSites N ξ η →
    ∀ e : I ≃ J, (∀ i, η (e i) = ν i) →
    ∃ U : H ≃ₗᵢ[ℂ] K, U Ω = ξ ∧
      ∀ x : H →L[ℂ] H, x ∈ M ↔ U.conjStarAlgEquiv x ∈ N

end

end KadisonKastler

end OAI
