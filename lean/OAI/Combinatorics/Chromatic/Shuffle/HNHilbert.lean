import Mathlib
import OAI.Combinatorics.Chromatic.Shuffle.HNHomogeneousBasis
import OAI.Combinatorics.Chromatic.GradedAlgebra.HomogeneousBasisFibre

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open ElementaryPositivity.SlopeArithmetic
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]
variable (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)

abbrev HNGradedIndex (d : I → ℕ) (k : ℤ) :=
  {i : Σ l : HNIndex c η d,HNBasisIndex a c η l.val // hnBasisDegree a c η i.1.val i.2=k}

lemma hnHomogeneousBasis_component (d : I → ℕ) (k : ℤ)
    (i : Σ l : HNIndex c η d,HNBasisIndex a c η l.val) :
    componentS d k (hnHomogeneousBasis a c η hc d i)=
      if hnBasisDegree a c η i.1.val i.2=k then hnHomogeneousBasis a c η hc d i else 0 := by
  rw [componentS_of_homogeneous _ _ (hnHomogeneousBasis_degree a c η hc d i)]
  simp only [eq_comm]

noncomputable def hnGradedBasis (d : I → ℕ) (k : ℤ) :
    Module.Basis (HNGradedIndex a c η d k) ℚ (LinearMap.range (componentS d k)) :=
  ElementaryPositivity.homogeneousBasisFibre (hnHomogeneousBasis a c η hc d)
    (fun i=>hnBasisDegree a c η i.1.val i.2) (componentS d)
    (hnHomogeneousBasis_component a c η hc d) k

include hc

theorem hnGradedIndex_finite (d : I → ℕ) (k : ℤ) : Finite (HNGradedIndex a c η d k) := by
  let := componentS_range_finite d k
  exact Module.Finite.finite_basis (hnGradedBasis a c η hc d k)

theorem hnHilbert_coefficient (d : I → ℕ) (k : ℤ) :
    Module.finrank ℚ (LinearMap.range (componentS d k))=Nat.card (HNGradedIndex a c η d k) := by
  let := hnGradedIndex_finite a c η hc d k
  let := Fintype.ofFinite (HNGradedIndex a c η d k)
  rw [Module.finrank_eq_card_basis (hnGradedBasis a c η hc d k),Nat.card_eq_fintype_card]
end ElementaryPositivity.RawShuffle

end

end OAI
