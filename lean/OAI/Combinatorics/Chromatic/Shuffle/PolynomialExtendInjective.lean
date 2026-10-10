import Mathlib
import OAI.Combinatorics.Chromatic.Shuffle.TripleAssociativity

namespace OAI

section
namespace ElementaryPositivity.RawShuffle.SplitTree
open MvPolynomial
lemma extendPolynomial_injective {A B α β : Type*} [CommRing A] [CommRing B]
    [Algebra ℚ A] [Algebra ℚ B] (f : A →ₐ[ℚ] B) (j : α → β)
    (hf : Function.Injective f) (hj : Function.Injective j) :
    Function.Injective (extendPolynomial f j) := by
  intro p q h
  apply MvPolynomial.map_injective f.toRingHom hf
  apply MvPolynomial.rename_injective j hj
  exact h
end ElementaryPositivity.RawShuffle.SplitTree

end
section
namespace ElementaryPositivity.RawShuffle
open ElementaryPositivity.LinearDetection
open scoped TensorProduct
variable {I : Type*} [Fintype I] [DecidableEq I]

noncomputable local instance pairAdd (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d e : I → ℕ) :
    AddCommGroup (B a μ d⊗[ℚ]B a μ e) := TensorProduct.addCommGroup
noncomputable local instance tripleAdd (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d e f : I → ℕ) :
    AddCommGroup ((B a μ d⊗[ℚ]B a μ e)⊗[ℚ]B a μ f) := TensorProduct.addCommGroup
noncomputable local instance tripleFilterAdd (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (d e f : I → ℕ) (W : ℤ) :
    AddCommGroup (sourceTripleFiltration a c η hc θ d e f W) := Submodule.addCommGroup _

noncomputable def sourceTripleAssoc (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (d e f : I → ℕ) (W : ℤ) :
    sourceTripleFiltration a c η hc θ d e f W ≃ₗ[ℚ]
      additiveTensorFiltration (sourceFiltration a c η hc θ d)
        (sourceTensorFiltration a c η hc θ e f) W :=
  tensorFiltrationAssoc (sourceFiltration a c η hc θ d) (sourceFiltration a c η hc θ e)
    (sourceFiltration a c η hc θ f) W

noncomputable def iteratedCoproductLeft (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (d e f : I → ℕ)
    (hde : SlopeArithmetic.slope c η d=SlopeArithmetic.slope c η e)
    (hef : SlopeArithmetic.slope c η e=SlopeArithmetic.slope c η f) (W : ℤ) :
    sourceFiltration a c η hc θ ((d+e)+f) W →ₗ[ℚ] sourceTripleFiltration a c η hc θ d e f W :=
  (tensorSeparationLeft a c η hc θ d e f hde W).comp
    (separationCoefficientRestricted a c η hc θ (d+e) f
      ((SlopeArithmetic.slope_add_same c η hc hde).trans (hde.trans hef)) W 0)

noncomputable def iteratedCoproductRight (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (d e f : I → ℕ)
    (hde : SlopeArithmetic.slope c η d=SlopeArithmetic.slope c η e)
    (hef : SlopeArithmetic.slope c η e=SlopeArithmetic.slope c η f) (W : ℤ) :
    sourceFiltration a c η hc θ ((d+e)+f) W →ₗ[ℚ]
      additiveTensorFiltration (sourceFiltration a c η hc θ d)
        (sourceTensorFiltration a c η hc θ e f) W :=
  ((tensorSeparationRight a c η hc θ d e f hef W).comp
    (separationCoefficientRestricted a c η hc θ d (e+f)
      (hde.trans (SlopeArithmetic.slope_add_same c η hc hef).symm) W 0)).comp
    (filtrationDimensionEquiv a c η hc θ (add_assoc d e f) W).toLinearMap

namespace SplitTree

lemma normalizedTripleSymbol_difference_mem (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (hχ : SlopeEulerSymmetric a c η θ)
    (d e f : I → ℕ) (W : ℤ) (x y : sourceTripleFiltration a c η hc θ d e f W)
    (h : ∀ (L M N : SplitTree I) (hL : L.OnSlope c η θ) (hM : M.OnSlope c η θ)
      (hN : N.OnSlope c η θ) (hd : L.dim=d) (he : M.dim=e) (hf : N.dim=f),
      normalizedTripleSymbol a c η hc θ L M N hL hM hN
        (pairSymmetric_of_slope a c η θ hχ L hL) (pairSymmetric_of_slope a c η θ hχ M hM)
        (pairSymmetric_of_slope a c η θ hχ N hN) W (hd ▸ he ▸ hf ▸ x)=
      normalizedTripleSymbol a c η hc θ L M N hL hM hN
        (pairSymmetric_of_slope a c η θ hχ L hL) (pairSymmetric_of_slope a c η θ hχ M hM)
        (pairSymmetric_of_slope a c η θ hχ N hN) W (hd ▸ he ▸ hf ▸ y)) :
    ((x-y : sourceTripleFiltration a c η hc θ d e f W)).val∈sourceTripleFiltration a c η hc θ d e f (W+1) := by
  apply normalizedTripleSymbol_detect a c η hc θ hχ d e f W (x-y)
  intro L M N hL hM hN hd he hf
  subst d
  subst e
  subst f
  rw [LinearMap.map_sub,h L M N hL hM hN rfl rfl rfl,sub_self]

end SplitTree
end ElementaryPositivity.RawShuffle

end
section
namespace ElementaryPositivity.RawShuffle.SplitTree
open MvPolynomial ElementaryPositivity.CenterCalculus
open ElementaryPositivity.LinearDetection
open scoped TensorProduct
variable {I : Type*} [Fintype I] [DecidableEq I]

lemma iteratedCoproductLeft_normalizedSymbol (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (hχ : SlopeEulerSymmetric a c η θ)
    (L M N : SplitTree I) (hL : L.OnSlope c η θ) (hM : M.OnSlope c η θ)
    (hN : N.OnSlope c η θ)
    (hde : SlopeArithmetic.slope c η L.dim=SlopeArithmetic.slope c η M.dim)
    (hef : SlopeArithmetic.slope c η M.dim=SlopeArithmetic.slope c η N.dim)
    (W : ℤ) (x : sourceFiltration a c η hc θ ((L.dim+M.dim)+N.dim) W) :
    normalizedTripleSymbol a c η hc θ L M N hL hM hN
      (pairSymmetric_of_slope a c η θ hχ L hL) (pairSymmetric_of_slope a c η θ hχ M hM)
      (pairSymmetric_of_slope a c η θ hχ N hN) W
      (iteratedCoproductLeft a c η hc θ L.dim M.dim N.dim hde hef W x)=
    normalizedSymbol a c η hc θ ((L.node M).node N) ⟨⟨hL,hM⟩,hN⟩
      (pairSymmetric_of_slope a c η θ hχ _ ⟨⟨hL,hM⟩,hN⟩) W x := by
  change normalizedTripleSymbol a c η hc θ L M N hL hM hN _ _ _ W
    (tensorSeparationLeft a c η hc θ L.dim M.dim N.dim hde W
      (separationCoefficientRestricted a c η hc θ (L.dim+M.dim) N.dim _ W 0 x))=_
  rw [tensorSeparationLeft_normalized_symbol a c η hc θ hχ L M N hL hM hN W]
  exact coproduct_normalized_symbol a c η hc θ hχ (.node L M) N ⟨hL,hM⟩ hN W x

lemma iteratedCoproductRight_normalizedSymbol (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (hχ : SlopeEulerSymmetric a c η θ)
    (L M N : SplitTree I) (hL : L.OnSlope c η θ) (hM : M.OnSlope c η θ)
    (hN : N.OnSlope c η θ)
    (hde : SlopeArithmetic.slope c η L.dim=SlopeArithmetic.slope c η M.dim)
    (hef : SlopeArithmetic.slope c η M.dim=SlopeArithmetic.slope c η N.dim)
    (W : ℤ) (x : sourceFiltration a c η hc θ ((L.dim+M.dim)+N.dim) W) :
    normalizedRightTripleSymbol a c η hc θ L M N hL hM hN
      (pairSymmetric_of_slope a c η θ hχ L hL) (pairSymmetric_of_slope a c η θ hχ M hM)
      (pairSymmetric_of_slope a c η θ hχ N hN) W
      (iteratedCoproductRight a c η hc θ L.dim M.dim N.dim hde hef W x)=
    normalizedSymbol a c η hc θ (L.node (M.node N)) ⟨hL,⟨hM,hN⟩⟩
      (pairSymmetric_of_slope a c η θ hχ _ ⟨hL,⟨hM,hN⟩⟩) W
      (filtrationDimensionEquiv a c η hc θ (add_assoc L.dim M.dim N.dim) W x) := by
  change normalizedRightTripleSymbol a c η hc θ L M N hL hM hN _ _ _ W
    (tensorSeparationRight a c η hc θ L.dim M.dim N.dim hef W
      (separationCoefficientRestricted a c η hc θ L.dim (M.dim+N.dim) _ W 0
        (filtrationDimensionEquiv a c η hc θ (add_assoc L.dim M.dim N.dim) W x)))=_
  rw [tensorSeparationRight_normalized_symbol a c η hc θ hχ L M N hL hM hN W]
  exact coproduct_normalized_symbol a c η hc θ hχ L (.node M N) hL ⟨hM,hN⟩ W _

end ElementaryPositivity.RawShuffle.SplitTree

end
section
namespace ElementaryPositivity.RawShuffle
open ElementaryPositivity.LinearDetection ElementaryPositivity.LinearFiltration
open scoped TensorProduct
variable {I : Type*} [Fintype I] [DecidableEq I]
attribute [local instance] pairAdd tripleAdd tripleFilterAdd

namespace SplitTree
lemma iteratedCoproduct_normalizedSymbol_eq (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (hχ : SlopeEulerSymmetric a c η θ)
    (L M N : SplitTree I) (hL : L.OnSlope c η θ) (hM : M.OnSlope c η θ)
    (hN : N.OnSlope c η θ)
    (hde : SlopeArithmetic.slope c η L.dim=SlopeArithmetic.slope c η M.dim)
    (hef : SlopeArithmetic.slope c η M.dim=SlopeArithmetic.slope c η N.dim)
    (W : ℤ) (x : sourceFiltration a c η hc θ ((L.dim+M.dim)+N.dim) W) :
    normalizedTripleSymbol a c η hc θ L M N hL hM hN
      (pairSymmetric_of_slope a c η θ hχ L hL) (pairSymmetric_of_slope a c η θ hχ M hM)
      (pairSymmetric_of_slope a c η θ hχ N hN) W
      (iteratedCoproductLeft a c η hc θ L.dim M.dim N.dim hde hef W x)=
    normalizedTripleSymbol a c η hc θ L M N hL hM hN
      (pairSymmetric_of_slope a c η θ hχ L hL) (pairSymmetric_of_slope a c η θ hχ M hM)
      (pairSymmetric_of_slope a c η θ hχ N hN) W
      ((sourceTripleAssoc a c η hc θ L.dim M.dim N.dim W).symm
        (iteratedCoproductRight a c η hc θ L.dim M.dim N.dim hde hef W x)) := by
  apply extendPolynomial_injective
    ((Regroup.assoc L M N).equivalence (quotientFamily a (SlopeArithmetic.slope c η))).toAlgHom
    (Regroup.assoc L M N).centers
    ((Regroup.assoc L M N).equivalence _).injective (Regroup.assoc L M N).centers.injective
  change extendPolynomial _ _ (normalizedTripleSymbol a c η hc θ L M N hL hM hN _ _ _ W
    (iteratedCoproductLeft a c η hc θ L.dim M.dim N.dim hde hef W x))=
    normalizedRightTripleSymbol a c η hc θ L M N hL hM hN _ _ _ W
      (iteratedCoproductRight a c η hc θ L.dim M.dim N.dim hde hef W x)
  rw [iteratedCoproductLeft_normalizedSymbol a c η hc θ hχ L M N hL hM hN hde hef W x,
    iteratedCoproductRight_normalizedSymbol a c η hc θ hχ L M N hL hM hN hde hef W x]
  exact (Regroup.normalizedSymbol_natural a c η hc θ (.assoc L M N)
    (Regroup.assoc_orderPreserving L M N) ⟨⟨hL,hM⟩,hN⟩ ⟨hL,⟨hM,hN⟩⟩
    (pairSymmetric_of_slope a c η θ hχ _ ⟨⟨hL,hM⟩,hN⟩)
    (pairSymmetric_of_slope a c η θ hχ _ ⟨hL,⟨hM,hN⟩⟩) W x).symm
end SplitTree

theorem separation_coassoc_filtration (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (hχ : SlopeEulerSymmetric a c η θ)
    (d e f : I → ℕ)
    (hde : SlopeArithmetic.slope c η d=SlopeArithmetic.slope c η e)
    (hef : SlopeArithmetic.slope c η e=SlopeArithmetic.slope c η f)
    (W : ℤ) (x : sourceFiltration a c η hc θ ((d+e)+f) W) :
    (iteratedCoproductLeft a c η hc θ d e f hde hef W x -
      (sourceTripleAssoc a c η hc θ d e f W).symm
        (iteratedCoproductRight a c η hc θ d e f hde hef W x)).val∈
      sourceTripleFiltration a c η hc θ d e f (W+1) := by
  apply SplitTree.normalizedTripleSymbol_difference_mem a c η hc θ hχ d e f W
  intro L M N hL hM hN hd he hf
  subst d
  subst e
  subst f
  exact SplitTree.iteratedCoproduct_normalizedSymbol_eq a c η hc θ hχ L M N hL hM hN hde hef W x

theorem separationCoproduct_coassociative (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (hχ : SlopeEulerSymmetric a c η θ)
    (d e f : I → ℕ)
    (hde : SlopeArithmetic.slope c η d=SlopeArithmetic.slope c η e)
    (hef : SlopeArithmetic.slope c η e=SlopeArithmetic.slope c η f)
    (W : ℤ) (x : sourceFiltration a c η hc θ ((d+e)+f) W) :
    LinearFiltration.mk (sourceTripleFiltration a c η hc θ d e f W)
      (sourceTripleFiltration a c η hc θ d e f (W+1))
      (iteratedCoproductLeft a c η hc θ d e f hde hef W x)=
    LinearFiltration.mk (sourceTripleFiltration a c η hc θ d e f W)
      (sourceTripleFiltration a c η hc θ d e f (W+1))
      ((sourceTripleAssoc a c η hc θ d e f W).symm
        (iteratedCoproductRight a c η hc θ d e f hde hef W x)) := by
  apply sub_eq_zero.mp
  rw [←LinearMap.map_sub]
  exact (Submodule.Quotient.mk_eq_zero _).mpr
    (separation_coassoc_filtration a c η hc θ hχ d e f hde hef W x)

end ElementaryPositivity.RawShuffle

end

end OAI
