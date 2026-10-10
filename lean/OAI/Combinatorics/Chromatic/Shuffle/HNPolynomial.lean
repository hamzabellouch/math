import Mathlib
import OAI.Combinatorics.Chromatic.Shuffle.CutoffGrid

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct DirectSum
open ElementaryPositivity.SlopeArithmetic
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]
variable (a : I → I → ℕ) (c η : I → ℝ)

noncomputable def hnPolynomial (σ : ∀ d,B a (slope c η) d →ₗ[ℚ] S d) :
    (l : List (I → ℕ)) → HNTensor a c η l →ₗ[ℚ] S l.sum
  | [] => LinearMap.id
  | d::l => (shuffleTensorLinear a d l.sum).comp (TensorProduct.map (σ d) (hnPolynomial σ l))
lemma hnPolynomial_cons (σ : ∀ d,B a (slope c η) d →ₗ[ℚ] S d)
    (d : I → ℕ) (l : List (I → ℕ)) (x : B a (slope c η) d) (y : HNTensor a c η l) :
    hnPolynomial a c η σ (d::l) (x⊗ₜ[ℚ]y)=shufflePolynomial a (σ d x) (hnPolynomial a c η σ l y) := rfl
lemma hnWordMap_polynomial (σ : ∀ d,B a (slope c η) d →ₗ[ℚ] S d) (l : List (I → ℕ)) :
    hnWordMap a c η σ l=(rawLof a l.sum).comp (hnPolynomial a c η σ l) := by
  induction l with
  | nil => rfl
  | cons d l ih =>
    apply TensorProduct.ext'
    intro x y
    change rawLof a d (σ d x)*hnWordMap a c η σ l y=rawLof a (d+l.sum) _
    rw [ih,LinearMap.comp_apply,rawLof_mul]
    rfl

lemma clipped_destabilizingSpace_le (κ : ℝ) (d : I → ℕ) :
    destabilizingSpace a (clippedSlope c η κ) d ≤ destabilizingSpace a (slope c η) d := by
  apply Submodule.span_le.mpr
  rintro f ⟨u,v,h,x,y,hu,hv,hs,rfl⟩
  apply Submodule.subset_span
  refine ⟨u,v,h,x,y,hu,hv,?_,rfl⟩
  have H := (lt_max_iff.mp hs).resolve_right (not_lt_of_ge (le_max_right _ _))
  exact (le_max_left _ _).trans_lt H

noncomputable def clippedToOriginal (κ : ℝ) (d : I → ℕ) :
    B a (clippedSlope c η κ) d →ₗ[ℚ] B a (slope c η) d :=
  Submodule.mapQ _ _ LinearMap.id (clipped_destabilizingSpace_le a c η κ d)
lemma clippedToOriginal_mk (κ : ℝ) (d : I → ℕ) (f : S d) :
    clippedToOriginal a c η κ d (quotientAlg a (clippedSlope c η κ) d f)=quotientAlg a (slope c η) d f := rfl

lemma headRestriction_wrong_head (hc : ∀ i,0<c i) (κ : ℝ)
    {d e α β : I → ℕ} (h : d+e=α+β) (f : S d) (g : S e) (hd : d≠0)
    (hk : κ < slope c η α) (ht : slope c η β ≤ κ)
    (hs : slope c η α ≤ slope c η d)
    (hm : slope c η d=slope c η α → mass c α ≤ mass c d) (hne : d≠α) :
    headRestriction a (clippedSlope c η κ) α β (castS h (shufflePolynomial a f g))=0 :=
  headRestriction_zero a _ α β _
    (clipped_restrict_wrong_head a c η hc κ h f g (firstCut α β) hd hk ht hs hm hne)
end ElementaryPositivity.RawShuffle

end

end OAI
