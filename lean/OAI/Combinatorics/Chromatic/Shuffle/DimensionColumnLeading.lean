import Mathlib
import OAI.Combinatorics.Chromatic.GradedAlgebra.UnitalProduct
import OAI.Combinatorics.Chromatic.Shuffle.SignedCoproductGridGrade

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct
open ElementaryPositivity.SlopeArithmetic DimensionSplit
variable {I : Type*} [Fintype I] [DecidableEq I]
attribute [local instance] Classical.propDecidable

lemma sum_subtype_of_zero_off {X M : Type*} [Fintype X] [AddCommMonoid M]
    (p : X → Prop) [DecidablePred p] (f : X → M) (hf : ∀ x,¬p x → f x=0) :
    ∑ x,f x=∑ x : {x // p x},f x.val := by
  rw [←Fintype.sum_subtype_add_sum_subtype p f]
  have hzero : ∑ x : {x // ¬p x},f x.val=0 := by
    apply Finset.sum_eq_zero
    intro x _
    exact hf x.val x.property
  rw [hzero,add_zero]

lemma dimensionRowLeadingB_zero_of_mismatch (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) {d e α β : I → ℕ} (f : S d) (g : S e)
    (u : DimensionSplit α) (v : DimensionSplit β)
    (h : ¬(left u+left v=d ∧ right u+right v=e)) :
    dimensionRowLeadingB a c η hc θ f g u v=0 := by
  unfold dimensionRowLeadingB
  split_ifs with hon
  · rw [cellLeadingB,dite_eq_right h]
    exact (castBTensor a (slope c η) (left_add_right u) (left_add_right v)).map_zero
  · rfl

noncomputable def dimensionColumnLeadingB (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) {d e α β : I → ℕ} (f : S d) (g : S e)
    (s : ColumnDimensionGrid d e α β) : B a (slope c η) α⊗[ℚ]B a (slope c η) β :=
  if hon : CellsOnSlope c η θ (left s.val.1) (left s.val.2)
      (right s.val.1) (right s.val.2) then
    castBTensor a (slope c η) s.property.1 s.property.2
      (cellLeadingB a c η hc θ _ _ _ _ hon f g)
  else 0

lemma dimensionColumnLeadingB_transpose (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) {d e α β : I → ℕ} (f : S d) (g : S e)
    (s : RowDimensionGrid d e α β) :
    dimensionColumnLeadingB a c η hc θ f g (transposeDimensionGrid d e α β s)=
      dimensionRowLeadingB a c η hc θ f g s.val.1 s.val.2 := by
  unfold dimensionColumnLeadingB dimensionRowLeadingB
  split_ifs with hon hon'
  · exact cast_cellLeadingB_congr a c η hc θ f g rfl rfl
      (transposeDimensionGrid_first_right d e α β s)
      (transposeDimensionGrid_second_right d e α β s) _ _ _ _ hon hon'
  · exact False.elim (hon' (by simpa only [transposeDimensionGrid_first_left,
      transposeDimensionGrid_second_left,transposeDimensionGrid_first_right,
      transposeDimensionGrid_second_right] using hon))
  · rename_i hon'
    exact False.elim (hon (by simpa only [transposeDimensionGrid_first_left,
      transposeDimensionGrid_second_left,transposeDimensionGrid_first_right,
      transposeDimensionGrid_second_right] using hon'))
  · rfl

lemma double_sum_eq_column_grid {M : Type*} [AddCommMonoid M]
    (d e α β : I → ℕ) (F : DimensionSplit α → DimensionSplit β → M)
    (G : ColumnDimensionGrid d e α β → M)
    (hz : ∀ u v,¬(left u+left v=d ∧ right u+right v=e) → F u v=0)
    (hg : ∀ s : RowDimensionGrid d e α β,
      F s.val.1 s.val.2=G (transposeDimensionGrid d e α β s)) :
    ∑ u,∑ v,F u v=∑ s,G s := by
  rw [←Fintype.sum_prod_type' F]
  rw [sum_subtype_of_zero_off
    (fun s : DimensionSplit α × DimensionSplit β=>left s.1+left s.2=d ∧ right s.1+right s.2=e)
    (fun s=>F s.1 s.2) (fun s hs=>hz s.1 s.2 hs)]
  exact sum_transposeDimensionGrid_congr d e α β (fun s=>F s.val.1 s.val.2) G hg

theorem dimensionLeadingB_eq_column_sum (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) {d e α β : I → ℕ} (f : S d) (g : S e) :
    dimensionLeadingB (α:=α) (β:=β) a c η hc θ f g=
      ∑ s : ColumnDimensionGrid d e α β,dimensionColumnLeadingB a c η hc θ f g s := by
  exact double_sum_eq_column_grid d e α β
    (dimensionRowLeadingB a c η hc θ f g) (dimensionColumnLeadingB a c η hc θ f g)
    (fun u v h=>dimensionRowLeadingB_zero_of_mismatch a c η hc θ f g u v h)
    (fun s=>(dimensionColumnLeadingB_transpose a c η hc θ f g s).symm)

end ElementaryPositivity.RawShuffle

end
section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct
open ElementaryPositivity.SlopeArithmetic ElementaryPositivity.PackConvolution
open ElementaryPositivity.LinearFiltration
open HahnSeries SeparationInfinity
variable {I : Type*} [Fintype I] [DecidableEq I]
variable {A : I → Type*} [∀ i,Fintype (A i)] [∀ i,DecidableEq (A i)]
attribute [local instance] Classical.propDecidable

omit [∀ i,Fintype (A i)] in
lemma clearedConstantB_grid_unital_support (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) {d e α β : I → ℕ} (f : S d) (g : S e)
    {s : Pack (A:=A)} (p : PackConvolution.Cut s)
    (R : Realization α (left p)) (T : Realization β (right p))
    (hα : OnSlopeOrZero c η θ α) (hβ : OnSlopeOrZero c η θ β)
    (hd : OnSlopeOrZero c η θ d) :
    clearedConstantB a (slope c η) α β (quotientTensor a (slope c η) α β (gridTensor a f g p R T))=
    ∑ u : CutShape (left p),∑ v : CutShape (right p),
      if CellsOnSlope c η θ
        (fun i=>(u i).val) (shapeComplement u) (fun i=>(v i).val) (shapeComplement v)
      then clearedConstantB a (slope c η) α β
        (quotientTensor a (slope c η) α β (gridShapeTensor a f g p R T u v)) else 0 := by
  rw [quotient_gridTensor_unital_support a c η hc θ f g p R T hα hβ hd]
  simp only [map_sum,apply_ite,(clearedConstantB a (slope c η) α β).map_zero]

omit [∀ i,Fintype (A i)] in
lemma clearedConstantB_grid_leading_unital (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) {d e α β : I → ℕ} (hχ : SlopeEulerSymmetric a c η θ)
    (h : d+e=α+β) (U V : ℤ) (f : S d) (g : S e)
    (hf : quotientAlg a (slope c η) d f∈unitalSourceFiltration a c η hc θ d U)
    (hg : quotientAlg a (slope c η) e g∈unitalSourceFiltration a c η hc θ e V)
    {s : Pack (A:=A)} (p : PackConvolution.Cut s)
    (R : Realization α (left p)) (T : Realization β (right p))
    (hα : OnSlopeOrZero c η θ α) (hβ : OnSlopeOrZero c η θ β)
    (hd : OnSlopeOrZero c η θ d) :
    clearedConstantB a (slope c η) α β (quotientTensor a (slope c η) α β (gridTensor a f g p R T))-
      gridLeadingB a c η hc θ f g p R T∈
    unitalSourceTensorFiltration a c η hc θ α β (U+V+1) := by
  rw [clearedConstantB_grid_unital_support a c η hc θ f g p R T hα hβ hd,gridLeadingB,
    ←Finset.sum_sub_distrib]
  apply Submodule.sum_mem
  intro u _
  rw [←Finset.sum_sub_distrib]
  apply Submodule.sum_mem
  intro v _
  split_ifs with hon
  · exact clearedConstantB_gridShape_leading a c η hc θ hχ h U V f g hf hg p R T u v hon
  · rw [sub_self]
    exact Submodule.zero_mem _

lemma unitalSeparationConstant_shuffle_leading_all (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) {d e α β : I → ℕ} (hχ : SlopeEulerSymmetric a c η θ)
    (h : d+e=α+β) (U V : ℤ) (f : S d) (g : S e)
    (hf : quotientAlg a (slope c η) d f∈unitalSourceFiltration a c η hc θ d U)
    (hg : quotientAlg a (slope c η) e g∈unitalSourceFiltration a c η hc θ e V)
    (hα : OnSlopeOrZero c η θ α) (hβ : OnSlopeOrZero c η θ β)
    (hd : OnSlopeOrZero c η θ d)
    {s : Pack (A:=A)} (R : Realization (α+β) s) :
    (unitalSeparationSeries a c η hc (hα.compatible hβ)
      (quotientAlg a (slope c η) (α+β) (castS h (shufflePolynomial a f g)))).coeff 0-
      gridLeadingB a c η hc θ f g (cutRealizationEquiv R (firstCut α β)).val
        (leftRealization R (firstCut α β)) (rightRealization R (firstCut α β))∈
    unitalSourceTensorFiltration a c η hc θ α β (U+V+1) := by
  rw [unitalSeparationConstant_shuffle_grid a c η hc h (hα.compatible hβ) f g R]
  exact clearedConstantB_grid_leading_unital a c η hc θ hχ h U V f g hf hg _ _ _ hα hβ hd

theorem unitalSeparationConstant_shuffle_column (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) {d e α β : I → ℕ} (hχ : SlopeEulerSymmetric a c η θ)
    (h : d+e=α+β) (U V : ℤ) (f : S d) (g : S e)
    (hf : quotientAlg a (slope c η) d f∈unitalSourceFiltration a c η hc θ d U)
    (hg : quotientAlg a (slope c η) e g∈unitalSourceFiltration a c η hc θ e V)
    (hα : OnSlopeOrZero c η θ α) (hβ : OnSlopeOrZero c η θ β)
    (hd : OnSlopeOrZero c η θ d)
    {s : Pack (A:=A)} (R : Realization (α+β) s) :
    (unitalSeparationSeries a c η hc (hα.compatible hβ)
      (quotientAlg a (slope c η) (α+β) (castS h (shufflePolynomial a f g)))).coeff 0-
      ∑ s : ColumnDimensionGrid d e α β,dimensionColumnLeadingB a c η hc θ f g s∈
    unitalSourceTensorFiltration a c η hc θ α β (U+V+1) := by
  have hdiff:=unitalSeparationConstant_shuffle_leading_all a c η hc θ hχ h U V f g hf hg hα hβ hd R
  rw [gridLeadingB_eq_dimensionLeadingB,dimensionLeadingB_eq_column_sum] at hdiff
  exact hdiff
end ElementaryPositivity.RawShuffle

end

end OAI
