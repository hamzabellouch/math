import Mathlib
import OAI.Combinatorics.Chromatic.Shuffle.TwoTargetFiltration

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct
open ElementaryPositivity.LaurentAtInfinity ElementaryPositivity.SlopeArithmetic
open ElementaryPositivity.PackConvolution HahnSeries SeparationInfinity
variable {I : Type*} [Fintype I] [DecidableEq I]
attribute [local instance] clearBTensorB clearBTensorBA Classical.propDecidable

noncomputable local instance cellLeadTensorN (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d e : I → ℕ) :
    NonUnitalNonAssocSemiring (B a μ d⊗[ℚ]B a μ e) :=
  (clearBTensorB a μ d e).toNonUnitalNonAssocSemiring

noncomputable def cellLeadingB (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (θ : ℝ) {d e : I → ℕ} (d₁ e₁ d₂ e₂ : I → ℕ)
    (hon : CellsOnSlope c η θ d₁ e₁ d₂ e₂) (f : S d) (g : S e) :
    B a (slope c η) (d₁+e₁)⊗[ℚ]B a (slope c η) (d₂+e₂) :=
  if h : d₁+d₂=d ∧ e₁+e₂=e then
    ((-1 : ℚ)^eulerForm a d₂ e₁) •
      twoTargetTransferB a c η hc d₁ e₁ d₂ e₂ (hon.1.compatible hon.2.1) (hon.2.2.1.compatible hon.2.2.2)
        (fourInterchangeB a (slope c η) d₁ e₁ d₂ e₂
          ((unitalSeparationSeries a c η hc (hon.1.compatible hon.2.2.1)
              (quotientAlg a (slope c η) (d₁+d₂) (castS h.1.symm f))).coeff 0⊗ₜ[ℚ]
           (unitalSeparationSeries a c η hc (hon.2.1.compatible hon.2.2.2)
              (quotientAlg a (slope c η) (e₁+e₂) (castS h.2.symm g))).coeff 0))
  else 0

lemma clearedConstantB_cell_leading (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (θ : ℝ) (hχ : SlopeEulerSymmetric a c η θ) {d e : I → ℕ} (d₁ e₁ d₂ e₂ : I → ℕ)
    (hon : CellsOnSlope c η θ d₁ e₁ d₂ e₂) (h : d+e=(d₁+e₁)+(d₂+e₂))
    (U V : ℤ) (f : S d) (g : S e)
    (hf : quotientAlg a (slope c η) d f∈unitalSourceFiltration a c η hc θ d U)
    (hg : quotientAlg a (slope c η) e g∈unitalSourceFiltration a c η hc θ e V) :
    clearedConstantB a (slope c η) (d₁+e₁) (d₂+e₂)
      (quotientTensor a (slope c η) (d₁+e₁) (d₂+e₂)
        (cellTransfer a d₁ e₁ d₂ e₂ (fourGridPolynomial a f g d₁ e₁ d₂ e₂))) -
      cellLeadingB a c η hc θ d₁ e₁ d₂ e₂ hon f g∈
    unitalSourceTensorFiltration a c η hc θ (d₁+e₁) (d₂+e₂) (U+V+1) := by
  by_cases hd : d₁+d₂=d
  · have he : e₁+e₂=e := by
      apply add_left_cancel (a:=d)
      calc
        d+(e₁+e₂)=(d₁+e₁)+(d₂+e₂) := by rw [←hd]; ac_rfl
        _=d+e := h.symm
    subst d
    subst e
    simpa only [cellLeadingB,dite_eq_left,castS_rfl,clearedConstantB_apply,and_self,
      dite_true] using
      clearedSeparationB_cell_constant_next a c η hc θ hχ d₁ e₁ d₂ e₂
        hon.1 hon.2.1 hon.2.2.1 hon.2.2.2 U V f g hf hg
  · rw [cellLeadingB,dite_eq_right (fun hm=>hd hm.1),
      fourGridPolynomial_zero_of_source_mismatch a f g _ _ _ _ hd]
    simp only [map_zero,sub_zero]
    exact Submodule.zero_mem _

noncomputable def castBTensor (a : I → I → ℕ) (μ : (I → ℕ) → ℝ)
    {d e d' e' : I → ℕ} (h : d=d') (k : e=e') :
    B a μ d⊗[ℚ]B a μ e ≃ₗ[ℚ] B a μ d'⊗[ℚ]B a μ e' := by
  subst d'
  subst e'
  exact LinearEquiv.refl ℚ _

lemma castBTensor_sub (a : I → I → ℕ) (μ : (I → ℕ) → ℝ)
    {d e d' e' : I → ℕ} (h : d=d') (k : e=e')
    (x y : B a μ d⊗[ℚ]B a μ e) :
    castBTensor a μ h k (x-y)=castBTensor a μ h k x-castBTensor a μ h k y := by
  subst d'
  subst e'
  rfl

lemma clearedConstantB_castTensor (a : I → I → ℕ) (μ : (I → ℕ) → ℝ)
    {d e d' e' : I → ℕ} (h : d=d') (k : e=e') (x : S d⊗[ℚ]S e) :
    clearedConstantB a μ d' e' (quotientTensor a μ d' e' (castTensor h k x))=
      castBTensor a μ h k (clearedConstantB a μ d e (quotientTensor a μ d e x)) := by
  subst d'
  subst e'
  rfl

lemma castBTensor_mem_unitalSource (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (θ : ℝ) {d e d' e' : I → ℕ} (h : d=d') (k : e=e') (W : ℤ)
    (x : B a (slope c η) d⊗[ℚ]B a (slope c η) e)
    (hx : x∈unitalSourceTensorFiltration a c η hc θ d e W) :
    castBTensor a (slope c η) h k x∈unitalSourceTensorFiltration a c η hc θ d' e' W := by
  subst d'
  subst e'
  exact hx

variable {A : I → Type*} [∀ i,Fintype (A i)] [∀ i,DecidableEq (A i)]
noncomputable def gridShapeLeadingB (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (θ : ℝ) {d e α β : I → ℕ} (f : S d) (g : S e) {s : Pack (A:=A)}
    (p : PackConvolution.Cut s) (R : Realization α (left p)) (T : Realization β (right p))
    (u : CutShape (left p)) (v : CutShape (right p))
    (hon : CellsOnSlope c η θ (fun i=>(u i).val) (shapeComplement u)
      (fun i=>(v i).val) (shapeComplement v)) : B a (slope c η) α⊗[ℚ]B a (slope c η) β :=
  castBTensor a (slope c η) ((shape_add_complement u).trans (realization_card R))
    ((shape_add_complement v).trans (realization_card T))
      (cellLeadingB a c η hc θ _ _ _ _ hon f g)

omit [∀ i, Fintype (A i)] in
lemma clearedConstantB_gridShape_leading (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (θ : ℝ) (hχ : SlopeEulerSymmetric a c η θ) {d e α β : I → ℕ} (h : d+e=α+β)
    (U V : ℤ) (f : S d) (g : S e)
    (hf : quotientAlg a (slope c η) d f∈unitalSourceFiltration a c η hc θ d U)
    (hg : quotientAlg a (slope c η) e g∈unitalSourceFiltration a c η hc θ e V)
    {s : Pack (A:=A)} (p : PackConvolution.Cut s)
    (R : Realization α (left p)) (T : Realization β (right p))
    (u : CutShape (left p)) (v : CutShape (right p))
    (hon : CellsOnSlope c η θ (fun i=>(u i).val) (shapeComplement u)
      (fun i=>(v i).val) (shapeComplement v)) :
    clearedConstantB a (slope c η) α β (quotientTensor a (slope c η) α β (gridShapeTensor a f g p R T u v))-
      gridShapeLeadingB a c η hc θ f g p R T u v hon∈
    unitalSourceTensorFiltration a c η hc θ α β (U+V+1) := by
  unfold gridShapeTensor gridShapeLeadingB
  rw [clearedConstantB_castTensor,←castBTensor_sub]
  apply castBTensor_mem_unitalSource
  apply clearedConstantB_cell_leading a c η hc θ hχ _ _ _ _ hon _ U V f g hf hg
  rw [(shape_add_complement u).trans (realization_card R),
    (shape_add_complement v).trans (realization_card T)]
  exact h

noncomputable def gridLeadingB (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (θ : ℝ) {d e α β : I → ℕ} (f : S d) (g : S e) {s : Pack (A:=A)}
    (p : PackConvolution.Cut s) (R : Realization α (left p)) (T : Realization β (right p)) :
    B a (slope c η) α⊗[ℚ]B a (slope c η) β :=
  ∑ u : CutShape (left p),∑ v : CutShape (right p),
    if hon : CellsOnSlope c η θ (fun i=>(u i).val) (shapeComplement u)
      (fun i=>(v i).val) (shapeComplement v)
    then gridShapeLeadingB a c η hc θ f g p R T u v hon else 0

omit [∀ i, Fintype (A i)] in
lemma clearedConstantB_grid_leading (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    {d e α β : I → ℕ} (hχ : SlopeEulerSymmetric a c η (slope c η α))
    (h : d+e=α+β) (U V : ℤ) (f : S d) (g : S e)
    (hf : quotientAlg a (slope c η) d f∈unitalSourceFiltration a c η hc (slope c η α) d U)
    (hg : quotientAlg a (slope c η) e g∈unitalSourceFiltration a c η hc (slope c η α) e V)
    {s : Pack (A:=A)} (p : PackConvolution.Cut s)
    (R : Realization α (left p)) (T : Realization β (right p))
    (ht : slope c η α=slope c η β) (hs : slope c η d=slope c η α) :
    clearedConstantB a (slope c η) α β (quotientTensor a (slope c η) α β (gridTensor a f g p R T))-
      gridLeadingB a c η hc (slope c η α) f g p R T∈
    unitalSourceTensorFiltration a c η hc (slope c η α) α β (U+V+1) := by
  rw [clearedConstantB_grid_sameSlope_support a c η hc f g p R T ht hs,gridLeadingB,
    ←Finset.sum_sub_distrib]
  apply Submodule.sum_mem
  intro u hu
  rw [←Finset.sum_sub_distrib]
  apply Submodule.sum_mem
  intro v hv
  split_ifs with hon
  · exact clearedConstantB_gridShape_leading a c η hc (slope c η α) hχ h U V f g hf hg p R T u v hon
  · rw [sub_self]
    exact Submodule.zero_mem _

lemma unitalSeparationConstant_shuffle_leading (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    {d e α β : I → ℕ} (hχ : SlopeEulerSymmetric a c η (slope c η α))
    (h : d+e=α+β) (U V : ℤ) (f : S d) (g : S e)
    (hf : quotientAlg a (slope c η) d f∈unitalSourceFiltration a c η hc (slope c η α) d U)
    (hg : quotientAlg a (slope c η) e g∈unitalSourceFiltration a c η hc (slope c η α) e V)
    (ht : slope c η α=slope c η β) (hs : slope c η d=slope c η α)
    {s : Pack (A:=A)} (R : Realization (α+β) s) :
    (unitalSeparationSeries a c η hc (Or.inr (Or.inr ht))
      (quotientAlg a (slope c η) (α+β) (castS h (shufflePolynomial a f g)))).coeff 0-
      gridLeadingB a c η hc (slope c η α) f g (cutRealizationEquiv R (firstCut α β)).val
        (leftRealization R (firstCut α β)) (rightRealization R (firstCut α β))∈
    unitalSourceTensorFiltration a c η hc (slope c η α) α β (U+V+1) := by
  rw [unitalSeparationConstant_shuffle_grid a c η hc h (Or.inr (Or.inr ht)) f g R]
  exact clearedConstantB_grid_leading a c η hc hχ h U V f g hf hg _ _ _ ht hs

end ElementaryPositivity.RawShuffle

end

end OAI
