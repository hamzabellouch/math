import Mathlib
import OAI.Combinatorics.Chromatic.Shuffle.UnitalGradeAlgebra
import OAI.Combinatorics.Chromatic.Shuffle.DimensionColumnLeading

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct
open ElementaryPositivity.SlopeArithmetic ElementaryPositivity.LinearDetection
open ElementaryPositivity.LinearFiltration
variable {I : Type*} [Fintype I] [DecidableEq I]

noncomputable def signedCellMultiplyB (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (d₁ e₁ d₂ e₂ : I → ℕ)
    (hon : CellsOnSlope c η θ d₁ e₁ d₂ e₂) :
    B a (slope c η) d₁⊗[ℚ]B a (slope c η) d₂ →ₗ[ℚ]
    B a (slope c η) e₁⊗[ℚ]B a (slope c η) e₂ →ₗ[ℚ]
    B a (slope c η) (d₁+e₁)⊗[ℚ]B a (slope c η) (d₂+e₂) :=
  ((-1 : ℚ)^eulerForm a d₂ e₁) • TensorProduct.curry
    ((twoTargetTransferB a c η hc d₁ e₁ d₂ e₂
      (hon.1.compatible hon.2.1) (hon.2.2.1.compatible hon.2.2.2)).comp
      (fourInterchangeB a (slope c η) d₁ e₁ d₂ e₂).toLinearMap)

lemma signedCellMultiplyB_apply (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (d₁ e₁ d₂ e₂ : I → ℕ)
    (hon : CellsOnSlope c η θ d₁ e₁ d₂ e₂)
    (x : B a (slope c η) d₁⊗[ℚ]B a (slope c η) d₂)
    (y : B a (slope c η) e₁⊗[ℚ]B a (slope c η) e₂) :
    signedCellMultiplyB a c η hc θ d₁ e₁ d₂ e₂ hon x y=
      ((-1 : ℚ)^eulerForm a d₂ e₁) •
        twoTargetTransferB a c η hc d₁ e₁ d₂ e₂
          (hon.1.compatible hon.2.1) (hon.2.2.1.compatible hon.2.2.2)
          (fourInterchangeB a (slope c η) d₁ e₁ d₂ e₂ (x⊗ₜ[ℚ]y)) := rfl

lemma signedCellMultiplyB_filtered (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (hχ : SlopeEulerSymmetric a c η θ)
    (d₁ e₁ d₂ e₂ : I → ℕ) (hon : CellsOnSlope c η θ d₁ e₁ d₂ e₂)
    (U V : ℤ) (x : B a (slope c η) d₁⊗[ℚ]B a (slope c η) d₂)
    (y : B a (slope c η) e₁⊗[ℚ]B a (slope c η) e₂)
    (hx : x∈unitalSourceTensorFiltration a c η hc θ d₁ d₂ U)
    (hy : y∈unitalSourceTensorFiltration a c η hc θ e₁ e₂ V) :
    signedCellMultiplyB a c η hc θ d₁ e₁ d₂ e₂ hon x y∈
      unitalSourceTensorFiltration a c η hc θ (d₁+e₁) (d₂+e₂) (U+V) := by
  rw [signedCellMultiplyB_apply]
  apply Submodule.smul_mem
  apply twoTargetTransferB_filtered a c η hc θ hχ d₁ e₁ d₂ e₂
    hon.1 hon.2.1 hon.2.2.1 hon.2.2.2 (U+V)
  exact interchange_mem_filtration (unitalSourceFiltration a c η hc θ d₁)
    (unitalSourceFiltration a c η hc θ d₂) (unitalSourceFiltration a c η hc θ e₁)
    (unitalSourceFiltration a c η hc θ e₂) U V x y hx hy

noncomputable def signedCellGradeMultiply (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (hχ : SlopeEulerSymmetric a c η θ)
    (d₁ e₁ d₂ e₂ : I → ℕ) (hon : CellsOnSlope c η θ d₁ e₁ d₂ e₂) (U V : ℤ) :
    UnitalSourceTensorGrade a c η hc θ d₁ d₂ U →ₗ[ℚ]
    UnitalSourceTensorGrade a c η hc θ e₁ e₂ V →ₗ[ℚ]
    UnitalSourceTensorGrade a c η hc θ (d₁+e₁) (d₂+e₂) (U+V) :=
  LinearFiltration.bilinear (unitalSourceTensorFiltration a c η hc θ d₁ d₂ U)
    (unitalSourceTensorFiltration a c η hc θ d₁ d₂ (U+1))
    (unitalSourceTensorFiltration a c η hc θ e₁ e₂ V)
    (unitalSourceTensorFiltration a c η hc θ e₁ e₂ (V+1))
    (unitalSourceTensorFiltration a c η hc θ (d₁+e₁) (d₂+e₂) (U+V))
    (unitalSourceTensorFiltration a c η hc θ (d₁+e₁) (d₂+e₂) (U+V+1))
    (signedCellMultiplyB a c η hc θ d₁ e₁ d₂ e₂ hon)
    (fun x hx y hy=>signedCellMultiplyB_filtered a c η hc θ hχ d₁ e₁ d₂ e₂ hon U V x y hx hy)
    (fun x hx y hy=>by simpa only [add_right_comm] using
      signedCellMultiplyB_filtered a c η hc θ hχ d₁ e₁ d₂ e₂ hon (U+1) V x y hx hy)
    (fun x hx y hy=>by simpa only [add_assoc] using
      signedCellMultiplyB_filtered a c η hc θ hχ d₁ e₁ d₂ e₂ hon U (V+1) x y hx hy)

lemma signedCellGradeMultiply_mk (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (hχ : SlopeEulerSymmetric a c η θ)
    (d₁ e₁ d₂ e₂ : I → ℕ) (hon : CellsOnSlope c η θ d₁ e₁ d₂ e₂) (U V : ℤ)
    (x : unitalSourceTensorFiltration a c η hc θ d₁ d₂ U)
    (y : unitalSourceTensorFiltration a c η hc θ e₁ e₂ V) :
    signedCellGradeMultiply a c η hc θ hχ d₁ e₁ d₂ e₂ hon U V
      (Submodule.Quotient.mk x) (Submodule.Quotient.mk y)=
      (Submodule.Quotient.mk ⟨signedCellMultiplyB a c η hc θ d₁ e₁ d₂ e₂ hon x.val y.val,
        signedCellMultiplyB_filtered a c η hc θ hχ d₁ e₁ d₂ e₂ hon U V x.val y.val x.property y.property⟩ :
        UnitalSourceTensorGrade a c η hc θ (d₁+e₁) (d₂+e₂) (U+V)) := rfl

end ElementaryPositivity.RawShuffle

end
section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct
open ElementaryPositivity.SlopeArithmetic ElementaryPositivity.LinearFiltration
open DimensionSplit SeparationInfinity
variable {I : Type*} [Fintype I] [DecidableEq I]
attribute [local instance] Classical.propDecidable

noncomputable def unitalTensorFiltrationCast (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) {d e d' e' : I → ℕ} {U V : ℤ}
    (h : d=d') (k : e=e') (w : U=V) :
    unitalSourceTensorFiltration a c η hc θ d e U ≃ₗ[ℚ]
      unitalSourceTensorFiltration a c η hc θ d' e' V := by
  subst d'; subst e'; subst V
  exact LinearEquiv.refl _ _

noncomputable def unitalTensorGradeCast (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) {d e d' e' : I → ℕ} {U V : ℤ}
    (h : d=d') (k : e=e') (w : U=V) :
    UnitalSourceTensorGrade a c η hc θ d e U ≃ₗ[ℚ]
      UnitalSourceTensorGrade a c η hc θ d' e' V := by
  subst d'; subst e'; subst V
  exact LinearEquiv.refl _ _

lemma unitalTensorFiltrationCast_val (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) {d e d' e' : I → ℕ} {U V : ℤ}
    (h : d=d') (k : e=e') (w : U=V)
    (x : unitalSourceTensorFiltration a c η hc θ d e U) :
    (unitalTensorFiltrationCast a c η hc θ h k w x).val=
      castBTensor a (slope c η) h k x.val := by
  subst d'; subst e'; subst V
  rfl

lemma unitalTensorGradeCast_mk (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) {d e d' e' : I → ℕ} {U V : ℤ}
    (h : d=d') (k : e=e') (w : U=V)
    (x : unitalSourceTensorFiltration a c η hc θ d e U) :
    unitalTensorGradeCast a c η hc θ h k w (Submodule.Quotient.mk x)=
      (Submodule.Quotient.mk (unitalTensorFiltrationCast a c η hc θ h k w x) :
        UnitalSourceTensorGrade a c η hc θ d' e' V) := by
  subst d'; subst e'; subst V
  rfl

noncomputable def splitCoproductFiltration (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) {d : I → ℕ} (p : DimensionSplit d)
    (hp : OnSlopeOrZero c η θ (left p) ∧ OnSlopeOrZero c η θ (right p)) (W : ℤ) :
    unitalSourceFiltration a c η hc θ d W →ₗ[ℚ]
      unitalSourceTensorFiltration a c η hc θ (left p) (right p) W :=
  (LinearFiltration.restrict _ _
    (unitalSeparationConstant a c η hc (left p) (right p) (hp.1.compatible hp.2))
    (fun x hx=>unitalSeparationSeries_coeff_filtration a c η hc θ _ _ (hp.1.compatible hp.2) W 0 x hx)).comp
    (unitalFiltrationCast a c η hc θ (left_add_right p).symm rfl).toLinearMap

noncomputable def splitCoproductGrade (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) {d : I → ℕ} (p : DimensionSplit d)
    (hp : OnSlopeOrZero c η θ (left p) ∧ OnSlopeOrZero c η θ (right p)) (W : ℤ) :
    UnitalSourceGrade a c η hc θ d W →ₗ[ℚ]
      UnitalSourceTensorGrade a c η hc θ (left p) (right p) W :=
  (unitalGradeCoproduct a c η hc θ (left p) (right p) (hp.1.compatible hp.2) W).comp
    (unitalGradeCast a c η hc θ (left_add_right p).symm rfl).toLinearMap

lemma splitCoproductGrade_mk (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) {d : I → ℕ} (p : DimensionSplit d)
    (hp : OnSlopeOrZero c η θ (left p) ∧ OnSlopeOrZero c η θ (right p)) (W : ℤ)
    (x : unitalSourceFiltration a c η hc θ d W) :
    splitCoproductGrade a c η hc θ p hp W (Submodule.Quotient.mk x)=
      (Submodule.Quotient.mk (splitCoproductFiltration a c η hc θ p hp W x) :
        UnitalSourceTensorGrade a c η hc θ (left p) (right p) W) := by
  exact congrArg (unitalGradeCoproduct a c η hc θ (left p) (right p) (hp.1.compatible hp.2) W)
    (unitalGradeCast_mk a c η hc θ (left_add_right p).symm rfl x)

lemma splitCoproductFiltration_val (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) {d : I → ℕ} (p : DimensionSplit d)
    (hp : OnSlopeOrZero c η θ (left p) ∧ OnSlopeOrZero c η θ (right p)) (W : ℤ)
    (x : unitalSourceFiltration a c η hc θ d W) :
    (splitCoproductFiltration a c η hc θ p hp W x).val=
      unitalSeparationConstant a c η hc (left p) (right p) (hp.1.compatible hp.2)
        (castB a (slope c η) (left_add_right p).symm x.val) := by
  change unitalSeparationConstant a c η hc _ _ _
    (unitalFiltrationCast a c η hc θ (left_add_right p).symm rfl x).val=_
  rw [unitalFiltrationCast_val]

lemma splitCoproductFiltration_val_mk (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) {d : I → ℕ} (p : DimensionSplit d)
    (hp : OnSlopeOrZero c η θ (left p) ∧ OnSlopeOrZero c η θ (right p)) (W : ℤ)
    (f : S d) (hf : quotientAlg a (slope c η) d f∈unitalSourceFiltration a c η hc θ d W) :
    (splitCoproductFiltration a c η hc θ p hp W ⟨_,hf⟩).val=
      (unitalSeparationSeries a c η hc (hp.1.compatible hp.2)
        (quotientAlg a (slope c η) (left p+right p) (castS (left_add_right p).symm f))).coeff 0 := by
  rw [splitCoproductFiltration_val,castB_mk]
  rfl

noncomputable def columnFiltrationTerm (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (hχ : SlopeEulerSymmetric a c η θ)
    {d e α β : I → ℕ} (U V : ℤ)
    (x : unitalSourceFiltration a c η hc θ d U)
    (y : unitalSourceFiltration a c η hc θ e V) (s : ColumnDimensionGrid d e α β) :
    unitalSourceTensorFiltration a c η hc θ α β (U+V) :=
  if hon : CellsOnSlope c η θ (left s.val.1) (left s.val.2) (right s.val.1) (right s.val.2) then
    unitalTensorFiltrationCast a c η hc θ s.property.1 s.property.2 rfl
      ⟨signedCellMultiplyB a c η hc θ _ _ _ _ hon
          (splitCoproductFiltration a c η hc θ s.val.1 ⟨hon.1,hon.2.2.1⟩ U x).val
          (splitCoproductFiltration a c η hc θ s.val.2 ⟨hon.2.1,hon.2.2.2⟩ V y).val,
        signedCellMultiplyB_filtered a c η hc θ hχ _ _ _ _ hon U V _ _
          (splitCoproductFiltration a c η hc θ s.val.1 ⟨hon.1,hon.2.2.1⟩ U x).property
          (splitCoproductFiltration a c η hc θ s.val.2 ⟨hon.2.1,hon.2.2.2⟩ V y).property⟩
  else 0

noncomputable def columnGradeTerm (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (hχ : SlopeEulerSymmetric a c η θ)
    {d e α β : I → ℕ} (U V : ℤ)
    (x : UnitalSourceGrade a c η hc θ d U)
    (y : UnitalSourceGrade a c η hc θ e V) (s : ColumnDimensionGrid d e α β) :
    UnitalSourceTensorGrade a c η hc θ α β (U+V) :=
  if hon : CellsOnSlope c η θ (left s.val.1) (left s.val.2) (right s.val.1) (right s.val.2) then
    unitalTensorGradeCast a c η hc θ s.property.1 s.property.2 rfl
      (signedCellGradeMultiply a c η hc θ hχ _ _ _ _ hon U V
        (splitCoproductGrade a c η hc θ s.val.1 ⟨hon.1,hon.2.2.1⟩ U x)
        (splitCoproductGrade a c η hc θ s.val.2 ⟨hon.2.1,hon.2.2.2⟩ V y))
  else 0

lemma columnGradeTerm_mk (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (hχ : SlopeEulerSymmetric a c η θ)
    {d e α β : I → ℕ} (U V : ℤ)
    (x : unitalSourceFiltration a c η hc θ d U)
    (y : unitalSourceFiltration a c η hc θ e V) (s : ColumnDimensionGrid d e α β) :
    columnGradeTerm a c η hc θ hχ U V (Submodule.Quotient.mk x) (Submodule.Quotient.mk y) s=
      (Submodule.Quotient.mk (columnFiltrationTerm a c η hc θ hχ U V x y s) :
        UnitalSourceTensorGrade a c η hc θ α β (U+V)) := by
  unfold columnGradeTerm columnFiltrationTerm
  split_ifs with hon
  · rw [splitCoproductGrade_mk,splitCoproductGrade_mk,signedCellGradeMultiply_mk,unitalTensorGradeCast_mk]
  · rfl

lemma columnFiltrationTerm_val_mk (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (hχ : SlopeEulerSymmetric a c η θ)
    {d e α β : I → ℕ} (U V : ℤ) (f : S d) (g : S e)
    (hf : quotientAlg a (slope c η) d f∈unitalSourceFiltration a c η hc θ d U)
    (hg : quotientAlg a (slope c η) e g∈unitalSourceFiltration a c η hc θ e V)
    (s : ColumnDimensionGrid d e α β) :
    (columnFiltrationTerm a c η hc θ hχ U V ⟨_,hf⟩ ⟨_,hg⟩ s).val=
      dimensionColumnLeadingB a c η hc θ f g s := by
  unfold columnFiltrationTerm dimensionColumnLeadingB
  split_ifs with hon
  · rw [unitalTensorFiltrationCast_val,cellLeadingB,
      dite_eq_left ⟨left_add_right s.val.1,left_add_right s.val.2⟩]
    congr 1
    apply congrArg₂ (fun x y=>signedCellMultiplyB a c η hc θ _ _ _ _ hon x y)
    · exact splitCoproductFiltration_val_mk a c η hc θ _ _ U f hf
    · exact splitCoproductFiltration_val_mk a c η hc θ _ _ V g hg
  · rfl

theorem unitalGradeCoproduct_shuffle_column (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) {d e α β : I → ℕ} (hχ : SlopeEulerSymmetric a c η θ)
    (h : d+e=α+β) (hd : OnSlopeOrZero c η θ d) (he : OnSlopeOrZero c η θ e)
    (hα : OnSlopeOrZero c η θ α) (hβ : OnSlopeOrZero c η θ β) (U V : ℤ)
    (x : UnitalSourceGrade a c η hc θ d U) (y : UnitalSourceGrade a c η hc θ e V) :
    unitalGradeCoproduct a c η hc θ α β (hα.compatible hβ) (U+V)
      (unitalGradeCast a c η hc θ h rfl (unitalGradeShuffle a c η hc θ hχ d e hd he U V x y))=
      ∑ s : ColumnDimensionGrid d e α β,columnGradeTerm a c η hc θ hχ U V x y s := by
  induction x using Submodule.Quotient.induction_on with
  | H x =>
    induction y using Submodule.Quotient.induction_on with
    | H y =>
      rcases x with ⟨x,hx⟩
      rcases y with ⟨y,hy⟩
      induction x using Submodule.Quotient.induction_on with
      | H f =>
        induction y using Submodule.Quotient.induction_on with
        | H g =>
          simp only [unitalGradeShuffle_mk,unitalGradeCast_mk,unitalGradeCoproduct_mk,
            columnGradeTerm_mk]
          change mk _ _ _=∑ s : ColumnDimensionGrid d e α β,
            mk _ _ (columnFiltrationTerm a c η hc θ hχ U V ⟨_,hx⟩ ⟨_,hy⟩ s)
          rw [←map_sum]
          apply (mk_eq_mk_iff_sub_mem _ _ _ _).mpr
          dsimp only [Subtype.coe_mk]
          rw [unitalFiltrationCast_val]
          have hv : (∑ s : ColumnDimensionGrid d e α β,
              columnFiltrationTerm a c η hc θ hχ U V ⟨_,hx⟩ ⟨_,hy⟩ s).val=
              ∑ s : ColumnDimensionGrid d e α β,dimensionColumnLeadingB a c η hc θ f g s := by
            rw [Submodule.coe_sum]
            exact Finset.sum_congr rfl (fun s _=>columnFiltrationTerm_val_mk a c η hc θ hχ U V f g hx hy s)
          rw [hv]
          change (unitalSeparationSeries a c η hc (hα.compatible hβ)
            (castB a (slope c η) h (quotientAlg a (slope c η) (d+e) (shufflePolynomial a f g)))).coeff 0-_∈_
          rw [castB_mk]
          let R : Realization (α+β) (A:=fun i=>Fin ((α+β) i)) (fun _=>Finset.univ) :=
            fun _=>(Equiv.subtypeUnivEquiv (fun _=>Finset.mem_univ _)).symm
          exact unitalSeparationConstant_shuffle_column a c η hc θ hχ h U V f g hx hy hα hβ hd R

end ElementaryPositivity.RawShuffle

end

end OAI
