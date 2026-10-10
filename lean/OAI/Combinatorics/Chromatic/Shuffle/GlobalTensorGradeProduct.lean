import Mathlib
import OAI.Combinatorics.Chromatic.Shuffle.UnitalCoproductComparison
import OAI.Combinatorics.Chromatic.Shuffle.TensorMiddleEnd

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct DirectSum
open ElementaryPositivity.SlopeArithmetic ElementaryPositivity.LinearFiltration
variable {I : Type*} [Fintype I] [DecidableEq I]
attribute [local instance] Classical.propDecidable

omit [DecidableEq I] in
lemma slopeDimensions_onSlope (c η : I → ℝ) (hc : ∀ i,0<c i) (θ : ℝ)
    (d : slopeDimensions c η hc θ) : OnSlopeOrZero c η θ d.val := d.property

omit [DecidableEq I] in
lemma slopeDimensions_cellsOnSlope (c η : I → ℝ) (hc : ∀ i,0<c i) (θ : ℝ)
    (d₁ e₁ d₂ e₂ : slopeDimensions c η hc θ) :
    OnSlopeOrZero c η θ d₁.val ∧ OnSlopeOrZero c η θ e₁.val ∧
      OnSlopeOrZero c η θ d₂.val ∧ OnSlopeOrZero c η θ e₂.val :=
  ⟨d₁.property,e₁.property,d₂.property,e₂.property⟩

lemma unitalLof_cast (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) {d e : slopeDimensions c η hc θ} {U V : ℤ}
    (h : d.val=e.val) (k : U=V) (x : UnitalSourceGrade a c η hc θ d.val U) :
    DirectSum.lof ℚ _ (unitalComponent a c η hc θ) (e,V) (unitalGradeCast a c η hc θ h k x)=
      DirectSum.lof ℚ _ (unitalComponent a c η hc θ) (d,U) x := by
  have hd : d=e := Subtype.ext h
  subst e; subst V
  rfl

lemma globalTensorGradeInclusion_cast (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) {d e d' e' : slopeDimensions c η hc θ} {U V : ℤ}
    (h : d.val=d'.val) (k : e.val=e'.val) (w : U=V)
    (x : UnitalSourceTensorGrade a c η hc θ d.val e.val U) :
    globalTensorGradeInclusion a c η hc θ d' e' V (unitalTensorGradeCast a c η hc θ h k w x)=
      globalTensorGradeInclusion a c η hc θ d e U x := by
  have hd : d=d' := Subtype.ext h
  have he : e=e' := Subtype.ext k
  subst d'; subst e'; subst V
  rfl

lemma unitalLof_shuffle (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) [hχ : Fact (SlopeEulerSymmetric a c η θ)]
    (d e : slopeDimensions c η hc θ) (U V : ℤ)
    (x : UnitalSourceGrade a c η hc θ d.val U) (y : UnitalSourceGrade a c η hc θ e.val V) :
    DirectSum.lof ℚ _ (unitalComponent a c η hc θ) (d+e,U+V)
      (unitalGradeShuffle a c η hc θ hχ.out d.val e.val (slopeDimensions_onSlope c η hc θ d) (slopeDimensions_onSlope c η hc θ e) U V x y)=
      DirectSum.lof ℚ _ (unitalComponent a c η hc θ) (d,U) x *
        DirectSum.lof ℚ _ (unitalComponent a c η hc θ) (e,V) y := by
  exact (DirectSum.of_mul_of (A:=unitalComponent a c η hc θ) (i:=(d,U)) (j:=(e,V)) x y).symm

lemma globalTensorGradeInclusion_part_add (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ)
    (d₁ e₁ d₂ e₂ : slopeDimensions c η hc θ) (W u : ℤ)
    (x : UnitalSourceGrade a c η hc θ (d₁.val+e₁.val) u)
    (y : UnitalSourceGrade a c η hc θ (d₂.val+e₂.val) (W-u)) :
    globalTensorGradeInclusion a c η hc θ (d₁+e₁) (d₂+e₂) W
      (unitalTensorGradeInclusionW a c η hc θ (d₁.val+e₁.val) (d₂.val+e₂.val) W u (x⊗ₜ[ℚ]y))=
      DirectSum.lof ℚ _ (unitalComponent a c η hc θ) (d₁+e₁,u) x⊗ₜ[ℚ]
        DirectSum.lof ℚ _ (unitalComponent a c η hc θ) (d₂+e₂,W-u) y := by
  have h := globalTensorGradeInclusion_part a c η hc θ (d₁+e₁) (d₂+e₂) W u x y
  simpa only [AddSubmonoid.coe_add] using h

theorem globalTensorGradeInclusion_signedProduct (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) [hχ : Fact (SlopeEulerSymmetric a c η θ)]
    (d₁ e₁ d₂ e₂ : slopeDimensions c η hc θ) (U V : ℤ)
    (x : UnitalSourceTensorGrade a c η hc θ d₁.val d₂.val U)
    (y : UnitalSourceTensorGrade a c η hc θ e₁.val e₂.val V) :
    globalTensorGradeInclusion a c η hc θ (d₁+e₁) (d₂+e₂) (U+V)
      (signedCellGradeMultiply a c η hc θ hχ.out d₁.val e₁.val d₂.val e₂.val
        (slopeDimensions_cellsOnSlope c η hc θ d₁ e₁ d₂ e₂) U V x y)=
    globalSignedTensorMultiply a c η hc θ
      (globalTensorGradeInclusion a c η hc θ d₁ d₂ U x)
      (globalTensorGradeInclusion a c η hc θ e₁ e₂ V y) := by
  induction x using unitalTensorGrade_induction a c η hc θ d₁.val d₂.val U with
  | hz => simp only [map_zero,LinearMap.zero_apply]
  | ha x x' hx hx' => simp only [map_add,LinearMap.add_apply,hx,hx']
  | ht u x₁ x₂ =>
    induction y using unitalTensorGrade_induction a c η hc θ e₁.val e₂.val V with
    | hz => simp only [map_zero]
    | ha y y' hy hy' => simp only [map_add,hy,hy']
    | ht v y₁ y₂ =>
      rw [signedCellGradeMultiply_part a c η hc θ hχ.out d₁.val e₁.val d₂.val e₂.val
        (slopeDimensions_cellsOnSlope c η hc θ d₁ e₁ d₂ e₂) U V u v x₁ x₂ y₁ y₂,
        map_smul,globalTensorGradeInclusion_part a c η hc θ d₁ d₂,
        globalTensorGradeInclusion_part a c η hc θ e₁ e₂]
      rw [globalTensorGradeInclusion_part_add,globalSignedTensorMultiply_tmul_lof]
      rw [unitalLof_cast a c η hc θ (d:=d₂+e₂) (e:=d₂+e₂)
        rfl (show (U-u)+(V-v)=U+V-(u+v) by omega)]
      rw [unitalLof_shuffle,unitalLof_shuffle]

lemma globalTensorGradeInclusion_signedProduct_cast (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) [hχ : Fact (SlopeEulerSymmetric a c η θ)]
    (d₁ e₁ d₂ e₂ α β : slopeDimensions c η hc θ) (U V : ℤ)
    (hα : (d₁+e₁).val=α.val) (hβ : (d₂+e₂).val=β.val)
    (x : UnitalSourceTensorGrade a c η hc θ d₁.val d₂.val U)
    (y : UnitalSourceTensorGrade a c η hc θ e₁.val e₂.val V) :
    globalTensorGradeInclusion a c η hc θ α β (U+V)
      (unitalTensorGradeCast a c η hc θ hα hβ rfl
        (signedCellGradeMultiply a c η hc θ hχ.out d₁.val e₁.val d₂.val e₂.val
          (slopeDimensions_cellsOnSlope c η hc θ d₁ e₁ d₂ e₂) U V x y))=
    globalSignedTensorMultiply a c η hc θ
      (globalTensorGradeInclusion a c η hc θ d₁ d₂ U x)
      (globalTensorGradeInclusion a c η hc θ e₁ e₂ V y) := by
  exact (globalTensorGradeInclusion_cast a c η hc θ
    (d:=d₁+e₁) (e:=d₂+e₂) (d':=α) (e':=β) hα hβ rfl _).trans
      (globalTensorGradeInclusion_signedProduct a c η hc θ d₁ e₁ d₂ e₂ U V x y)

lemma globalRawColumnProduct (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) [hχ : Fact (SlopeEulerSymmetric a c η θ)]
    (d₁ e₁ d₂ e₂ α β : I → ℕ) (hon : CellsOnSlope c η θ d₁ e₁ d₂ e₂)
    (hα : d₁+e₁=α) (hβ : d₂+e₂=β)
    (hA : OnSlopeOrZero c η θ α) (hB : OnSlopeOrZero c η θ β) (U V : ℤ)
    (x : UnitalSourceTensorGrade a c η hc θ d₁ d₂ U)
    (y : UnitalSourceTensorGrade a c η hc θ e₁ e₂ V) :
    globalTensorGradeInclusion a c η hc θ ⟨α,hA⟩ ⟨β,hB⟩ (U+V)
      (unitalTensorGradeCast a c η hc θ hα hβ rfl
        (signedCellGradeMultiply a c η hc θ hχ.out d₁ e₁ d₂ e₂ hon U V x y))=
    globalSignedTensorMultiply a c η hc θ
      (globalTensorGradeInclusion a c η hc θ ⟨d₁,hon.1⟩ ⟨d₂,hon.2.2.1⟩ U x)
      (globalTensorGradeInclusion a c η hc θ ⟨e₁,hon.2.1⟩ ⟨e₂,hon.2.2.2⟩ V y) := by
  have h := globalTensorGradeInclusion_signedProduct_cast a c η hc θ
    ⟨d₁,hon.1⟩ ⟨e₁,hon.2.1⟩ ⟨d₂,hon.2.2.1⟩ ⟨e₂,hon.2.2.2⟩
    ⟨α,hA⟩ ⟨β,hB⟩ U V hα hβ x y
  simp only at h
  exact h

end ElementaryPositivity.RawShuffle

end
section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct DirectSum
open ElementaryPositivity.SlopeArithmetic ElementaryPositivity.LinearFiltration
variable {I : Type*} [Fintype I] [DecidableEq I]

noncomputable def unitalTensorGradeComm (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (d e : I → ℕ) (W : ℤ) :
    UnitalSourceTensorGrade a c η hc θ d e W →ₗ[ℚ]
      UnitalSourceTensorGrade a c η hc θ e d W :=
  tensorGradeComm (unitalSourceFiltration a c η hc θ d) (unitalSourceFiltration a c η hc θ e) W

lemma unitalGradeCoproduct_cocommutative (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (hχ : SlopeEulerSymmetric a c η θ) (d e : I → ℕ)
    (hd : OnSlopeOrZero c η θ d) (he : OnSlopeOrZero c η θ e) (W : ℤ)
    (x : UnitalSourceGrade a c η hc θ (d+e) W) :
    unitalGradeCoproduct a c η hc θ e d (he.compatible hd) W
        (unitalGradeCast a c η hc θ (add_comm d e) rfl x)=
      (-1:ℚ)^eulerForm a d e • unitalTensorGradeComm a c η hc θ d e W
        (unitalGradeCoproduct a c η hc θ d e (hd.compatible he) W x) := by
  induction x using Submodule.Quotient.induction_on with
  | H x =>
    let : AddCommGroup (LinearDetection.additiveTensorFiltration
        (unitalSourceFiltration a c η hc θ e) (unitalSourceFiltration a c η hc θ d) W) :=
      Submodule.addCommGroup _
    let : Module ℚ (LinearDetection.additiveTensorFiltration
        (unitalSourceFiltration a c η hc θ e) (unitalSourceFiltration a c η hc θ d) W) :=
      Submodule.module _
    rw [unitalGradeCast_mk,unitalGradeCoproduct_mk,unitalGradeCoproduct_mk]
    apply sub_eq_zero.mp
    unfold unitalSourceTensorFiltration at *
    change Submodule.Quotient.mk
      ((⟨unitalSeparationConstant a c η hc e d (he.compatible hd)
          (unitalFiltrationCast a c η hc θ (add_comm d e) rfl x).val, _⟩ :
          LinearDetection.additiveTensorFiltration (unitalSourceFiltration a c η hc θ e)
            (unitalSourceFiltration a c η hc θ d) W) -
        (-1:ℚ)^eulerForm a d e • (tensorFiltrationComm
          (unitalSourceFiltration a c η hc θ d) (unitalSourceFiltration a c η hc θ e) W
          ⟨unitalSeparationConstant a c η hc d e (hd.compatible he) x.val, _⟩ :
            LinearDetection.additiveTensorFiltration (unitalSourceFiltration a c η hc θ e)
            (unitalSourceFiltration a c η hc θ d) W))=0
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    change unitalSeparationConstant a c η hc e d (he.compatible hd)
      (unitalFiltrationCast a c η hc θ (add_comm d e) rfl x).val -
      (-1:ℚ)^eulerForm a d e • TensorProduct.comm ℚ _ _
        (unitalSeparationConstant a c η hc d e (hd.compatible he) x.val)∈
          unitalSourceTensorFiltration a c η hc θ e d (W+1)
    rw [unitalFiltrationCast_val]
    exact unitalSeparationConstant_cocommutative_filtration a c η hc θ hχ d e hd he W x.val x.property

lemma unitalTensorGradeComm_part (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (d e : I → ℕ) (W u : ℤ)
    (x : UnitalSourceGrade a c η hc θ d u)
    (y : UnitalSourceGrade a c η hc θ e (W-u)) :
    unitalTensorGradeComm a c η hc θ d e W
      (unitalTensorGradeInclusionW a c η hc θ d e W u (x⊗ₜ[ℚ]y))=
      unitalTensorGradeInclusionW a c η hc θ e d W (W-u)
        (y⊗ₜ[ℚ]unitalGradeCast a c η hc θ rfl (show u=W-(W-u) by omega) x) := by
  induction x using Submodule.Quotient.induction_on with
  | H x =>
    induction y using Submodule.Quotient.induction_on with
    | H y =>
      simp only [unitalTensorGradeInclusionW,unitalGradeCast_mk,
        unitalTensorGradeComm]
      apply congrArg (mk _ _)
      apply Subtype.ext
      change y.val⊗ₜ[ℚ]x.val=y.val⊗ₜ[ℚ](unitalFiltrationCast a c η hc θ rfl _ x).val
      rw [unitalFiltrationCast_val,castB_rfl]

lemma globalTensorGradeInclusion_comm (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (d e : slopeDimensions c η hc θ) (W : ℤ)
    (x : UnitalSourceTensorGrade a c η hc θ d.val e.val W) :
    globalTensorGradeInclusion a c η hc θ e d W (unitalTensorGradeComm a c η hc θ d.val e.val W x)=
      TensorProduct.comm ℚ _ _ (globalTensorGradeInclusion a c η hc θ d e W x) := by
  induction x using unitalTensorGrade_induction a c η hc θ d.val e.val W with
  | hz => simp only [map_zero]
  | ha x y hx hy => simp only [map_add,hx,hy]
  | ht u x y =>
    rw [unitalTensorGradeComm_part,globalTensorGradeInclusion_part,globalTensorGradeInclusion_part,
      TensorProduct.comm_tmul,unitalLof_cast a c η hc θ (d:=d) (e:=d)]

end ElementaryPositivity.RawShuffle

end

end OAI
