import Mathlib
import OAI.Combinatorics.Chromatic.Shuffle.UnitalCoproductUnits
import OAI.Combinatorics.Chromatic.Shuffle.UnitalTensorGradeInclusion

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct DirectSum
open ElementaryPositivity.SlopeArithmetic ElementaryPositivity.LinearFiltration
variable {I : Type*} [Fintype I] [DecidableEq I]

lemma unitalGradeCoproduct_zero_left (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (d : I → ℕ) (W : ℤ)
    (f : UnitalSourceGrade a c η hc θ d W) :
    unitalGradeCoproduct a c η hc θ 0 d (Or.inl rfl) W
      (unitalGradeCast a c η hc θ (zero_add d).symm rfl f)=
      unitalTensorGradeInclusionW a c η hc θ 0 d W 0
        (unitalGradeOne a c η hc θ⊗ₜ[ℚ]
          unitalGradeCast a c η hc θ rfl (sub_zero W).symm f) := by
  induction f using Submodule.Quotient.induction_on with
  | H f =>
    simp only [unitalGradeCast_mk,unitalGradeOne,unitalTensorGradeInclusionW,
      unitalGradeCoproduct_mk]
    apply congrArg (mk _ _)
    apply Subtype.ext
    change unitalSeparationConstant a c η hc 0 d (Or.inl rfl)
      (unitalFiltrationCast a c η hc θ (zero_add d).symm rfl f).val=
      (1:B a (slope c η) 0)⊗ₜ[ℚ]
        (unitalFiltrationCast a c η hc θ rfl (sub_zero W).symm f).val
    rw [unitalFiltrationCast_val,unitalFiltrationCast_val]
    exact unitalSeparationConstant_zero_left a c η hc d f.val

lemma unitalGradeCoproduct_zero_right (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (d : I → ℕ) (W : ℤ)
    (f : UnitalSourceGrade a c η hc θ d W) :
    unitalGradeCoproduct a c η hc θ d 0 (Or.inr (Or.inl rfl)) W
      (unitalGradeCast a c η hc θ (add_zero d).symm rfl f)=
      unitalTensorGradeInclusionW a c η hc θ d 0 W W
        (f⊗ₜ[ℚ]unitalGradeCast a c η hc θ rfl (sub_self W).symm
          (unitalGradeOne a c η hc θ)) := by
  induction f using Submodule.Quotient.induction_on with
  | H f =>
    simp only [unitalGradeCast_mk,unitalGradeOne,unitalTensorGradeInclusionW,
      unitalGradeCoproduct_mk]
    apply congrArg (mk _ _)
    apply Subtype.ext
    change unitalSeparationConstant a c η hc d 0 (Or.inr (Or.inl rfl))
      (unitalFiltrationCast a c η hc θ (add_zero d).symm rfl f).val=
      f.val⊗ₜ[ℚ](unitalFiltrationCast a c η hc θ rfl (sub_self W).symm _).val
    rw [unitalFiltrationCast_val,unitalFiltrationCast_val]
    exact unitalSeparationConstant_zero_right a c η hc d f.val

end ElementaryPositivity.RawShuffle

end
section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct DirectSum
open ElementaryPositivity.SlopeArithmetic ElementaryPositivity.LinearFiltration DimensionSplit
variable {I : Type*} [Fintype I] [DecidableEq I]
attribute [local instance] Classical.propDecidable

noncomputable def zeroGradeCounit (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) : UnitalSourceGrade a c η hc θ 0 0 →ₗ[ℚ] ℚ :=
  (next (unitalSourceFiltration a c η hc θ 0 0)
    (unitalSourceFiltration a c η hc θ 0 (0+1))).liftQ
    ((zeroQuotientEquiv a (slope c η)).toLinearMap.comp
      (unitalSourceFiltration a c η hc θ 0 0).subtype) (by
        intro x hx
        have hx0 : x.val=0 := by
          change x.val∈unitalSourceFiltration a c η hc θ 0 (0+1) at hx
          simpa only [unitalSourceFiltration_zero,Int.reduceAdd,Int.reduceLE,ite_false,
            Submodule.mem_bot] using hx
        change zeroQuotientEquiv a (slope c η) x.val=0
        rw [hx0,map_zero])

lemma zeroGradeCounit_mk (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (x : unitalSourceFiltration a c η hc θ 0 0) :
    zeroGradeCounit a c η hc θ (Submodule.Quotient.mk x)=
      zeroQuotientEquiv a (slope c η) x.val := rfl

lemma zeroGradeCounit_one (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) :
    zeroGradeCounit a c η hc θ (unitalGradeOne a c η hc θ)=1 := by
  rw [unitalGradeOne,zeroGradeCounit_mk]
  change MvPolynomial.constantCoeff (1 : S (0:I → ℕ)).val=1
  simp

lemma zeroGrade_eq_scalar (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (x : UnitalSourceGrade a c η hc θ 0 0) :
    x=zeroGradeCounit a c η hc θ x • unitalGradeOne a c η hc θ := by
  induction x using Submodule.Quotient.induction_on with
  | H x =>
    rw [zeroGradeCounit_mk,unitalGradeOne]
    change mk _ _ x = mk _ _ (_ • _)
    apply congrArg (mk _ _)
    apply Subtype.ext
    change x.val=zeroQuotientEquiv a (slope c η) x.val • (1 : B a (slope c η) 0)
    apply (zeroQuotientEquiv a (slope c η)).injective
    rw [map_smul]
    change zeroQuotientEquiv a (slope c η) x.val =
      zeroQuotientEquiv a (slope c η) x.val • MvPolynomial.constantCoeff (1 : S (0:I → ℕ)).val
    simp

noncomputable def globalUnit (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) : UnitalShuffle a c η hc θ :=
  DirectSum.lof ℚ _ (unitalComponent a c η hc θ) 0 (unitalGradeOne a c η hc θ)

noncomputable def globalCounit (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) : UnitalShuffle a c η hc θ →ₗ[ℚ] ℚ :=
  (zeroGradeCounit a c η hc θ).comp
    (DirectSum.component ℚ _ (unitalComponent a c η hc θ) 0)

lemma globalCounit_lof_zero (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (x : unitalComponent a c η hc θ 0) :
    globalCounit a c η hc θ (DirectSum.lof ℚ _ (unitalComponent a c η hc θ) 0 x)=
      zeroGradeCounit a c η hc θ x := by
  rw [globalCounit,LinearMap.comp_apply,DirectSum.component.lof_self]

lemma globalCounit_lof_ne (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (k : SlopeWeight c η hc θ) (hk : k≠0)
    (x : unitalComponent a c η hc θ k) :
    globalCounit a c η hc θ (DirectSum.lof ℚ _ (unitalComponent a c η hc θ) k x)=0 := by
  simp only [globalCounit,LinearMap.comp_apply,DirectSum.component.of,dite_eq_right hk,map_zero]

lemma globalCounit_unit (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) : globalCounit a c η hc θ (globalUnit a c η hc θ)=1 := by
  rw [globalUnit,globalCounit_lof_zero,zeroGradeCounit_one]

lemma globalUnit_eq_one (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) [Fact (SlopeEulerSymmetric a c η θ)] :
    globalUnit a c η hc θ=1 := rfl

lemma globalCounit_tensor_nonzero_left (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (d e : slopeDimensions c η hc θ) (hd : d.val≠0)
    (W : ℤ) (x : UnitalSourceTensorGrade a c η hc θ d.val e.val W) :
    TensorProduct.map (globalCounit a c η hc θ) LinearMap.id
      (globalTensorGradeInclusion a c η hc θ d e W x)=0 := by
  induction x using unitalTensorGrade_induction a c η hc θ d.val e.val W with
  | hz => simp only [map_zero]
  | ha x y hx hy => simp only [map_add,hx,hy,add_zero]
  | ht u x y =>
    rw [globalTensorGradeInclusion_part,TensorProduct.map_tmul,
      globalCounit_lof_ne a c η hc θ (d,u) (by intro h; exact hd (congrArg (fun k=>k.1.val) h)),
      TensorProduct.zero_tmul]

lemma globalCounit_tensor_nonzero_right (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (d e : slopeDimensions c η hc θ) (he : e.val≠0)
    (W : ℤ) (x : UnitalSourceTensorGrade a c η hc θ d.val e.val W) :
    TensorProduct.map LinearMap.id (globalCounit a c η hc θ)
      (globalTensorGradeInclusion a c η hc θ d e W x)=0 := by
  induction x using unitalTensorGrade_induction a c η hc θ d.val e.val W with
  | hz => simp only [map_zero]
  | ha x y hx hy => simp only [map_add,hx,hy,add_zero]
  | ht u x y =>
    rw [globalTensorGradeInclusion_part,TensorProduct.map_tmul,
      globalCounit_lof_ne a c η hc θ (e,W-u) (by intro h; exact he (congrArg (fun k=>k.1.val) h)),
      TensorProduct.tmul_zero]
end ElementaryPositivity.RawShuffle

end

end OAI
