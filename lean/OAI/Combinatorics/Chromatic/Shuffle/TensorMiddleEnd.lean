import Mathlib
import OAI.Combinatorics.Chromatic.Shuffle.SignedTensorGradeProduct
import OAI.Combinatorics.Chromatic.Shuffle.UnitalTensorGradeInclusion
import OAI.Combinatorics.Chromatic.Walls.DirectSumBilinear

namespace OAI

section
namespace ElementaryPositivity
open scoped TensorProduct
variable {A B C D : Type*}
variable [AddCommGroup A] [Module ℚ A] [AddCommGroup B] [Module ℚ B]
variable [AddCommGroup C] [Module ℚ C] [AddCommGroup D] [Module ℚ D]

noncomputable def middleGroup : (A⊗[ℚ]B)⊗[ℚ](C⊗[ℚ]D) ≃ₗ[ℚ] (A⊗[ℚ](B⊗[ℚ]C))⊗[ℚ]D :=
  (TensorProduct.assoc ℚ (A⊗[ℚ]B) C D).symm.trans
    (TensorProduct.congr (TensorProduct.assoc ℚ A B C) (LinearEquiv.refl ℚ D))

lemma middleGroup_tmul (a : A) (b : B) (c : C) (d : D) :
    middleGroup ((a⊗ₜ[ℚ]b)⊗ₜ[ℚ](c⊗ₜ[ℚ]d))=(a⊗ₜ[ℚ](b⊗ₜ[ℚ]c))⊗ₜ[ℚ]d := rfl

lemma middleGroup_symm_tmul (a : A) (b : B) (c : C) (d : D) :
    middleGroup.symm ((a⊗ₜ[ℚ](b⊗ₜ[ℚ]c))⊗ₜ[ℚ]d)=(a⊗ₜ[ℚ]b)⊗ₜ[ℚ](c⊗ₜ[ℚ]d) := rfl

noncomputable def middleEnd (f : B⊗[ℚ]C →ₗ[ℚ] B⊗[ℚ]C) :
    (A⊗[ℚ]B)⊗[ℚ](C⊗[ℚ]D) →ₗ[ℚ] (A⊗[ℚ]B)⊗[ℚ](C⊗[ℚ]D) :=
  middleGroup.symm.toLinearMap.comp
    ((TensorProduct.map (TensorProduct.map (LinearMap.id : A →ₗ[ℚ] A) f)
      (LinearMap.id : D →ₗ[ℚ] D)).comp middleGroup.toLinearMap)

lemma middleEnd_scalar (f : B⊗[ℚ]C →ₗ[ℚ] B⊗[ℚ]C)
    (a : A) (b : B) (c : C) (d : D) (r : ℚ) (h : f (b⊗ₜ[ℚ]c)=r•(b⊗ₜ[ℚ]c)) :
    middleEnd f ((a⊗ₜ[ℚ]b)⊗ₜ[ℚ](c⊗ₜ[ℚ]d))=r•((a⊗ₜ[ℚ]b)⊗ₜ[ℚ](c⊗ₜ[ℚ]d)) := by
  change middleGroup.symm ((TensorProduct.map (TensorProduct.map LinearMap.id f) LinearMap.id)
    (middleGroup ((a⊗ₜ[ℚ]b)⊗ₜ[ℚ](c⊗ₜ[ℚ]d))))=_
  rw [middleGroup_tmul,TensorProduct.map_tmul,TensorProduct.map_tmul,h]
  change middleGroup.symm ((a⊗ₜ[ℚ](r•(b⊗ₜ[ℚ]c)))⊗ₜ[ℚ]d)=_
  rw [TensorProduct.tmul_smul,←TensorProduct.smul_tmul',map_smul,middleGroup_symm_tmul]

end ElementaryPositivity

end
section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct DirectSum
open ElementaryPositivity.SlopeArithmetic
variable {I : Type*} [Fintype I] [DecidableEq I]
attribute [local instance] Classical.propDecidable

noncomputable def globalSignOperator (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) :
    UnitalShuffle a c η hc θ⊗[ℚ]UnitalShuffle a c η hc θ →ₗ[ℚ]
      UnitalShuffle a c η hc θ⊗[ℚ]UnitalShuffle a c η hc θ :=
  TensorProduct.lift (directSumBilinear (unitalComponent a c η hc θ)
    (unitalComponent a c η hc θ) _ (fun k l=>TensorProduct.curry
      (((-1:ℚ)^eulerForm a k.1.val l.1.val) • TensorProduct.map
        (DirectSum.lof ℚ (SlopeWeight c η hc θ) (unitalComponent a c η hc θ) k)
        (DirectSum.lof ℚ (SlopeWeight c η hc θ) (unitalComponent a c η hc θ) l))))

lemma globalSignOperator_tmul_lof (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (k l : SlopeWeight c η hc θ)
    (x : unitalComponent a c η hc θ k) (y : unitalComponent a c η hc θ l) :
    globalSignOperator a c η hc θ
      (DirectSum.lof ℚ _ (unitalComponent a c η hc θ) k x⊗ₜ[ℚ]
        DirectSum.lof ℚ _ (unitalComponent a c η hc θ) l y)=
      ((-1:ℚ)^eulerForm a k.1.val l.1.val) •
        (DirectSum.lof ℚ _ (unitalComponent a c η hc θ) k x⊗ₜ[ℚ]
          DirectSum.lof ℚ _ (unitalComponent a c η hc θ) l y) := by
  rw [globalSignOperator,TensorProduct.lift.tmul,directSumBilinear_lof]
  rfl

noncomputable def globalSignedTensorMultiply (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) [Fact (SlopeEulerSymmetric a c η θ)] :
    UnitalShuffle a c η hc θ⊗[ℚ]UnitalShuffle a c η hc θ →ₗ[ℚ]
    UnitalShuffle a c η hc θ⊗[ℚ]UnitalShuffle a c η hc θ →ₗ[ℚ]
    UnitalShuffle a c η hc θ⊗[ℚ]UnitalShuffle a c η hc θ :=
  TensorProduct.curry ((TensorProduct.lift
    (Algebra.lmul ℚ (UnitalShuffle a c η hc θ⊗[ℚ]UnitalShuffle a c η hc θ)).toLinearMap).comp
      (middleEnd (globalSignOperator a c η hc θ)))

lemma globalSignedTensorMultiply_tmul_lof (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) [Fact (SlopeEulerSymmetric a c η θ)]
    (k l m n : SlopeWeight c η hc θ)
    (x : unitalComponent a c η hc θ k) (y : unitalComponent a c η hc θ l)
    (z : unitalComponent a c η hc θ m) (w : unitalComponent a c η hc θ n) :
    globalSignedTensorMultiply a c η hc θ
      (DirectSum.lof ℚ _ (unitalComponent a c η hc θ) k x⊗ₜ[ℚ]
        DirectSum.lof ℚ _ (unitalComponent a c η hc θ) l y)
      (DirectSum.lof ℚ _ (unitalComponent a c η hc θ) m z⊗ₜ[ℚ]
        DirectSum.lof ℚ _ (unitalComponent a c η hc θ) n w)=
      ((-1:ℚ)^eulerForm a l.1.val m.1.val) •
        ((DirectSum.lof ℚ _ (unitalComponent a c η hc θ) k x *
          DirectSum.lof ℚ _ (unitalComponent a c η hc θ) m z)⊗ₜ[ℚ]
         (DirectSum.lof ℚ _ (unitalComponent a c η hc θ) l y *
          DirectSum.lof ℚ _ (unitalComponent a c η hc θ) n w)) := by
  unfold globalSignedTensorMultiply
  simp only [TensorProduct.curry_apply,LinearMap.comp_apply]
  rw [middleEnd_scalar _ _ _ _ _ _ (globalSignOperator_tmul_lof a c η hc θ l m y z),map_smul,
    TensorProduct.lift.tmul]
  exact congrArg (fun t=>((-1:ℚ)^eulerForm a l.1.val m.1.val) • t)
    (Algebra.TensorProduct.tmul_mul_tmul _ _ _ _)

end ElementaryPositivity.RawShuffle

end
section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct DirectSum
open ElementaryPositivity.SlopeArithmetic ElementaryPositivity.LinearFiltration
variable {I : Type*} [Fintype I] [DecidableEq I]
attribute [local instance] Classical.propDecidable

lemma signedCellMultiplyB_tmul (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (d₁ e₁ d₂ e₂ : I → ℕ)
    (hon : CellsOnSlope c η θ d₁ e₁ d₂ e₂)
    (x : B a (slope c η) d₁) (y : B a (slope c η) d₂)
    (z : B a (slope c η) e₁) (w : B a (slope c η) e₂) :
    signedCellMultiplyB a c η hc θ d₁ e₁ d₂ e₂ hon (x⊗ₜ[ℚ]y) (z⊗ₜ[ℚ]w)=
      ((-1:ℚ)^eulerForm a d₂ e₁) •
        (shuffleBUnit a c η hc d₁ e₁ (hon.1.compatible hon.2.1) x z⊗ₜ[ℚ]
          shuffleBUnit a c η hc d₂ e₂ (hon.2.2.1.compatible hon.2.2.2) y w) := rfl

private lemma mk_eq_smul_of_val_eq {M : Type*} [AddCommGroup M] [Module ℚ M]
    (F G : Submodule ℚ M) (x y : F) (r : ℚ) (h : x.val=r • y.val) :
    mk F G x=r • mk F G y :=
  (congrArg (mk F G) (Subtype.ext h)).trans ((mk F G).map_smul r y)

lemma signedCellGradeMultiply_part (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (hχ : SlopeEulerSymmetric a c η θ)
    (d₁ e₁ d₂ e₂ : I → ℕ) (hon : CellsOnSlope c η θ d₁ e₁ d₂ e₂)
    (U V u v : ℤ)
    (x : UnitalSourceGrade a c η hc θ d₁ u)
    (y : UnitalSourceGrade a c η hc θ d₂ (U-u))
    (z : UnitalSourceGrade a c η hc θ e₁ v)
    (w : UnitalSourceGrade a c η hc θ e₂ (V-v)) :
    signedCellGradeMultiply a c η hc θ hχ d₁ e₁ d₂ e₂ hon U V
      (unitalTensorGradeInclusionW a c η hc θ d₁ d₂ U u (x⊗ₜ[ℚ]y))
      (unitalTensorGradeInclusionW a c η hc θ e₁ e₂ V v (z⊗ₜ[ℚ]w))=
    ((-1:ℚ)^eulerForm a d₂ e₁) •
      unitalTensorGradeInclusionW a c η hc θ (d₁+e₁) (d₂+e₂) (U+V) (u+v)
        (unitalGradeShuffle a c η hc θ hχ d₁ e₁ hon.1 hon.2.1 u v x z⊗ₜ[ℚ]
          unitalGradeCast a c η hc θ rfl (show (U-u)+(V-v)=U+V-(u+v) by omega)
            (unitalGradeShuffle a c η hc θ hχ d₂ e₂ hon.2.2.1 hon.2.2.2 (U-u) (V-v) y w)) := by
  induction x using Submodule.Quotient.induction_on with
  | H x =>
    induction y using Submodule.Quotient.induction_on with
    | H y =>
      induction z using Submodule.Quotient.induction_on with
      | H z =>
        induction w using Submodule.Quotient.induction_on with
        | H w =>
          simp only [unitalGradeShuffle_mk,unitalGradeCast_mk,unitalTensorGradeInclusionW]
          apply mk_eq_smul_of_val_eq
          change signedCellMultiplyB a c η hc θ _ _ _ _ hon
            (x.val⊗ₜ[ℚ]y.val) (z.val⊗ₜ[ℚ]w.val)=
              ((-1:ℚ)^eulerForm a d₂ e₁) •
                (shuffleBUnit a c η hc d₁ e₁ _ x.val z.val⊗ₜ[ℚ]
                  (unitalFiltrationCast a c η hc θ rfl _ _).val)
          rw [unitalFiltrationCast_val]
          exact signedCellMultiplyB_tmul a c η hc θ d₁ e₁ d₂ e₂ hon x.val y.val z.val w.val

end ElementaryPositivity.RawShuffle

end

end OAI
