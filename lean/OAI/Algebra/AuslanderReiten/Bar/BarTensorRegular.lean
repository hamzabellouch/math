import OAI.Algebra.AuslanderReiten.Tensor.ExternalEnveloping
import OAI.Algebra.AuslanderReiten.Bar.BarBimodule
import OAI.Algebra.AuslanderReiten.Coordinates.TensorRestriction
import OAI.Algebra.AuslanderReiten.BaseChange.ScalarExtensionComplete

namespace OAI

noncomputable section
namespace ArExplicit
open CategoryTheory
open scoped TensorProduct
universe u
variable (k A B : Type u) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]

attribute [local instance 2000] moduleCatBaseModule moduleCatBaseTower

def barZeroScalarEquiv : AbsoluteBar.moduleObject k A 0 ≃ₗ[k] A where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' a x := by
    change AbsoluteBar.representation k A 0 (algebraMap k (AbsoluteBar.Enveloping k A) a)
      (show A from x) = a • (show A from x)
    rw [AlgHom.commutes]
    rfl

def barTensorZeroEquiv :
    ExternalTensor.envelopingObject k A B
      (ExternalTensor.moduleObject k (AbsoluteBar.Enveloping k A) (AbsoluteBar.Enveloping k B)
        (AbsoluteBar.moduleObject k A 0) (AbsoluteBar.moduleObject k B 0)) ≃ₗ[
          ExternalTensor.EnvelopingProduct k A B] AbsoluteBar.moduleObject k (A ⊗[k] B) 0 where
  __ := (TensorProduct.congr (barZeroScalarEquiv k A) (barZeroScalarEquiv k B)).toAddEquiv
  map_smul' a x := by
    let z : (AbsoluteBar.moduleObject k A 0) ⊗[k] (AbsoluteBar.moduleObject k B 0) := x
    let e := TensorProduct.congr (barZeroScalarEquiv k A) (barZeroScalarEquiv k B)
    change e (ExternalTensor.representation k (AbsoluteBar.Enveloping k A) (AbsoluteBar.Enveloping k B)
      (AbsoluteBar.moduleObject k A 0) (AbsoluteBar.moduleObject k B 0)
        ((ExternalTensor.envelopingEquiv k A B).symm a) z) =
      AbsoluteBar.representation k (A ⊗[k] B) 0 a (e z)
    obtain ⟨a, rfl⟩ := (ExternalTensor.envelopingEquiv k A B).surjective a
    rw [AlgEquiv.symm_apply_apply]
    induction a using TensorProduct.inductionOn with
    | add a b ha hb => simp only [map_add, LinearMap.add_apply, ha, hb]
    | tmul a b =>
      induction a using TensorProduct.inductionOn with
      | add a c ha hc => simp only [TensorProduct.add_tmul, map_add, LinearMap.add_apply, ha, hc]
      | tmul a c =>
        induction b using TensorProduct.inductionOn with
        | add b d hb hd => simp only [TensorProduct.tmul_add, map_add, LinearMap.add_apply, hb, hd]
        | tmul b d =>
          have he := ExternalTensor.envelopingEquiv_tmul k A B a (MulOpposite.unop c) b (MulOpposite.unop d)
          simp only [MulOpposite.op_unop] at he
          rw [he]
          induction z using TensorProduct.inductionOn with
          | add x y hx hy => simp only [map_add, hx, hy]
          | tmul x y =>
            let xa : A := x
            let yb : B := y
            change (a * (xa * MulOpposite.unop c)) ⊗ₜ[k]
              (b * (yb * MulOpposite.unop d)) =
              (a ⊗ₜ[k] b) * ((xa ⊗ₜ[k] yb) *
                ((MulOpposite.unop c) ⊗ₜ[k] (MulOpposite.unop d)))
            exact ((congrArg (fun z : A ⊗[k] B => (a ⊗ₜ[k] b) * z)
              (Algebra.TensorProduct.tmul_mul_tmul xa (MulOpposite.unop c) yb (MulOpposite.unop d))).trans
                (Algebra.TensorProduct.tmul_mul_tmul a (xa * MulOpposite.unop c) b
                  (yb * MulOpposite.unop d))).symm

def barZeroLeftEquiv :
    ((ModuleCat.restrictScalars (tensorLeftInclusion k A Aᵐᵒᵖ)).obj
      (AbsoluteBar.moduleObject k A 0)) ≃ₗ[A] A where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' a x := by
    change a * ((show A from x) * 1) = a * (show A from x)
    rw [mul_one]

def barZeroRightEquiv :
    ((ModuleCat.restrictScalars (tensorRightInclusion k A Aᵐᵒᵖ)).obj
      (AbsoluteBar.moduleObject k A 0)) ≃ₗ[Aᵐᵒᵖ] Aᵐᵒᵖ where
  toFun x := MulOpposite.op (show A from x)
  invFun x := MulOpposite.unop x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' a x := by
    change MulOpposite.op (1 * ((show A from x) * MulOpposite.unop a)) =
      a * MulOpposite.op (show A from x)
    rw [one_mul]
    rfl

end ArExplicit

end

end OAI
