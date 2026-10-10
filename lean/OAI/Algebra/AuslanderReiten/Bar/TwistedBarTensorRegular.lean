import OAI.Algebra.AuslanderReiten.Bar.BarTensorRegular
import OAI.Algebra.AuslanderReiten.Bar.TwistedBar
import OAI.Algebra.AuslanderReiten.Modules.BimoduleEnveloping

namespace OAI

noncomputable section
namespace ArExplicit
open CategoryTheory
open scoped TensorProduct
universe u
variable (k A B : Type u) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
attribute [local instance 2000] moduleCatBaseModule moduleCatBaseTower

def twistedBarZeroScalarEquiv (h : A ≃ₐ[k] A) : AbsoluteBar.twistedObject k A h 0 ≃ₗ[k] A where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' a x := by
    change ((AbsoluteBar.representation k A 0).comp (AbsoluteBar.twistEnveloping k A h).toAlgHom)
      (algebraMap k (AbsoluteBar.Enveloping k A) a) (show A from x) = a • (show A from x)
    rw [AlgHom.commutes]
    rfl

def twistedBarTensorZeroEquiv (hA : A ≃ₐ[k] A) (hB : B ≃ₐ[k] B) :
    ExternalTensor.envelopingObject k A B
      (ExternalTensor.moduleObject k (AbsoluteBar.Enveloping k A) (AbsoluteBar.Enveloping k B)
        (AbsoluteBar.twistedObject k A hA 0) (AbsoluteBar.twistedObject k B hB 0)) ≃ₗ[
          ExternalTensor.EnvelopingProduct k A B]
      AbsoluteBar.twistedObject k (A ⊗[k] B) (Algebra.TensorProduct.congr hA hB) 0 where
  __ := (TensorProduct.congr (twistedBarZeroScalarEquiv k A hA)
    (twistedBarZeroScalarEquiv k B hB)).toAddEquiv
  map_smul' a x := by
    let z : (AbsoluteBar.twistedObject k A hA 0) ⊗[k] (AbsoluteBar.twistedObject k B hB 0) := x
    let e := TensorProduct.congr (twistedBarZeroScalarEquiv k A hA) (twistedBarZeroScalarEquiv k B hB)
    change e (ExternalTensor.representation k (AbsoluteBar.Enveloping k A) (AbsoluteBar.Enveloping k B)
      (AbsoluteBar.twistedObject k A hA 0) (AbsoluteBar.twistedObject k B hB 0)
        ((ExternalTensor.envelopingEquiv k A B).symm a) z) =
      ((AbsoluteBar.representation k (A ⊗[k] B) 0).comp
        (AbsoluteBar.twistEnveloping k (A ⊗[k] B) (Algebra.TensorProduct.congr hA hB)).toAlgHom) a (e z)
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
            change (a * (xa * hA (MulOpposite.unop c))) ⊗ₜ[k]
              (b * (yb * hB (MulOpposite.unop d))) =
              (a ⊗ₜ[k] b) * ((xa ⊗ₜ[k] yb) *
                ((hA (MulOpposite.unop c)) ⊗ₜ[k] (hB (MulOpposite.unop d))))
            exact ((congrArg (fun z : A ⊗[k] B => (a ⊗ₜ[k] b) * z)
              (Algebra.TensorProduct.tmul_mul_tmul xa (hA (MulOpposite.unop c)) yb
                (hB (MulOpposite.unop d)))).trans
                (Algebra.TensorProduct.tmul_mul_tmul a (xa * hA (MulOpposite.unop c)) b
                  (yb * hB (MulOpposite.unop d)))).symm

def twistedBarZeroBimoduleEquiv (h : A ≃ₐ[k] A) : AbsoluteBar.twistedObject k A h 0 ≃ₗ[
    AbsoluteBar.Enveloping k A] bimoduleEnvelopingObject k A (TwistedBimodule k A h) where
  toFun x := ⟨x⟩
  invFun x := x.value
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' a x := by
    apply TwistedBimodule.ext
    change (((AbsoluteBar.representation k A 0).comp (AbsoluteBar.twistEnveloping k A h).toAlgHom) a)
      (show A from x) = (bimoduleEnvelopingRepresentation k A (TwistedBimodule k A h) a ⟨x⟩).value
    induction a using TensorProduct.inductionOn with
    | add a b ha hb =>
      simp only [map_add]
      change (((AbsoluteBar.representation k A 0).comp (AbsoluteBar.twistEnveloping k A h).toAlgHom) a) x +
          (((AbsoluteBar.representation k A 0).comp (AbsoluteBar.twistEnveloping k A h).toAlgHom) b) x = _
      rw [ha, hb]
      rfl
    | tmul a b => rfl

def twistedBarTensorBimoduleEquiv (hA : A ≃ₐ[k] A) (hB : B ≃ₐ[k] B) :
    ExternalTensor.envelopingObject k A B
      (ExternalTensor.moduleObject k (AbsoluteBar.Enveloping k A) (AbsoluteBar.Enveloping k B)
        (AbsoluteBar.twistedObject k A hA 0) (AbsoluteBar.twistedObject k B hB 0)) ≃ₗ[
          ExternalTensor.EnvelopingProduct k A B]
      bimoduleEnvelopingObject k (A ⊗[k] B)
        (TwistedBimodule k (A ⊗[k] B) (Algebra.TensorProduct.congr hA hB)) :=
  (twistedBarTensorZeroEquiv k A B hA hB).trans
    (twistedBarZeroBimoduleEquiv k (A ⊗[k] B) (Algebra.TensorProduct.congr hA hB))

end ArExplicit

end

end OAI
