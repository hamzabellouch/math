import OAI.Algebra.Finitistic.Ordinary.OrdinaryResolutionQuasiIso
import OAI.Algebra.Finitistic.Ordinary.OrdinaryTensorIdealActions
import Mathlib.RingTheory.Flat.Basic

namespace OAI
noncomputable section
open CategoryTheory
open scoped TensorProduct
namespace LittleFinitistic.OrdinarySimulation
universe u
variable (k B : Type u) [Field k] [Ring B] [Algebra k B] (l : ℕ)
namespace TensorResolution
open ChainAlgebra

abbrev term (n : ℕ) := IdempotentTensor.rightIdeal
  (TensorIdeal.vertex (k := k) (B := B) (extendedVertex k l n))

def termEquiv (n : ℕ) : B ⊗[k] resolutionIdeal k l n ≃ₗ[k] term k B l n :=
  TensorIdeal.equivalence _ (extendedVertex_idempotent k l n)

def regularEquiv : (B ⊗[k] ChainAlgebra k l)ᵐᵒᵖ ≃ₗ[(B ⊗[k] ChainAlgebra k l)ᵐᵒᵖ]
    B ⊗[k] ChainAlgebra k l where
  toFun := MulOpposite.unop
  invFun := MulOpposite.op
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def leftMultiply (x : B ⊗[k] ChainAlgebra k l) :
    B ⊗[k] ChainAlgebra k l →ₗ[(B ⊗[k] ChainAlgebra k l)ᵐᵒᵖ] B ⊗[k] ChainAlgebra k l where
  toFun y := x*y
  map_add' := mul_add x
  map_smul' r y := (mul_assoc x y r.unop).symm

def retract (n : ℕ) : B ⊗[k] ChainAlgebra k l →ₗ[(B ⊗[k] ChainAlgebra k l)ᵐᵒᵖ] term k B l n :=
  (leftMultiply k B l (TensorIdeal.vertex (k := k) (B := B) (extendedVertex k l n))).codRestrict _ (fun x => by
    change _ * (_ * x) = _ * x
    rw [← mul_assoc, TensorIdeal.vertex_idempotent _ (extendedVertex_idempotent k l n)])

instance term_projective (n : ℕ) : Module.Projective (B ⊗[k] ChainAlgebra k l)ᵐᵒᵖ (term k B l n) := by
  let : Module.Projective (B ⊗[k] ChainAlgebra k l)ᵐᵒᵖ (B ⊗[k] ChainAlgebra k l) :=
    Module.Projective.of_equiv (regularEquiv k B l)
  apply Module.Projective.of_split (term k B l n).subtype (retract k B l n)
  ext x
  exact x.property

/-- The B-extended resolution differential is left multiplication by 1 tensor c. -/
def differential (n : ℕ) : term k B l n →ₗ[(B ⊗[k] ChainAlgebra k l)ᵐᵒᵖ] term k B l (n+1) :=
  ((leftMultiply k B l ((1:B) ⊗ₜ[k] extendedArrow k l n)).comp (term k B l n).subtype).codRestrict _ (fun x => by
    change TensorIdeal.vertex (k := k) (B := B) (extendedVertex k l (n+1)) *
      (((1:B) ⊗ₜ[k] extendedArrow k l n) * x.val) = ((1:B) ⊗ₜ[k] extendedArrow k l n) * x.val
    rw [← mul_assoc]
    congr 1
    simp only [TensorIdeal.vertex,Algebra.TensorProduct.tmul_mul_tmul,one_mul,extendedArrow_target])

theorem differential_square (n : ℕ) : (differential k B l (n+1)).comp (differential k B l n) = 0 := by
  ext x
  change ((1:B) ⊗ₜ[k] extendedArrow k l (n+1)) * (((1:B) ⊗ₜ[k] extendedArrow k l n) * x.val) = 0
  rw [← mul_assoc,Algebra.TensorProduct.tmul_mul_tmul,extendedArrow_square,TensorProduct.tmul_zero,zero_mul]

theorem termEquiv_d (n : ℕ) (z : B ⊗[k] resolutionIdeal k l n) :
    termEquiv k B l (n+1) (((resolutionDifferential k l n).hom.restrictScalars k).lTensor B z) =
      differential k B l n (termEquiv k B l n z) := by
  induction z using TensorProduct.inductionOn with
  | tmul b c =>
    apply Subtype.ext
    change b ⊗ₜ[k] (extendedArrow k l n * c.val) =
      ((1:B) ⊗ₜ[k] extendedArrow k l n) * (b ⊗ₜ[k] c.val)
    rw [Algebra.TensorProduct.tmul_mul_tmul,one_mul]
  | add x y hx hy => simp only [map_add,hx,hy]

/-- Every interior exact sequence stays exact after the actual B-extension over k. -/
theorem differential_exact (n : ℕ) (hn : n+1 < l) :
    Function.Exact (differential k B l n) (differential k B l (n+1)) := by
  have hc : Function.Exact ((resolutionDifferential k l n).hom.restrictScalars k)
      ((resolutionDifferential k l (n+1)).hom.restrictScalars k) := by
    intro x
    constructor
    · intro hx
      exact (ShortComplex.moduleCat_exact_iff _).mp (supported_complex_exact k l n hn) x hx
    · rintro ⟨y,rfl⟩
      have h := congrArg (fun f => f.hom y) (resolutionDifferential_square k l n)
      exact h
  have ht := Module.Flat.lTensor_exact B hc
  intro x
  constructor
  · intro hx
    have hzero : (((resolutionDifferential k l (n+1)).hom.restrictScalars k).lTensor B)
        ((termEquiv k B l (n+1)).symm x) = 0 := by
      apply (termEquiv k B l (n+2)).injective
      rw [termEquiv_d,LinearEquiv.apply_symm_apply,hx,map_zero]
    obtain ⟨y,hy⟩ := (ht _).mp hzero
    refine ⟨termEquiv k B l n y, ?_⟩
    rw [← termEquiv_d,hy,LinearEquiv.apply_symm_apply]
  · rintro ⟨y,rfl⟩
    exact congrArg (fun f => f y) (differential_square k B l n)
end TensorResolution
end LittleFinitistic.OrdinarySimulation

end

end OAI
