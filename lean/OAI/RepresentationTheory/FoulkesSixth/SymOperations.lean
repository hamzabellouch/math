import Mathlib
import OAI.RepresentationTheory.FoulkesSixth.SymDual

namespace OAI

noncomputable section

namespace Foulkes
universe u v
open scoped TensorProduct
open SymmetricTensor

variable {V : Type u} {W : Type v} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W]

def symEquiv (n : ℕ) (e : V ≃ₗ[ℂ] W) : Sym n V ≃ₗ[ℂ] Sym n W :=
  LinearEquiv.ofLinearMap (symMap n e.toLinearMap) (symMap n e.symm.toLinearMap)
    (by apply symMap_ext; intro v; simp)
    (by apply symMap_ext; intro v; simp)

@[simp] lemma symEquiv_apply (n : ℕ) (e : V ≃ₗ[ℂ] W) (x : Sym n V) :
    symEquiv n e x = symMap n e.toLinearMap x := rfl

namespace SymmetricTensor

def oneEquiv (V : Type u) [AddCommGroup V] [Module ℂ V] : Sym 1 V ≃ₗ[ℂ] V :=
  LinearEquiv.ofBijective
    ((PiTensorProduct.subsingletonEquiv (R := ℂ) (s := fun _ : Fin 1 => V) 0).toLinearMap.comp
      (symmetricTensors 1 V).subtype)
    ⟨(PiTensorProduct.subsingletonEquiv (R := ℂ) (s := fun _ : Fin 1 => V) 0).injective.comp
        Subtype.val_injective,
      fun v => ⟨power 1 V v, by simp [power]⟩⟩

@[simp] lemma oneEquiv_power (v : V) : oneEquiv V (power 1 V v) = v := by
  change PiTensorProduct.subsingletonEquiv (R := ℂ) (s := fun _ : Fin 1 => V) 0
    (PiTensorProduct.tprod ℂ (fun _ : Fin 1 => v)) = v
  simp

@[simp] lemma oneEquiv_symm (v : V) : (oneEquiv V).symm v = power 1 V v := by
  apply (oneEquiv V).injective
  simp

end SymmetricTensor

namespace SymAlgebra
variable {A : Type*} [CommRing A] [Algebra ℂ A]

def tensorMul (b : ℕ) (q : V →ₗ[ℂ] A) : T b V →ₗ[ℂ] A :=
  PiTensorProduct.lift ((MultilinearMap.mkPiAlgebra ℂ (Fin b) A).compLinearMap (fun _ => q))

@[simp] lemma tensorMul_tprod (b : ℕ) (q : V →ₗ[ℂ] A) (v : Fin b → V) :
    tensorMul b q (PiTensorProduct.tprod ℂ v) = ∏ i, q (v i) := by
  simp [tensorMul]

lemma tensorMul_perm (b : ℕ) (q : V →ₗ[ℂ] A) (σ : Equiv.Perm (Fin b)) (x : T b V) :
    tensorMul b q (perm b V σ x) = tensorMul b q x := by
  have h : (tensorMul b q).comp (perm b V σ).toLinearMap = tensorMul b q := by
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro v
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
      perm, PiTensorProduct.reindex_tprod, tensorMul_tprod]
    exact Equiv.prod_comp σ.symm (fun i => q (v i))
  exact DFunLike.congr_fun h x

def multiply (b : ℕ) (q : V →ₗ[ℂ] A) : Sym b V →ₗ[ℂ] A :=
  (tensorMul b q).comp (symmetricTensors b V).subtype

@[simp] lemma multiply_power (b : ℕ) (q : V →ₗ[ℂ] A) (v : V) :
    multiply b q (power b V v) = q v ^ b := by
  simp [multiply, power]

lemma multiply_project (b : ℕ) (q : V →ₗ[ℂ] A) (x : T b V) :
    multiply b q (project b V x) = tensorMul b q x := by
  change tensorMul b q (average b V x) = _
  simp only [average_apply, map_smul, map_sum, tensorMul_perm, Finset.sum_const,
    Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
  have hb : (b.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero b
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hb, one_smul]

end SymAlgebra
end Foulkes

end

end OAI
