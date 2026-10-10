import OAI.Algebra.AuslanderReiten.Algebras.TensorRadical
import Mathlib.RingTheory.TensorProduct.Pi
import Mathlib.RingTheory.Flat.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.RingTheory.Ideal.Quotient.Operations

namespace OAI

namespace ArExplicit

open TensorProduct

variable {k R : Type*} [Field k] [Ring R] [Algebra k R] [Module.Finite k R]
variable (E : Type*) [Field E] [Algebra k E]

theorem scalarExtension_radical_pow_ne_bot (n : ℕ) (hn : (Ring.jacobson R) ^ n ≠ ⊥) :
    (Ring.jacobson (E ⊗[k] R)) ^ n ≠ ⊥ := by
  let f : R →+* E ⊗[k] R :=
    (Algebra.TensorProduct.includeRight : R →ₐ[k] E ⊗[k] R).toRingHom
  apply radical_pow_ne_bot_of_injective f
    (Algebra.TensorProduct.includeRight_injective (algebraMap k E).injective) _ n hn
  intro x hx
  apply nilpotentIdeal_le_jacobson
    (rightTensorIdeal (k := k) (R := E) (Ring.jacobson R))
    (rightTensorIdeal_isNilpotent _ (finiteAlgebra_radical_isNilpotent (k := k)))
  exact tmul_mem_rightTensorIdeal _ 1 hx

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def scalarExtensionQuotientMap (f : R →ₐ[k] (ι → k)) :
    E ⊗[k] R →ₐ[E] (ι → E) :=
  (Algebra.TensorProduct.piScalarRight k E E ι).toAlgHom.comp
    (Algebra.TensorProduct.map (AlgHom.id E E) f)

omit [Module.Finite k R] in
theorem scalarExtensionQuotientMap_surjective (f : R →ₐ[k] (ι → k))
    (hf : Function.Surjective f) : Function.Surjective (scalarExtensionQuotientMap E f) :=
  (Algebra.TensorProduct.piScalarRight k E E ι).surjective.comp
    (Algebra.TensorProduct.map_surjective (AlgHom.id E E) f Function.surjective_id hf)

theorem scalarExtension_radical_eq_kernel (f : R →ₐ[k] (ι → k))
    (hf : Function.Surjective f) (hJ : Ring.jacobson R = RingHom.ker f) :
    Ring.jacobson (E ⊗[k] R) = RingHom.ker (scalarExtensionQuotientMap E f) := by
  have hnil : IsNilpotent (RingHom.ker f) := by
    rw [← hJ]
    exact finiteAlgebra_radical_isNilpotent (k := k)
  have hid : IsNilpotent (RingHom.ker (AlgHom.id k E)) := by
    refine ⟨1, ?_⟩
    rw [Submodule.pow_one]
    ext e
    rfl
  have ht : Ring.jacobson (E ⊗[k] (ι → k)) = ⊥ :=
    jacobson_eq_bot_of_equiv (Algebra.TensorProduct.piScalarRight k E E ι).toRingEquiv
      (field_pi_jacobson_eq_bot E ι)
  rw [tensor_radical_eq_kernel (AlgHom.id k E) f Function.surjective_id hf hid hnil ht]
  ext x
  change (Algebra.TensorProduct.map (AlgHom.id k E) f) x = 0 ↔
    (Algebra.TensorProduct.piScalarRight k E E ι)
      ((Algebra.TensorProduct.map (AlgHom.id E E) f) x) = 0
  have heq : (Algebra.TensorProduct.map (AlgHom.id k E) f) x =
      (Algebra.TensorProduct.map (AlgHom.id E E) f) x := by
    induction x with
    | tmul e r => rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  rw [heq]
  exact ⟨fun h => by rw [h, map_zero], fun h =>
    (Algebra.TensorProduct.piScalarRight k E E ι).injective (by simpa using h)⟩

noncomputable def scalarExtension_semisimpleQuotientEquiv (f : R →ₐ[k] (ι → k))
    (hf : Function.Surjective f) (hJ : Ring.jacobson R = RingHom.ker f) :
    (E ⊗[k] R ⧸ Ring.jacobson (E ⊗[k] R)) ≃ₐ[E] (ι → E) :=
  (Ideal.quotientEquivAlgOfEq E (scalarExtension_radical_eq_kernel E f hf hJ)).trans
    (Ideal.quotientKerAlgEquivOfSurjective (scalarExtensionQuotientMap_surjective E f hf))

end ArExplicit

end OAI
