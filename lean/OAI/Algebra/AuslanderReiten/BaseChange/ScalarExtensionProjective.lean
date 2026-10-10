import OAI.Algebra.AuslanderReiten.BaseChange.ScalarExtensionExact
import Mathlib.Algebra.Module.Projective
import Mathlib.RingTheory.Finiteness.Cardinality
import Mathlib.LinearAlgebra.TensorProduct.Pi

namespace OAI

noncomputable section
open scoped TensorProduct
namespace ArExplicit
universe u v w

variable (k : Type u) [Field k] (E : Type v) [Field E] [Algebra k E]
  (R : Type w) [Ring R] [Algebra k R]

attribute [local instance] scalarExtensionModule

def scalarExtensionPi (n : ℕ) :
    (E ⊗[k] (Fin n → R)) ≃ₗ[E ⊗[k] R] (Fin n → E ⊗[k] R) where
  __ := (TensorProduct.piRight k E E (fun _ : Fin n => R)).toAddEquiv
  map_smul' a x := by
    change TensorProduct.piRight k E E (fun _ : Fin n => R) (a • x) =
      a • TensorProduct.piRight k E E (fun _ : Fin n => R) x
    induction a using TensorProduct.inductionOn with
    | add a b ha hb => simp only [add_smul, map_add, ha, hb]
    | tmul e r =>
      induction x using TensorProduct.inductionOn with
      | add x y hx hy => simp only [smul_add, map_add, hx, hy]
      | tmul e' f =>
        ext i
        simp only [scalarExtension_smul_tmul, TensorProduct.piRight_apply,
          TensorProduct.piRightHom_tmul, Pi.smul_apply, smul_eq_mul,
          Algebra.TensorProduct.tmul_mul_tmul]

variable (M : Type w) [AddCommGroup M] [Module R M] [Module k M]
  [IsScalarTower k R M]

theorem scalarExtension_finite [Module.Finite R M] :
    Module.Finite (E ⊗[k] R) (E ⊗[k] M) := by
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' R M
  let e := scalarExtensionPi k E R n
  exact Module.Finite.of_surjective
    ((scalarExtensionMap k E R f).comp e.symm.toLinearMap)
    ((scalarExtensionMap_surjective k E R f hf).comp e.symm.surjective)

theorem scalarExtension_projective [Module.Finite R M] [Module.Projective R M] :
    Module.Projective (E ⊗[k] R) (E ⊗[k] M) := by
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' R M
  obtain ⟨s, hs⟩ := Module.projective_lifting_property f (LinearMap.id : M →ₗ[R] M) hf
  let e := scalarExtensionPi k E R n
  let i := e.toLinearMap.comp (scalarExtensionMap k E R s)
  let p := (scalarExtensionMap k E R f).comp e.symm.toLinearMap
  apply Module.Projective.of_split i p
  ext x
  change scalarExtensionMap k E R f
    (e.symm (e (scalarExtensionMap k E R s x))) = x
  rw [e.symm_apply_apply]
  change ((scalarExtensionMap k E R f).comp (scalarExtensionMap k E R s)) x = x
  rw [← scalarExtensionMap_comp, hs, scalarExtensionMap_id]
  rfl

end ArExplicit

end

end OAI
