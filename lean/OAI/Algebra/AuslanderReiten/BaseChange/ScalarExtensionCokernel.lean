import OAI.Algebra.AuslanderReiten.BaseChange.ScalarExtensionExact

namespace OAI

noncomputable section
open scoped TensorProduct
namespace ArExplicit
universe u v w
variable (k : Type u) [Field k] (E : Type v) [Field E] [Algebra k E]
  (R : Type w) [Ring R] [Algebra k R]
  {L M : Type w}
  [AddCommGroup L] [Module R L] [Module k L] [IsScalarTower k R L]
  [AddCommGroup M] [Module R M] [Module k M] [IsScalarTower k R M]

attribute [local instance] scalarExtensionModule

def scalarExtensionCokernelEquiv (d : L →ₗ[R] M) :
    ((E ⊗[k] M) ⧸ LinearMap.range (scalarExtensionMap k E R d)) ≃ₗ[E ⊗[k] R]
      (E ⊗[k] (M ⧸ LinearMap.range d)) :=
  (scalarExtensionMap_exact k E R d (LinearMap.range d).mkQ
    (LinearMap.exact_map_mkQ_range d)).linearEquivOfSurjective
      (scalarExtensionMap_surjective k E R _ (Submodule.mkQ_surjective _))

def scalarExtensionEquiv (e : L ≃ₗ[R] M) :
    (E ⊗[k] L) ≃ₗ[E ⊗[k] R] (E ⊗[k] M) :=
  LinearEquiv.ofLinearMap (scalarExtensionMap k E R e.toLinearMap)
    (scalarExtensionMap k E R e.symm.toLinearMap)
    (by rw [← scalarExtensionMap_comp]; simp)
    (by rw [← scalarExtensionMap_comp]; simp)

theorem scalarExtension_regular_smul (a b : E ⊗[k] R) :
    scalarExtensionRepresentation k E R R a b = a * b := by
  induction a using TensorProduct.inductionOn with
  | add a b ha hb => simp only [map_add, LinearMap.add_apply, add_mul, ha, hb]
  | tmul e r =>
    induction b using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add, mul_add, hx, hy]
    | tmul e' r' =>
      rw [Algebra.TensorProduct.tmul_mul_tmul]
      rfl

theorem scalarExtensionModule_eq_regular :
    scalarExtensionModule k E R R = (Semiring.toModule : Module (E ⊗[k] R) (E ⊗[k] R)) :=
  Module.ext' _ _ (scalarExtension_regular_smul k E R)

end ArExplicit

end

end OAI
