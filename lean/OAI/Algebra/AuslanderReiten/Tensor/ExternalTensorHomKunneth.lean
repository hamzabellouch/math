import OAI.Algebra.AuslanderReiten.Tensor.ExternalTensorHomDifferential
import OAI.Algebra.AuslanderReiten.Homology.VectorCochainKunneth

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped TensorProduct
namespace ArExplicit.ExternalTensor
universe u
variable (k A B : Type u) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
attribute [local instance] moduleCatBaseModule moduleCatBaseTower
variable (P : ChainComplex (ModuleCat.{u} A) ℕ) (Q : ChainComplex (ModuleCat.{u} B) ℕ)
variable (U : ModuleCat.{u} A) (V : ModuleCat.{u} B)
variable [∀ n, Module.Finite A (P.X n)] [∀ n, Module.Projective A (P.X n)]
variable [∀ n, Module.Finite B (Q.X n)] [∀ n, Module.Projective B (Q.X n)]

def homKunnethEquiv (n : ℕ) :
    (homCochain k (A ⊗[k] B) (complex k A B P Q) (moduleObject k A B U V)).homology n ≃ₗ[k]
      (Π₀ p : Diagonal n,
        ((homCochain k A P U).homology p.val.1 ⊗[k] (homCochain k B Q V).homology p.val.2)) :=
  (((homologyFunctor (ModuleCat.{u} k) (ComplexShape.up ℕ) n).mapIso
    (homCochainTotalIso k A B P Q U V)).symm.toLinearEquiv).trans
      (VectorCochain.kunnethLinearEquiv k (MonoidalCategory.curriedTensor (ModuleCat.{u} k))
        (homCochain k A P U) (homCochain k B Q V) n)

end ArExplicit.ExternalTensor

end

end OAI
