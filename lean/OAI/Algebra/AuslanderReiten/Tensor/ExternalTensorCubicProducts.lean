import OAI.Algebra.AuslanderReiten.Ext.CubicExtCommute
import OAI.Algebra.AuslanderReiten.Tensor.ExternalTensorCubicExt
import OAI.Algebra.AuslanderReiten.Tensor.ExternalTensorCubicComm

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian
open scoped TensorProduct
namespace ArExplicit.ExternalTensor
universe u
variable (k A B : Type u) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
variable [CharP k 2]
variable [HasDerivedCategory (ModuleCat.{u} (A ⊗[k] B))]
attribute [local instance] moduleCatBaseModule moduleCatBaseTower
variable {X : ModuleCat.{u} A} {Y : ModuleCat.{u} B}
variable (P : ProjectiveResolution X) (Q : ProjectiveResolution Y)
variable [∀ n, Module.Finite A (P.complex.X n)] [∀ n, Module.Finite B (Q.complex.X n)]
variable (p : ∀ n, P.complex.X (n+3) ⟶ P.complex.X n)
variable (r : ∀ n, Q.complex.X (n+3) ⟶ Q.complex.X n)
variable (hp : ∀ n, p (n+1) ≫ P.complex.d (n+1) n = P.complex.d (n+4) (n+3) ≫ p n)
variable (hr : ∀ n, r (n+1) ≫ Q.complex.d (n+1) n = Q.complex.d (n+4) (n+3) ≫ r n)

theorem cubicExt_commute :
    (firstCubicExt k A B P Q p hp).comp (secondCubicExt k A B P Q r hr) rfl =
      (secondCubicExt k A B P Q r hr).comp (firstCubicExt k A B P Q p hp) rfl := by
  apply ResolutionProducts.cubic_endExt_commute (k := k)
    (projectiveResolution k A B P Q)
    (firstComparison k A B P Q p) (secondComparison k A B P Q r)
    (firstComparison_comm k A B P Q p hp) (secondComparison_comm k A B P Q r hr)
  apply ModuleCat.hom_ext
  exact (cubic_commute k A B P.complex Q.complex p r 0).symm

end ArExplicit.ExternalTensor

end

end OAI
