import OAI.Algebra.AuslanderReiten.Tensor.ExternalTensorHomKunneth
import OAI.Algebra.AuslanderReiten.Tensor.ExternalTensorResolution
import OAI.Algebra.AuslanderReiten.HomComplex.HomCochainExt
import OAI.Algebra.AuslanderReiten.HomComplex.HomCochainScalar

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian HomologicalComplex
open scoped TensorProduct
open scoped ModuleCat.Algebra
namespace ArExplicit.ExternalTensor
universe u
variable (k R : Type u) [Field k] [Ring R] [Algebra k R]
attribute [local instance] moduleCatBaseModule moduleCatBaseTower

def homCochainNativeExtEquiv {X : ModuleCat.{u} R} (P : ProjectiveResolution X)
    (Y : Type u) [AddCommGroup Y] [Module R Y] [Module k Y] [IsScalarTower k R Y]
    (n : ℕ) : (homCochain k R P.complex Y).homology n ≃ₗ[k]
      Ext X (ModuleCat.of R Y) n :=
  (((homologyFunctor (ModuleCat.{u} k) (ComplexShape.up ℕ) n).mapIso
    (homCochainScalarIso k R P.complex Y)).toLinearEquiv).trans
      (homCochainExtEquiv k R (Y := ModuleCat.of R Y) P n)

variable (A B : Type u) [Ring A] [Ring B] [Algebra k A] [Algebra k B]
variable [Module.Finite k A] [Module.Finite k B]
variable {X : ModuleCat.{u} A} {Y : ModuleCat.{u} B}
variable (P : ProjectiveResolution X) (Q : ProjectiveResolution Y)
variable [∀ n, Module.Finite A (P.complex.X n)] [∀ n, Module.Finite B (Q.complex.X n)]
variable (U : ModuleCat.{u} A) (V : ModuleCat.{u} B)

def extKunnethEquiv (n : ℕ) :
    Ext (moduleObject k A B X Y) (moduleObject k A B U V) n ≃ₗ[k]
      (∀ p : Diagonal n, Ext X U p.val.1 ⊗[k] Ext Y V p.val.2) :=
  (homCochainNativeExtEquiv k (A ⊗[k] B) (projectiveResolution k A B P Q)
    (moduleObject k A B U V) n).symm.trans
    ((homKunnethEquiv k A B P.complex Q.complex U V n).trans
      ((DFinsupp.linearEquivFunOnFintype (R := k)).trans
        (LinearEquiv.piCongrRight fun p => TensorProduct.congr
          (homCochainExtEquiv k A (Y := U) P p.val.1)
          (homCochainExtEquiv k B (Y := V) Q p.val.2))))

end ArExplicit.ExternalTensor

end

end OAI
