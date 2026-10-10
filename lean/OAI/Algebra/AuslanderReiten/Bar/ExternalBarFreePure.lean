import OAI.Algebra.AuslanderReiten.Ext.ExternalEvaluationPure
import OAI.Algebra.AuslanderReiten.Bar.ExternalBarFreeCoordinate

namespace OAI

noncomputable section
namespace ArExplicit.ExternalBalanced
open CategoryTheory
open scoped TensorProduct
universe u
variable (k A B M N : Type u) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
variable [AddCommGroup M] [AddCommGroup N] [Module A M] [Module B N]
variable [Module k M] [Module k N] [IsScalarTower k A M] [IsScalarTower k B N]
variable (e : M ≃ₗ[k] k) (f : N ≃ₗ[k] k)
attribute [local instance 2000] moduleCatBaseModule moduleCatBaseTower
variable (K : ModuleCat.{u} (A ⊗[k] Aᵐᵒᵖ)) (L : ModuleCat.{u} (B ⊗[k] Bᵐᵒᵖ))
variable (X : ModuleCat.{u} A) (Y : ModuleCat.{u} B)
variable (g : (EnvelopingBimodule.evaluationFunctor k A X).obj K ⟶ ModuleBar.moduleObject k A M 1)
  (h : (EnvelopingBimodule.evaluationFunctor k B Y).obj L ⟶ ModuleBar.moduleObject k B N 1)

theorem postShuffle_barFree_pure (a : EnvelopingBimodule k A K)
    (b : EnvelopingBimodule k B L) (x : X) (y : Y) :
    ((shuffle k A B K L X Y).toModuleIso.hom ≫ ExternalTensor.mapHom k A B g h ≫
      ExternalTensor.barFreeCoordinate k A B M N e f)
      (BalancedTensor.tmul
        ((bimoduleCoordinates k A B K L).symm (a ⊗ₜ[k] b))
        ((ExternalTensor.moduleScalarCoordinates k A B X Y).symm (x ⊗ₜ[k] y))) =
      ((g ≫ (ModuleBar.freeCoordinate k A M e).toModuleIso.hom) (BalancedTensor.tmul a x)) ⊗ₜ[k]
        ((h ≫ (ModuleBar.freeCoordinate k B N f).toModuleIso.hom) (BalancedTensor.tmul b y)) :=
  (postShuffle_pure k A B K L X Y (ModuleBar.moduleObject k A M 1)
    (ModuleBar.moduleObject k B N 1) (ModuleCat.of (A ⊗[k] B) (A ⊗[k] B)) g h
    (ExternalTensor.barFreeCoordinate k A B M N e f) a b x y).trans
      (ExternalTensor.barFreeCoordinate_tmul k A B M N e f
        (g (BalancedTensor.tmul a x)) (h (BalancedTensor.tmul b y)))

theorem postShuffle_barFree_values (a : EnvelopingBimodule k A K)
    (b : EnvelopingBimodule k B L) (x : X) (y : Y) (r : A) (s : B)
    (hg : (g ≫ (ModuleBar.freeCoordinate k A M e).toModuleIso.hom)
      (BalancedTensor.tmul a x) = r)
    (hh : (h ≫ (ModuleBar.freeCoordinate k B N f).toModuleIso.hom)
      (BalancedTensor.tmul b y) = s) :
    ((shuffle k A B K L X Y).toModuleIso.hom ≫ ExternalTensor.mapHom k A B g h ≫
      ExternalTensor.barFreeCoordinate k A B M N e f)
      (BalancedTensor.tmul
        ((bimoduleCoordinates k A B K L).symm (a ⊗ₜ[k] b))
        ((ExternalTensor.moduleScalarCoordinates k A B X Y).symm (x ⊗ₜ[k] y))) =
      r ⊗ₜ[k] s := by
  rw [postShuffle_barFree_pure, hg, hh]

end ArExplicit.ExternalBalanced

end

end OAI
