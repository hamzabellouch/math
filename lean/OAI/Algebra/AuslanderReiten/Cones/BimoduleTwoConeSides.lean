import OAI.Algebra.AuslanderReiten.Cones.BimoduleTwoConeExact
import OAI.Algebra.AuslanderReiten.Bar.BarTensorRegular
import OAI.Algebra.AuslanderReiten.Cones.TwoConeBaseRestriction

namespace OAI

noncomputable section
namespace ArExplicit.T
open CategoryTheory
open scoped TensorProduct
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k)
attribute [local instance 2000] moduleCatBaseModule moduleCatBaseTower
attribute [local instance 2001] Semiring.toNonAssocSemiring
local notation "R" => T k q
local notation "A₀" => R ⊗[k] R
local notation "Ae" => ExternalTensor.EnvelopingProduct k R R
local notation "D" => bimoduleTwoConeData q

private def productBaseTyped : TwoCone.BaseCokernel (productTwoConeData q) 0 ≃ₗ[
    AbsoluteBar.Enveloping k R ⊗[k] AbsoluteBar.Enveloping k R]
    ExternalTensor.moduleObject k (AbsoluteBar.Enveloping k R) (AbsoluteBar.Enveloping k R)
      (AbsoluteBar.moduleObject k R 0) (AbsoluteBar.moduleObject k R 0) :=
  productBaseCokernelEquiv q

private def baseQuotientRestriction : TwoCone.BaseCokernel D 0 ≃ₗ[Ae]
    (ExternalTensor.envelopingFunctor k R R).obj
      (ModuleCat.of (ExternalTensor.ProductEnveloping k R R)
        (TwoCone.BaseCokernel (productTwoConeData q) 0)) := by
  unfold bimoduleTwoConeData
  convert! (TwoCone.baseCokernelRestrictionEquiv (ExternalTensor.envelopingEquiv k R R).symm.toRingHom
    (productTwoConeData q) 0).symm using 1

private def productBaseRestricted := Iso.toLinearEquiv
  ((ExternalTensor.envelopingFunctor k R R).mapIso (productBaseTyped q).toModuleIso)

private def baseToTensorRegular := (baseQuotientRestriction q).trans (productBaseRestricted q)

def bimoduleBaseCokernelEquiv : TwoCone.BaseCokernel D 0 ≃ₗ[Ae] AbsoluteBar.moduleObject k A₀ 0 :=
  (baseToTensorRegular q).trans (barTensorZeroEquiv k R R)

def baseLeftEquiv :
    TwoCone.BaseCokernel ((D).restrict (tensorLeftInclusion k A₀ A₀ᵐᵒᵖ)) 0 ≃ₗ[A₀] A₀ :=
  TwoCone.baseCokernelTransport (tensorLeftInclusion k A₀ A₀ᵐᵒᵖ) D 0
    (N := ModuleCat.of A₀ A₀) (bimoduleBaseCokernelEquiv q) (barZeroLeftEquiv k A₀)

def baseRightEquiv :
    TwoCone.BaseCokernel ((D).restrict (tensorRightInclusion k A₀ A₀ᵐᵒᵖ)) 0 ≃ₗ[A₀ᵐᵒᵖ] A₀ᵐᵒᵖ :=
  TwoCone.baseCokernelTransport (tensorRightInclusion k A₀ A₀ᵐᵒᵖ) D 0
    (N := ModuleCat.of A₀ᵐᵒᵖ A₀ᵐᵒᵖ) (bimoduleBaseCokernelEquiv q) (barZeroRightEquiv k A₀)

theorem baseTerm_left_projective (n : ℕ) :
    Module.Projective A₀ (((D).restrict (tensorLeftInclusion k A₀ A₀ᵐᵒᵖ)).term n) := by
  let := bimodule_term_finite q n
  let := bimodule_term_projective q n
  let := tensorLeftRegular_projective k A₀ A₀ᵐᵒᵖ
  exact restrict_projective (tensorLeftInclusion k A₀ A₀ᵐᵒᵖ) ((D).term n)

theorem baseTerm_right_projective (n : ℕ) :
    Module.Projective A₀ᵐᵒᵖ (((D).restrict (tensorRightInclusion k A₀ A₀ᵐᵒᵖ)).term n) := by
  let := bimodule_term_finite q n
  let := bimodule_term_projective q n
  let := tensorRightRegular_projective k A₀ A₀ᵐᵒᵖ
  exact restrict_projective (tensorRightInclusion k A₀ A₀ᵐᵒᵖ) ((D).term n)

theorem firstTail_left_projective :
    Module.Projective A₀ ((ModuleCat.restrictScalars (tensorLeftInclusion k A₀ A₀ᵐᵒᵖ)).obj
      (ModuleCat.of Ae (firstTail q))) := by
  let : Module.Projective A₀
      (TwoCone.BaseCokernel ((D).restrict (tensorLeftInclusion k A₀ A₀ᵐᵒᵖ)) 0) :=
    Module.Projective.of_equiv (baseLeftEquiv q).symm
  exact TwoCone.C₁_side_projective (tensorLeftInclusion k A₀ A₀ᵐᵒᵖ) D
    (bimodule_exact q) (baseTerm_left_projective q)

theorem firstTail_right_projective :
    Module.Projective A₀ᵐᵒᵖ ((ModuleCat.restrictScalars (tensorRightInclusion k A₀ A₀ᵐᵒᵖ)).obj
      (ModuleCat.of Ae (firstTail q))) := by
  let : Module.Projective A₀ᵐᵒᵖ
      (TwoCone.BaseCokernel ((D).restrict (tensorRightInclusion k A₀ A₀ᵐᵒᵖ)) 0) :=
    Module.Projective.of_equiv (baseRightEquiv q).symm
  exact TwoCone.C₁_side_projective (tensorRightInclusion k A₀ A₀ᵐᵒᵖ) D
    (bimodule_exact q) (baseTerm_right_projective q)

theorem firstTail_left_finite :
    Module.Finite A₀ ((ModuleCat.restrictScalars (tensorLeftInclusion k A₀ A₀ᵐᵒᵖ)).obj
      (ModuleCat.of Ae (firstTail q))) := by
  let := firstTail_finite q
  let := tensorLeftRegular_finite k A₀ A₀ᵐᵒᵖ
  exact restrict_finite (tensorLeftInclusion k A₀ A₀ᵐᵒᵖ) (ModuleCat.of Ae (firstTail q))

theorem firstTail_right_finite :
    Module.Finite A₀ᵐᵒᵖ ((ModuleCat.restrictScalars (tensorRightInclusion k A₀ A₀ᵐᵒᵖ)).obj
      (ModuleCat.of Ae (firstTail q))) := by
  let := firstTail_finite q
  let := tensorRightRegular_finite k A₀ A₀ᵐᵒᵖ
  exact restrict_finite (tensorRightInclusion k A₀ A₀ᵐᵒᵖ) (ModuleCat.of Ae (firstTail q))

end ArExplicit.T

end

end OAI
