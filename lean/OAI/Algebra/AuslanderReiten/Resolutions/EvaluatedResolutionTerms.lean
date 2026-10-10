import OAI.Algebra.AuslanderReiten.Resolutions.EvaluatedOrdinaryResolution

namespace OAI

noncomputable section
namespace ArExplicit.TwoCone
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R]
variable (D : Data (R ⊗[k] Rᵐᵒᵖ)) (hf : ∀ n, Module.Finite k (D.term n))
variable (X : FiniteLeftModule k R)
variable (hex : ∀ n, Function.Exact (D.d (n+1)) (D.d n))
variable (hr : ∀ n, Module.Projective Rᵐᵒᵖ
  (EnvelopingBimodule k R (baseCokernelModule D hf n).carrier))
variable (hp : ∀ n, Module.Projective (R ⊗[k] Rᵐᵒᵖ) (D.term n))

def evaluatedResolutionTermIso (n : ℕ) :
    (evaluatedOrdinaryResolution D hf X hex hr hp).complex.X n ≅ evaluatedRawTerm D hf X n :=
  Iso.refl _

@[simp] theorem evaluatedResolutionTermIso_inv_apply (n : ℕ) (x : evaluatedRawTerm D hf X n) :
    (evaluatedResolutionTermIso D hf X hex hr hp n).inv x = x := rfl

theorem evaluatedResolutionTermIso_augmentation :
    (evaluatedResolutionTermIso D hf X hex hr hp 0).inv ≫
      (evaluatedOrdinaryResolution D hf X hex hr hp).π.f 0 =
        ModuleCat.ofHom (evaluatedBaseQuotient D hf X 0) := by
  change 𝟙 _ ≫ (evaluatedOrdinaryAugmentation D hf X).f 0 = _
  rw [Category.id_comp, evaluatedOrdinaryAugmentation_zero]

end ArExplicit.TwoCone

end

end OAI
