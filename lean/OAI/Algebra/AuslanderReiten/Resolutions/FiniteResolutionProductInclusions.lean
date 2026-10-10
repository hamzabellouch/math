import OAI.Algebra.AuslanderReiten.Resolutions.FiniteResolutionProduct

namespace OAI

noncomputable section
namespace ArExplicit.FiniteLeftModule
open CategoryTheory CategoryTheory.Limits
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R] [Module.Finite k R]
variable (τ : FrobeniusTrace k R) (M N : FiniteLeftModule k R)
local notation "Q" => HomotopyCategory.quotient (ModuleCat R) (ComplexShape.up ℤ)

theorem resolutionPairInl :
    (Q).map (resolutionMap (M := M) (N := pairModule M N) τ (pairInl M N)) ≫
      (resolutionPairIso τ M N).hom = biprod.inl := by
  apply biprod.hom_ext
  · rw [Category.assoc, resolutionPairIso_hom_fst, biprod.inl_fst]
    exact (resolutionPairBicone τ M N).inl_fst
  · rw [Category.assoc, resolutionPairIso_hom_snd, biprod.inl_snd]
    exact (resolutionPairBicone τ M N).inl_snd

theorem resolutionPairInr :
    (Q).map (resolutionMap (M := N) (N := pairModule M N) τ (pairInr M N)) ≫
      (resolutionPairIso τ M N).hom = biprod.inr := by
  apply biprod.hom_ext
  · rw [Category.assoc, resolutionPairIso_hom_fst, biprod.inr_fst]
    exact (resolutionPairBicone τ M N).inr_fst
  · rw [Category.assoc, resolutionPairIso_hom_snd, biprod.inr_snd]
    exact (resolutionPairBicone τ M N).inr_snd

end ArExplicit.FiniteLeftModule

end

end OAI
