import OAI.Algebra.AuslanderReiten.Complete.CompleteTailFunctor
import OAI.Algebra.AuslanderReiten.Resolutions.ResolutionEndpointIso
import OAI.Algebra.AuslanderReiten.Resolutions.MapResolutionExtMk

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace ArExplicit.CompleteComparison
universe u
variable {R S : Type u} [Ring R] [Ring S]
variable (F : ModuleCat.{u} R ⥤ ModuleCat.{u} S) [F.Additive]
variable (K : CochainComplex (ModuleCat.{u} R) ℤ)

def tailFunctorIso : nonnegativeTail (chainOfCochain (functorComplex F K)) ≅
    (F.mapHomologicalComplex (.down ℕ)).obj (nonnegativeTail (chainOfCochain K)) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => tailTermIso (functorComplex F K) n ≪≫ (F.mapIso (tailTermIso K n)).symm)
    (fun i j _ => (tailFunctorHom F K).comm i j)

@[simp] theorem tailFunctorIso_hom : (tailFunctorIso F K).hom = tailFunctorHom F K := rfl

variable [PreservesFiniteLimits F] [PreservesFiniteColimits F] [F.PreservesProjectiveObjects]
variable (hK : TotallyAcyclicComplex (chainOfCochain K))
variable (hFK : TotallyAcyclicComplex (chainOfCochain (functorComplex F K)))

def completeFunctorEndpointIso :
    ModuleCat.of S (Cokernel (chainOfCochain (functorComplex F K)) 0) ≅
      F.obj (ModuleCat.of R (Cokernel (chainOfCochain K) 0)) :=
  ResolutionProducts.resolutionEndpointIso (completeExtResolution hFK)
    (ResolutionProducts.mapResolution F (completeExtResolution hK)) (tailFunctorIso F K)

theorem completeFunctorEndpointIso_augmentation :
    (tailFunctorHom F K).f 0 ≫ F.map ((completeExtResolution hK).π.f 0) =
      (completeExtResolution hFK).π.f 0 ≫ (completeFunctorEndpointIso F K hK hFK).hom := by
  have h := ResolutionProducts.resolutionEndpointIso_augmentation (completeExtResolution hFK)
    (ResolutionProducts.mapResolution F (completeExtResolution hK)) (tailFunctorIso F K)
  erw [ResolutionProducts.mapResolution_π_zero] at h
  rw [tailFunctorIso_hom] at h
  exact h.symm

end ArExplicit.CompleteComparison

end

end OAI
