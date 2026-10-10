import OAI.GroupTheory.PolycyclicRecognition.Finiteness.IntegerInducedCochains
import OAI.GroupTheory.PolycyclicRecognition.Algebra.TwistedBilateralSequence

namespace OAI

/-! # Injectivity and cokernel of translation minus identity on induced cohomology -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory CategoryTheory.Limits
open scoped MonoidAlgebra
attribute [local instance 2000] Rep.hV2
attribute [local instance 2000] Rep.instLinear
attribute [local instance 2100] Linear.homModule
attribute [local instance 2200] Finsupp.module

variable {G : Type} [Group G] (q : G →* Multiplicative ℤ)
  (t : G) (ht : q t = Multiplicative.ofAdd 1)
  (P : ProjectiveResolution (Rep.trivial ℤ q.ker ℤ))
  (hP : ∀ i, Module.Finite ℤ[q.ker] (P.complex.X i).ρ.asModule)

def inducedTranslationDifference := inducedTranslation ℤ q.ker t P - 𝟙 _

def inducedCohomologyDifference (i : ℕ) :=
  HomologicalComplex.homologyMap
    (repCochainPrecomp ℤ (inducedTranslationDifference q t P) (Rep.leftRegular ℤ G)) i

theorem integerInducedCohomologyIso_difference (i : ℕ) :
    inducedCohomologyDifference q t P i ≫
        (integerInducedCohomologyIso q t ht P hP i).hom =
      (integerInducedCohomologyIso q t ht P hP i).hom ≫
        ModuleCat.ofHom (twistedBilateralDifference ℤ _
          (conjugationCohomologyIso ℤ q.ker t P i).toLinearEquiv) := by
  have h := integerInducedCohomologyIso_translation q t ht P hP i
  rw [inducedCohomologyDifference, inducedTranslationDifference,
    repCochainPrecomp_sub, repCochainPrecomp_id, HomologicalComplex.homologyMap_sub,
    HomologicalComplex.homologyMap_id, Preadditive.sub_comp, Category.id_comp, h]
  change _ = (integerInducedCohomologyIso q t ht P hP i).hom ≫
    ((bilateralFunctorTranslation ℤ (Multiplicative.ofAdd 1)).app
      ((P.complex.linearYonedaObj ℤ (Rep.leftRegular ℤ q.ker)).homology i) ≫
      (moduleFinsuppFunctor ℤ ℤ).map (conjugationCohomologyIso ℤ q.ker t P i).hom - 𝟙 _)
  rw [Preadditive.comp_sub, Category.comp_id]

include ht hP in
theorem inducedCohomologyDifference_injective (i : ℕ) :
    Function.Injective (inducedCohomologyDifference q t P i).hom := by
  intro x y hxy
  apply (integerInducedCohomologyIso q t ht P hP i).toLinearEquiv.injective
  apply twistedBilateralDifference_injective ℤ _
    (conjugationCohomologyIso ℤ q.ker t P i).toLinearEquiv
  have h := integerInducedCohomologyIso_difference q t ht P hP i
  have hx := congrArg (fun f => f.hom x) h
  have hy := congrArg (fun f => f.hom y) h
  exact hx.symm.trans ((congrArg (integerInducedCohomologyIso q t ht P hP i).hom.hom hxy).trans hy)

def inducedCohomologyDifferenceCokernelIso (i : ℕ) :
    cokernel (inducedCohomologyDifference q t P i) ≅
      (P.complex.linearYonedaObj ℤ (Rep.leftRegular ℤ q.ker)).homology i :=
  cokernel.mapIso _ _
    (integerInducedCohomologyIso q t ht P hP i)
    (integerInducedCohomologyIso q t ht P hP i)
    (integerInducedCohomologyIso_difference q t ht P hP i) ≪≫
      twistedBilateralCokernelIso ℤ _ (conjugationCohomologyIso ℤ q.ker t P i).toLinearEquiv

end PolycyclicRecognition

end

end OAI
