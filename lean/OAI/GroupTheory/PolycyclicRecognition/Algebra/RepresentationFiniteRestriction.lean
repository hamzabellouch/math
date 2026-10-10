import Mathlib.RepresentationTheory.Intertwining
import Mathlib.RingTheory.Finiteness.Basic

namespace OAI

/-! # Finite generation after pullback along a surjective group homomorphism -/

noncomputable section
namespace PolycyclicRecognition
open scoped MonoidAlgebra
variable {k G Q M : Type} [CommRing k] [Group G] [Group Q]
  [AddCommGroup M] [Module k M]

theorem finite_representation_pullback_iff (ρ : Representation k Q M)
    (f : G →* Q) (hf : Function.Surjective f) :
    Module.Finite k[G] (Representation.asModule (ρ.comp f)) ↔
      Module.Finite k[Q] ρ.asModule := by
  let σ : Representation k G M := ρ.comp f
  let e := σ.asModuleEquiv.trans ρ.asModuleEquiv.symm
  let rmap := MonoidAlgebra.mapDomainRingHom k f
  have he : ρ.asAlgebraHom.comp (MonoidAlgebra.mapDomainAlgHom k k f) =
      σ.asAlgebraHom := by
    apply MonoidAlgebra.algHom_ext
    · intro g
      simp only [AlgHom.comp_apply, MonoidAlgebra.mapDomainAlgHom_apply,
        MonoidAlgebra.mapDomain_single, Representation.asAlgebraHom_single_one]
      rfl
    · exact Subsingleton.elim _ _
  let F : σ.asModule →ₛₗ[rmap] ρ.asModule :=
    { toFun := e
      map_add' := e.map_add
      map_smul' := by
        intro a x
        apply ρ.asModuleEquiv.injective
        change σ.asAlgebraHom a (σ.asModuleEquiv x) =
          ρ.asAlgebraHom (MonoidAlgebra.mapDomain f a) (σ.asModuleEquiv x)
        exact (congrArg (fun F : Module.End k M => F (σ.asModuleEquiv x))
          (AlgHom.congr_fun he a)).symm }
  let : RingHomSurjective rmap := ⟨by
    intro a
    obtain ⟨b, hb⟩ := Finsupp.mapDomain_surjective hf a.coeff
    refine ⟨MonoidAlgebra.ofCoeff b, ?_⟩
    exact MonoidAlgebra.coeff_injective hb⟩
  exact LinearMap.finite_iff_of_bijective F e.bijective

end PolycyclicRecognition

end

end OAI
