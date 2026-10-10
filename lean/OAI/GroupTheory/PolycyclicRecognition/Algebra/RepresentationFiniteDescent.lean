import OAI.GroupTheory.PolycyclicRecognition.Algebra.PositiveCharacterIdeal
import Mathlib.RingTheory.Finiteness.Basic

namespace OAI

/-! # Descending finite module generation to the quotient action -/

noncomputable section
namespace PolycyclicRecognition
open scoped MonoidAlgebra
variable {G Q M : Type} [Monoid G] [Monoid Q] [AddCommGroup M]

theorem finite_representation_of_comp (ρ : Representation ℤ Q M) (f : G →* Q)
    [Module.Finite ℤ[G] (Representation.asModule (ρ.comp f))] :
    Module.Finite ℤ[Q] ρ.asModule := by
  let σ : Representation ℤ G M := ρ.comp f
  let e := σ.asModuleEquiv.trans ρ.asModuleEquiv.symm
  let F : σ.asModule →ₛₗ[MonoidAlgebra.mapDomainRingHom ℤ f] ρ.asModule :=
    { toFun := e
      map_add' := e.map_add
      map_smul' := by
        intro a x
        apply ρ.asModuleEquiv.injective
        change σ.asAlgebraHom a (σ.asModuleEquiv x) =
          ρ.asAlgebraHom (MonoidAlgebra.mapDomain f a) (σ.asModuleEquiv x)
        rw [representation_mapDomain] }
  exact Module.Finite.of_surjective F e.surjective

theorem finite_representation_comp_iff (ρ : Representation ℤ Q M) (f : G →* Q)
    (hf : Function.Surjective f) :
    Module.Finite ℤ[G] (Representation.asModule (ρ.comp f)) ↔
      Module.Finite ℤ[Q] ρ.asModule := by
  let σ : Representation ℤ G M := ρ.comp f
  let e := σ.asModuleEquiv.trans ρ.asModuleEquiv.symm
  let rmap := MonoidAlgebra.mapDomainRingHom ℤ f
  let F : σ.asModule →ₛₗ[rmap] ρ.asModule :=
    { toFun := e
      map_add' := e.map_add
      map_smul' := by
        intro a x
        apply ρ.asModuleEquiv.injective
        change σ.asAlgebraHom a (σ.asModuleEquiv x) =
          ρ.asAlgebraHom (MonoidAlgebra.mapDomain f a) (σ.asModuleEquiv x)
        rw [representation_mapDomain] }
  let : RingHomSurjective rmap := ⟨by
    intro a
    obtain ⟨b, hb⟩ := Finsupp.mapDomain_surjective hf a.coeff
    refine ⟨MonoidAlgebra.ofCoeff b, ?_⟩
    exact MonoidAlgebra.coeff_injective hb⟩
  exact LinearMap.finite_iff_of_bijective F e.bijective

end PolycyclicRecognition

end

end OAI
