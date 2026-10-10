import OAI.GroupTheory.PolycyclicRecognition.Finiteness.CohomologicalFiniteness

namespace OAI

/-! # Finite generation in the concrete integral resolutions -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory CategoryTheory.Limits
open scoped MonoidAlgebra

variable (G : Type) [Group G]

theorem integralRepresentationFinite_free (α : Type) [Finite α] :
    IntegralRepresentationFinite G (Rep.free ℤ G α) := by
  classical
  let := Fintype.ofFinite α
  exact Module.Finite.of_basis (Representation.freeAsModuleBasis ℤ G α)

theorem integralRepresentationFinite_of_finite (A : Rep ℤ G)
    (hA : letI : Module ℤ A := A.hV2; Module.Finite ℤ A) :
    IntegralRepresentationFinite G A := by
  let module : Module ℤ A := A.hV2
  let finite : Module.Finite ℤ A := hA
  let moduleZ : Module ℤ A.ρ.asModule := A.ρ.instModuleAsModule
  let finiteModule : Module.Finite ℤ A.ρ.asModule :=
    Module.Finite.equiv A.ρ.asModuleEquiv.symm
  exact Module.Finite.of_restrictScalars_finite ℤ ℤ[G] A.ρ.asModule

theorem integralRepresentationFinite_of_isZero (A : Rep ℤ G) (hA : IsZero A) :
    IntegralRepresentationFinite G A := by
  have ha (a : A) : a = 0 := by
    have hh : (𝟙 A : A ⟶ A) = 0 := hA.eq_of_src _ _
    exact congrArg (fun f : A ⟶ A => f.hom a) hh
  let sub : Subsingleton A := ⟨fun a b => (ha a).trans (ha b).symm⟩
  exact integralRepresentationFinite_of_finite G A (by
    let module : Module ℤ A := A.hV2
    infer_instance)

theorem typeFP_zero : TypeFP G 0 := by
  refine ⟨Rep.barResolution ℤ G, ?_⟩
  intro i hi
  have : i = 0 := by omega
  subst i
  exact integralRepresentationFinite_free G (Fin 0 → G)

theorem typeFPInfinity_of_finite [Finite G] : TypeFPInfinity G := by
  intro n
  refine ⟨Rep.barResolution ℤ G, ?_⟩
  intro i _
  exact integralRepresentationFinite_free G (Fin i → G)

end PolycyclicRecognition

end

end OAI
