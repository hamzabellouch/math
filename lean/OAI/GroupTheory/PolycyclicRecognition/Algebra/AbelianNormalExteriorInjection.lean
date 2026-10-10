import OAI.GroupTheory.PolycyclicRecognition.Algebra.ScalarHigherProductNaturality
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.AbelianNormalHigherExteriorFiniteness

namespace OAI

/-! # FP-infinity controls all exterior degrees in every characteristic -/

noncomputable section
namespace PolycyclicRecognition
open CategoryTheory
open scoped TensorProduct MonoidAlgebra IsMulCommutative
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable (K : Type) [Field K] {G : Type} [Group G]
  (N : Subgroup G) [N.Normal] [IsMulCommutative N]

def scalarAbelianNormalExteriorInjection (n : ℕ) :
    scalarAbelianNormalExterior K N (n + 1) ⟶ scalarNormalHomology K N (n + 1) := by
  refine Rep.ofHom ⟨scalarHigherExteriorProduct K N n, ?_⟩
  intro q
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N q
  exact (scalarHigherExteriorProduct_natural K
    (MulAut.conjNormal (H := N) g).toMonoidHom n).symm

theorem typeFPInfinity_abelianNormalHigherExterior_finite_all_char [Group.FG G]
    [IsMulCommutative (G ⧸ N)] (h : TypeFPInfinity G) (n : ℕ) :
    Module.Finite K[G ⧸ N] (scalarAbelianNormalExterior K N (n + 1)).ρ.asModule := by
  let A := scalarAbelianNormalExterior K N (n + 1)
  let B := scalarNormalHomology K N (n + 1)
  let : Module.Finite ℤ[G ⧸ N]
      (quotientHomologyAction N (trivialIntegral G) (n + 1)).ρ.asModule :=
    typeFPInfinity_normalHomologyQuotient_finite N h (n + 1)
  let : Module.Finite K[G ⧸ N] B.ρ.asModule :=
    scalarExtendedRepresentation_finite K
      (quotientHomologyAction N (trivialIntegral G) (n + 1)).ρ
  let : IsNoetherianRing K[G ⧸ N] :=
    Algebra.FiniteType.isNoetherianRing K K[G ⧸ N]
  let : IsNoetherian K[G ⧸ N] B.ρ.asModule :=
    isNoetherian_of_isNoetherianRing_of_finite K[G ⧸ N] B.ρ.asModule
  let f := scalarAbelianNormalExteriorInjection K N n
  let fM : A.ρ.asModule →ₗ[K[G ⧸ N]] B.ρ.asModule :=
    Representation.IntertwiningMap.equivLinearMapAsModule A.ρ B.ρ f.hom
  apply Module.Finite.of_injective fM
  intro x y hxy
  apply A.ρ.asModuleEquiv.injective
  apply scalarHigherExteriorProduct_injective K N n
  exact congrArg B.ρ.asModuleEquiv hxy

end PolycyclicRecognition

end

end OAI
