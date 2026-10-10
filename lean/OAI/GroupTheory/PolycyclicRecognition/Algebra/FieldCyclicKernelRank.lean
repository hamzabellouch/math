import OAI.GroupTheory.PolycyclicRecognition.Algebra.ScalarH2CrossProductNaturality
import OAI.GroupTheory.PolycyclicRecognition.Algebra.AbelianCyclicKernelRank

namespace OAI

/-! # Finite rank of cyclic kernels after extension to a field

This includes prime-field reductions as well as rationalization. The exterior
cross product is injective in every characteristic.
-/

noncomputable section
namespace PolycyclicRecognition
open CategoryTheory
open scoped TensorProduct MonoidAlgebra IsMulCommutative
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable (K : Type) [Field K] {G : Type} [Group G]
  (N : Subgroup G) [N.Normal] [IsMulCommutative N]

def fieldCyclicKernelAction (f : Multiplicative ℤ →* G ⧸ N) :
    Representation K (Multiplicative ℤ) (K ⊗[ℤ] Additive N) :=
  scalarExtendedRepresentation K ((abelianKernelQuotientConjugationAction N).comp f)

def fieldCyclicKernelHomology (f : Multiplicative ℤ →* G ⧸ N) : Rep K (Multiplicative ℤ) :=
  Rep.of (scalarExtendedRepresentation K
    ((quotientHomologyAction N (trivialIntegral G) 2).ρ.comp f))

theorem fieldKernelExterior_intertwines (q : G ⧸ N) :
    (scalarExtendedRepresentation K (quotientHomologyAction N (trivialIntegral G) 2).ρ q).comp
        (scalarExtendedH2ExteriorProduct K N) =
      (scalarExtendedH2ExteriorProduct K N).comp
        (exteriorPower.map 2
          (scalarExtendedRepresentation K (abelianKernelQuotientConjugationAction N) q)) := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N q
  exact scalarExtendedH2ExteriorProduct_natural K (MulAut.conjNormal (H := N) g).toMonoidHom

def fieldCyclicKernelExteriorMap (f : Multiplicative ℤ →* G ⧸ N) :
    Rep.of (rationalExteriorSquareRepresentation (fieldCyclicKernelAction K N f)) ⟶
      fieldCyclicKernelHomology K N f :=
  Rep.ofHom ⟨scalarExtendedH2ExteriorProduct K N,
    fun q => (fieldKernelExterior_intertwines K N (f q)).symm⟩

theorem abelian_cyclic_kernel_field_finite_rank [Group.FG G]
    [IsMulCommutative (G ⧸ N)] (h : TypeFPInfinity G)
    (f : Multiplicative ℤ →* G ⧸ N) (hf : Function.Surjective f) :
    FiniteDimensional K (K ⊗[ℤ] Additive N) := by
  let ρ : Representation ℤ (Multiplicative ℤ) (Additive N) :=
    (abelianKernelQuotientConjugationAction N).comp f
  let η : Representation ℤ (Multiplicative ℤ)
      (quotientHomologyAction N (trivialIntegral G) 2) :=
    (quotientHomologyAction N (trivialIntegral G) 2).ρ.comp f
  let : Module.Finite ℤ[Multiplicative ℤ] ρ.asModule :=
    (finite_representation_pullback_iff (abelianKernelQuotientConjugationAction N) f hf).mpr
      (abelianKernelQuotient_finite N)
  let : Module.Finite ℤ[Multiplicative ℤ] η.asModule :=
    (finite_representation_pullback_iff
      (quotientHomologyAction N (trivialIntegral G) 2).ρ f hf).mpr
        (typeFPInfinity_normalHomologyQuotient_finite N h 2)
  let A := Rep.of (rationalExteriorSquareRepresentation (fieldCyclicKernelAction K N f))
  let B := fieldCyclicKernelHomology K N f
  let : Module.Finite K[Multiplicative ℤ] (fieldCyclicKernelAction K N f).asModule :=
    scalarExtendedRepresentation_finite K ρ
  let : Module.Finite K[Multiplicative ℤ] B.ρ.asModule :=
    scalarExtendedRepresentation_finite K η
  let : IsNoetherianRing K[Multiplicative ℤ] :=
    Algebra.FiniteType.isNoetherianRing K K[Multiplicative ℤ]
  let : IsNoetherian K[Multiplicative ℤ] B.ρ.asModule :=
    isNoetherian_of_isNoetherianRing_of_finite K[Multiplicative ℤ] B.ρ.asModule
  let F := fieldCyclicKernelExteriorMap K N f
  let FM : A.ρ.asModule →ₗ[K[Multiplicative ℤ]] B.ρ.asModule :=
    Representation.IntertwiningMap.equivLinearMapAsModule A.ρ B.ρ F.hom
  have hinj : Function.Injective FM := by
    intro x y hxy
    apply A.ρ.asModuleEquiv.injective
    apply scalarExtendedH2ExteriorProduct_injective K N
    exact congrArg B.ρ.asModuleEquiv hxy
  let : Module.Finite K[Multiplicative ℤ] A.ρ.asModule :=
    Module.Finite.of_injective FM hinj
  exact rational_cyclic_finite_rank (fieldCyclicKernelAction K N f)

end PolycyclicRecognition

end

end OAI
