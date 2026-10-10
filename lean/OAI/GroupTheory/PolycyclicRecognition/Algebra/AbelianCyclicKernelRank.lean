import OAI.GroupTheory.PolycyclicRecognition.Finiteness.RationalExteriorHomology
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.AbelianNormalExteriorFiniteness
import OAI.GroupTheory.PolycyclicRecognition.Algebra.NormalAbelianizationQuotient
import OAI.GroupTheory.PolycyclicRecognition.Algebra.CyclicExteriorFiniteRank
import OAI.GroupTheory.PolycyclicRecognition.Algebra.RepresentationFiniteRestriction

namespace OAI

/-! # Finite rational rank of an abelian kernel with cyclic quotient

This is deduced from actual FP-infinity and conjugation on subgroup homology.
No rank, torsion-free, or character-tameness assumption is added.
-/

noncomputable section
namespace PolycyclicRecognition
open CategoryTheory
open scoped MonoidAlgebra TensorProduct IsMulCommutative
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {G : Type} [Group G] (N : Subgroup G) [N.Normal] [IsMulCommutative N]

def abelianKernelAbelianizationIso :
    Rep.of (abelianKernelQuotientConjugationAction N) ≅
      Rep.of (normalQuotientAbelianizationRepresentation N) := by
  let e : Additive N ≃ₗ[ℤ] Additive (Abelianization N) :=
    (Abelianization.equivOfComm (H := N)).toAdditive.toIntLinearEquiv
  refine Rep.mkIso (Representation.Equiv.mk e ?_)
  intro q
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N q
  apply LinearMap.ext
  intro n
  rfl

theorem abelianKernelQuotient_finite [Group.FG G] [IsMulCommutative (G ⧸ N)] :
    Module.Finite ℤ[G ⧸ N] (abelianKernelQuotientConjugationAction N).asModule := by
  have h : IntegralRepresentationFinite (G ⧸ N)
      (Rep.of (normalQuotientAbelianizationRepresentation N)) :=
    finite_normalQuotientAbelianizationModule_of_abelian_quotient N
  exact h.of_iso (abelianKernelAbelianizationIso N).symm

theorem rationalKernelExterior_intertwines (q : G ⧸ N) :
    (rationalAbelianH2Exterior N).comp
        (rationalRepresentation (quotientHomologyAction N (trivialIntegral G) 2).ρ q) =
      (exteriorPower.map 2
        (rationalRepresentation (abelianKernelQuotientConjugationAction N) q)).comp
          (rationalAbelianH2Exterior N) := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N q
  exact rationalAbelianH2Exterior_natural (MulAut.conjNormal (H := N) g).toMonoidHom

def rationalCyclicKernelHomology (f : Multiplicative ℤ →* G ⧸ N) : Rep ℚ (Multiplicative ℤ) :=
  Rep.of (rationalRepresentation ((quotientHomologyAction N (trivialIntegral G) 2).ρ.comp f))

def rationalCyclicKernelAction (f : Multiplicative ℤ →* G ⧸ N) :
    Representation ℚ (Multiplicative ℤ) (ℚ ⊗[ℤ] Additive N) :=
  rationalRepresentation ((abelianKernelQuotientConjugationAction N).comp f)

def rationalCyclicKernelExteriorMap (f : Multiplicative ℤ →* G ⧸ N) :
    rationalCyclicKernelHomology N f ⟶
      Rep.of (rationalExteriorSquareRepresentation (rationalCyclicKernelAction N f)) :=
  Rep.ofHom ⟨rationalAbelianH2Exterior N, fun q => rationalKernelExterior_intertwines N (f q)⟩

theorem abelian_cyclic_kernel_finite_rational_rank [Group.FG G]
    [IsMulCommutative (G ⧸ N)] (h : TypeFPInfinity G)
    (f : Multiplicative ℤ →* G ⧸ N) (hf : Function.Surjective f) :
    FiniteDimensional ℚ (ℚ ⊗[ℤ] Additive N) := by
  let ρ : Representation ℤ (Multiplicative ℤ) (Additive N) :=
    (abelianKernelQuotientConjugationAction N).comp f
  let η : Representation ℤ (Multiplicative ℤ)
      (quotientHomologyAction N (trivialIntegral G) 2) :=
    (quotientHomologyAction N (trivialIntegral G) 2).ρ.comp f
  have hρ : Module.Finite ℤ[Multiplicative ℤ] ρ.asModule :=
    (finite_representation_pullback_iff (abelianKernelQuotientConjugationAction N) f hf).mpr
      (abelianKernelQuotient_finite N)
  have hη : Module.Finite ℤ[Multiplicative ℤ] η.asModule :=
    (finite_representation_pullback_iff
      (quotientHomologyAction N (trivialIntegral G) 2).ρ f hf).mpr
        (typeFPInfinity_normalHomologyQuotient_finite N h 2)
  let := hρ
  let := hη
  have hratρ := rationalRepresentation_finite ρ
  have hratη := rationalRepresentation_finite η
  let := hratρ
  let := hratη
  let F := rationalCyclicKernelExteriorMap N f
  let B := Rep.of (rationalExteriorSquareRepresentation (rationalCyclicKernelAction N f))
  let A := rationalCyclicKernelHomology N f
  let : Module.Finite ℚ[Multiplicative ℤ] A.ρ.asModule := hratη
  let : Module.Finite ℚ[Multiplicative ℤ] (rationalCyclicKernelAction N f).asModule := hratρ
  let FM : A.ρ.asModule →ₗ[ℚ[Multiplicative ℤ]] B.ρ.asModule :=
    Representation.IntertwiningMap.equivLinearMapAsModule A.ρ B.ρ F.hom
  have hsurj : Function.Surjective FM := by
    intro y
    obtain ⟨x, hx⟩ := rationalAbelianH2Exterior_surjective N (B.ρ.asModuleEquiv y)
    refine ⟨A.ρ.asModuleEquiv.symm x, ?_⟩
    apply B.ρ.asModuleEquiv.injective
    exact hx
  have hfin : Module.Finite ℚ[Multiplicative ℤ] B.ρ.asModule :=
    Module.Finite.of_surjective FM hsurj
  let := hfin
  exact rational_cyclic_finite_rank (rationalCyclicKernelAction N f)

end PolycyclicRecognition

end

end OAI
