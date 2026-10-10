import OAI.GroupTheory.PolycyclicRecognition.Finiteness.ExteriorSquareHomologyNaturality
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.NormalHomologyModuleFiniteness

namespace OAI

/-! # The exterior square of an abelian normal subgroup

The quotient acts by actual conjugation. The cross product is equivariant and,
when multiplication by two is injective on the exterior square, embeds this
module in second homology. No character-tameness conclusion is asserted.
-/

noncomputable section
namespace PolycyclicRecognition
open CategoryTheory
open scoped MonoidAlgebra IsMulCommutative
attribute [local instance 2000] Rep.hV2 Rep.instLinear

theorem IntegralRepresentationFinite.of_mono {Q : Type} [CommGroup Q] [Group.FG Q]
    {A B : Rep ℤ Q} (f : A ⟶ B) [Mono f]
    (hB : IntegralRepresentationFinite Q B) : IntegralRepresentationFinite Q A := by
  let : Module ℤ A := A.hV2
  let : Module ℤ B := B.hV2
  let : IsNoetherianRing ℤ[Q] := integralAbelianGroupRing_noetherian Q
  let : Module.Finite ℤ[Q] B.ρ.asModule := hB
  let fM : A.ρ.asModule →ₗ[ℤ[Q]] B.ρ.asModule :=
    Representation.IntertwiningMap.equivLinearMapAsModule A.ρ B.ρ f.hom
  apply Module.Finite.of_injective fM
  intro x y hxy
  apply A.ρ.asModuleEquiv.injective
  apply (Rep.mono_iff_injective f).mp inferInstance
  exact congrArg B.ρ.asModuleEquiv hxy

variable {G : Type} [Group G] (N : Subgroup G) [N.Normal] [IsMulCommutative N]

def abelianKernelConjugationAction : Representation ℤ G (Additive N) where
  toFun g := additiveGroupLinearMap (MulAut.conjNormal (H := N) g).toMonoidHom
  map_one' := by
    apply LinearMap.ext
    intro n
    change Additive.ofMul (MulAut.conjNormal (H := N) 1 n.toMul) = n
    rw [map_one]
    rfl
  map_mul' g h := by
    apply LinearMap.ext
    intro n
    change Additive.ofMul (MulAut.conjNormal (H := N) (g * h) n.toMul) =
      Additive.ofMul (MulAut.conjNormal (H := N) g
        (MulAut.conjNormal (H := N) h n.toMul))
    rw [map_mul]
    rfl

def abelianKernelQuotientConjugationAction : Representation ℤ (G ⧸ N) (Additive N) :=
  QuotientGroup.lift N (abelianKernelConjugationAction N) (by
    intro g hg
    apply LinearMap.ext
    intro n
    change Additive.ofMul (MulAut.conjNormal (H := N) g n.toMul) = n
    apply congrArg Additive.ofMul
    have he : MulAut.conjNormal (H := N) g n.toMul =
        (⟨g, hg⟩ : N) * n.toMul * (⟨g, hg⟩ : N)⁻¹ := Subtype.ext rfl
    rw [he, mul_comm (⟨g, hg⟩ : N), mul_inv_cancel_right]
    rfl)

def abelianNormalExteriorAction : Rep ℤ (G ⧸ N) :=
  Rep.of (exteriorSquareRepresentation (abelianKernelQuotientConjugationAction N))

def abelianNormalExteriorProduct :
    abelianNormalExteriorAction N ⟶ quotientHomologyAction N (trivialIntegral G) 2 := by
  refine Rep.ofHom ⟨abelianH2ExteriorProduct N, ?_⟩
  intro q
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N q
  apply LinearMap.ext
  intro x
  have h := LinearMap.congr_fun
    (abelianH2ExteriorProduct_natural (MulAut.conjNormal (H := N) g).toMonoidHom) x
  exact h.symm

theorem abelianNormalExteriorProduct_mono
    (h2 : Function.Injective (fun x : ⋀[ℤ]^2 (Additive N) => (2 : ℤ) • x)) :
    Mono (abelianNormalExteriorProduct N) := by
  apply (Rep.mono_iff_injective _).mpr
  exact abelianH2ExteriorProduct_injective N h2

/-- A concrete necessary finiteness consequence of FP-infinity. -/
theorem typeFPInfinity_abelianNormalExterior_finite [Group.FG G]
    [IsMulCommutative (G ⧸ N)] (h : TypeFPInfinity G)
    (h2 : Function.Injective (fun x : ⋀[ℤ]^2 (Additive N) => (2 : ℤ) • x)) :
    IntegralRepresentationFinite (G ⧸ N) (abelianNormalExteriorAction N) := by
  let := abelianNormalExteriorProduct_mono N h2
  exact (typeFPInfinity_normalHomologyQuotient_finite N h 2).of_mono
    (abelianNormalExteriorProduct N)

end PolycyclicRecognition

end

end OAI
