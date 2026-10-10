import Mathlib.RepresentationTheory.Homological.GroupHomology.LowDegree

namespace OAI

/-! # Bilinear pairings descend to second homology of an abelian group

The antisymmetric bar cycle on two commuting elements evaluates to twice the
pairing. This will supply the exterior-square quotient used in the character
obstruction.
-/

noncomputable section
namespace PolycyclicRecognition
open CategoryTheory
open scoped MonoidAlgebra
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {A M : Type} [CommGroup A] [AddCommGroup M]

abbrev integralTrivialCoefficient (A : Type) [Group A] := Rep.trivial ℤ A ℤ

def bilinearPairingChains (b : Additive A →+ Additive A →+ M) :
    (A × A →₀ ℤ) →ₗ[ℤ] M :=
  Finsupp.linearCombination ℤ (fun p => b (Additive.ofMul p.1) (Additive.ofMul p.2))

@[simp] theorem bilinearPairingChains_single (b : Additive A →+ Additive A →+ M)
    (a c : A) (z : ℤ) :
    bilinearPairingChains b (Finsupp.single (a, c) z) =
      z • b (Additive.ofMul a) (Additive.ofMul c) := by
  simp [bilinearPairingChains]

theorem bilinearPairingChains_boundary (b : Additive A →+ Additive A →+ M) :
    (bilinearPairingChains b).comp (groupHomology.d₃₂ (integralTrivialCoefficient A)).hom = 0 := by
  apply Finsupp.lhom_ext'
  intro x
  apply LinearMap.ext
  intro z
  rcases x with ⟨a, c, d⟩
  change bilinearPairingChains b
    (groupHomology.d₃₂ (integralTrivialCoefficient A) (Finsupp.single (a, c, d) z)) = 0
  rw [groupHomology.d₃₂_single]
  change bilinearPairingChains b
    (Finsupp.single (c, d) z - Finsupp.single (a * c, d) z +
      Finsupp.single (a, c * d) z - Finsupp.single (a, c) z) = 0
  simp only [map_sub, map_add, bilinearPairingChains_single, ofMul_mul, AddMonoidHom.add_apply,
    smul_add]
  abel

def antisymmetricBarCycle (a c : A) : groupHomology.cycles₂ (integralTrivialCoefficient A) :=
  ⟨Finsupp.single (a, c) 1 - Finsupp.single (c, a) 1, by
    change groupHomology.d₂₁ (integralTrivialCoefficient A)
      (Finsupp.single (a, c) 1 - Finsupp.single (c, a) 1) = 0
    rw [map_sub, groupHomology.d₂₁_single, groupHomology.d₂₁_single]
    change Finsupp.single c 1 - Finsupp.single (a * c) 1 + Finsupp.single a 1 -
      (Finsupp.single a 1 - Finsupp.single (c * a) 1 + Finsupp.single c 1) = 0
    rw [mul_comm c a]
    abel⟩

theorem bilinearPairingChains_antisymmetric (b : Additive A →+ Additive A →+ M)
    (hskew : ∀ x y, b x y = -b y x) (a c : A) :
    bilinearPairingChains b (antisymmetricBarCycle a c).val =
      (2 : ℤ) • b (Additive.ofMul a) (Additive.ofMul c) := by
  change bilinearPairingChains b (Finsupp.single (a, c) 1 - Finsupp.single (c, a) 1) = _
  rw [map_sub, bilinearPairingChains_single, bilinearPairingChains_single, one_smul, one_smul,
    hskew (Additive.ofMul c) (Additive.ofMul a)]
  simp only [sub_neg_eq_add, two_smul]

def bilinearPairingQuotient (b : Additive A →+ Additive A →+ M) :
    (groupHomology.shortComplexH2 (integralTrivialCoefficient A)).moduleCatLeftHomologyData.H
      →ₗ[ℤ] M := by
  let S := groupHomology.shortComplexH2 (integralTrivialCoefficient A)
  let f : groupHomology.cycles₂ (integralTrivialCoefficient A) →ₗ[ℤ] M :=
    (bilinearPairingChains b).comp (Submodule.subtype _)
  have hz : S.moduleCatToCycles.range ≤ f.ker := by
    rintro x ⟨y, rfl⟩
    change bilinearPairingChains b
      (groupHomology.d₃₂ (integralTrivialCoefficient A) y) = 0
    exact LinearMap.congr_fun (bilinearPairingChains_boundary b) y
  exact S.moduleCatToCycles.range.liftQ f hz

def bilinearPairingHomology (b : Additive A →+ Additive A →+ M) :
    groupHomology.H2 (integralTrivialCoefficient A) →ₗ[ℤ] M :=
  (bilinearPairingQuotient b).comp
    (groupHomology.H2Iso (integralTrivialCoefficient A)).hom.hom

theorem bilinearPairingHomology_π (b : Additive A →+ Additive A →+ M)
    (z : groupHomology.cycles₂ (integralTrivialCoefficient A)) :
    bilinearPairingHomology b (groupHomology.H2π (integralTrivialCoefficient A) z) =
      bilinearPairingChains b z.val := by
  let S := groupHomology.shortComplexH2 (integralTrivialCoefficient A)
  have he : groupHomology.H2π (integralTrivialCoefficient A) ≫
      (groupHomology.H2Iso (integralTrivialCoefficient A)).hom =
      S.moduleCatLeftHomologyData.π := by
    exact ((Iso.comp_inv_eq (groupHomology.H2Iso (integralTrivialCoefficient A))).mp
      (groupHomology.π_comp_H2Iso_inv (integralTrivialCoefficient A))).symm
  have hz := congrArg (fun f => f.hom z) he
  change (groupHomology.H2Iso (integralTrivialCoefficient A)).hom.hom
    ((groupHomology.H2π (integralTrivialCoefficient A)).hom z) =
      S.moduleCatLeftHomologyData.π.hom z at hz
  exact congrArg (bilinearPairingQuotient b) hz

theorem bilinearPairingHomology_antisymmetric (b : Additive A →+ Additive A →+ M)
    (hskew : ∀ x y, b x y = -b y x) (a c : A) :
    bilinearPairingHomology b
      (groupHomology.H2π (integralTrivialCoefficient A) (antisymmetricBarCycle a c)) =
      (2 : ℤ) • b (Additive.ofMul a) (Additive.ofMul c) := by
  rw [bilinearPairingHomology_π]
  exact bilinearPairingChains_antisymmetric b hskew a c

end PolycyclicRecognition

end

end OAI
