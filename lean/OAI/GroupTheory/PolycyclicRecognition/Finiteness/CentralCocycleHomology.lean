import OAI.GroupTheory.PolycyclicRecognition.Finiteness.AbelianSecondHomologyPairing

namespace OAI

/-! # A central two-cocycle evaluates actual second group homology -/

noncomputable section
namespace PolycyclicRecognition
open CategoryTheory
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {Q M : Type} [Group Q] [AddCommGroup M]

def groupTwoCocycleChains (c : Q → Q → M) : ((Q × Q) →₀ ℤ) →ₗ[ℤ] M :=
  Finsupp.linearCombination ℤ (fun p => c p.1 p.2)

omit [Group Q] in
@[simp] theorem groupTwoCocycleChains_single (c : Q → Q → M) (q r : Q) (n : ℤ) :
    groupTwoCocycleChains c (Finsupp.single (q, r) n) = n • c q r := by
  simp [groupTwoCocycleChains]

theorem groupTwoCocycleChains_boundary (c : Q → Q → M)
    (hc : ∀ q r s, c q r + c (q * r) s = c r s + c q (r * s)) :
    (groupTwoCocycleChains c).comp (groupHomology.d₃₂ (integralTrivialCoefficient Q)).hom = 0 := by
  apply Finsupp.lhom_ext'
  intro p
  apply LinearMap.ext
  intro n
  rcases p with ⟨q, r, s⟩
  change groupTwoCocycleChains c
    (groupHomology.d₃₂ (integralTrivialCoefficient Q) (Finsupp.single (q, r, s) n)) = 0
  rw [groupHomology.d₃₂_single]
  change groupTwoCocycleChains c
    (Finsupp.single (r, s) n - Finsupp.single (q * r, s) n +
      Finsupp.single (q, r * s) n - Finsupp.single (q, r) n) = 0
  simp only [map_sub, map_add, groupTwoCocycleChains_single]
  have he := congrArg (fun x : M => n • x) (hc q r s)
  simp only [smul_add] at he
  calc
    n • c r s - n • c (q * r) s + n • c q (r * s) - n • c q r =
        (n • c r s + n • c q (r * s)) - (n • c q r + n • c (q * r) s) := by abel
    _ = 0 := sub_eq_zero.mpr he.symm

def cycleFunctionalHomology
    (F : ((Q × Q) →₀ ℤ) →ₗ[ℤ] M)
    (hF : F.comp (groupHomology.d₃₂ (integralTrivialCoefficient Q)).hom = 0) :
    groupHomology.H2 (integralTrivialCoefficient Q) →ₗ[ℤ] M := by
  let S := groupHomology.shortComplexH2 (integralTrivialCoefficient Q)
  let f : groupHomology.cycles₂ (integralTrivialCoefficient Q) →ₗ[ℤ] M :=
    F.comp (Submodule.subtype _)
  have hz : S.moduleCatToCycles.range ≤ f.ker := by
    rintro x ⟨y, rfl⟩
    change F (groupHomology.d₃₂ (integralTrivialCoefficient Q) y) = 0
    exact LinearMap.congr_fun hF y
  exact (S.moduleCatToCycles.range.liftQ f hz).comp
    (groupHomology.H2Iso (integralTrivialCoefficient Q)).hom.hom

theorem cycleFunctionalHomology_π
    (F : ((Q × Q) →₀ ℤ) →ₗ[ℤ] M)
    (hF : F.comp (groupHomology.d₃₂ (integralTrivialCoefficient Q)).hom = 0)
    (z : groupHomology.cycles₂ (integralTrivialCoefficient Q)) :
    cycleFunctionalHomology F hF
      (groupHomology.H2π (integralTrivialCoefficient Q) z) = F z.val := by
  let S := groupHomology.shortComplexH2 (integralTrivialCoefficient Q)
  have he : groupHomology.H2π (integralTrivialCoefficient Q) ≫
      (groupHomology.H2Iso (integralTrivialCoefficient Q)).hom =
      S.moduleCatLeftHomologyData.π := by
    exact ((Iso.comp_inv_eq (groupHomology.H2Iso (integralTrivialCoefficient Q))).mp
      (groupHomology.π_comp_H2Iso_inv (integralTrivialCoefficient Q))).symm
  have hz := congrArg (fun f => f.hom z) he
  change (groupHomology.H2Iso (integralTrivialCoefficient Q)).hom.hom
    ((groupHomology.H2π (integralTrivialCoefficient Q)).hom z) =
      S.moduleCatLeftHomologyData.π.hom z at hz
  exact congrArg (S.moduleCatToCycles.range.liftQ
    (F.comp (Submodule.subtype _)) (by
      rintro x ⟨y, rfl⟩
      exact LinearMap.congr_fun hF y)) hz

def groupTwoCocycleHomology (c : Q → Q → M)
    (hc : ∀ q r s, c q r + c (q * r) s = c r s + c q (r * s)) :
    groupHomology.H2 (integralTrivialCoefficient Q) →ₗ[ℤ] M :=
  cycleFunctionalHomology (groupTwoCocycleChains c) (groupTwoCocycleChains_boundary c hc)

@[simp] theorem groupTwoCocycleHomology_π (c : Q → Q → M)
    (hc : ∀ q r s, c q r + c (q * r) s = c r s + c q (r * s))
    (z : groupHomology.cycles₂ (integralTrivialCoefficient Q)) :
    groupTwoCocycleHomology c hc
      (groupHomology.H2π (integralTrivialCoefficient Q) z) = groupTwoCocycleChains c z.val :=
  cycleFunctionalHomology_π _ _ _

end PolycyclicRecognition

end

end OAI
