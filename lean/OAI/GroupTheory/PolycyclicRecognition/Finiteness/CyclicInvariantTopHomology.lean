import OAI.GroupTheory.PolycyclicRecognition.Finiteness.InducedBarHomology

namespace OAI

/-! # A fixed top class lifts across an infinite cyclic quotient -/

noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits HomologicalComplex
attribute [local instance 2000] Rep.hV2 Rep.instLinear ModuleCat.isModule
variable {G : Type} [Group G]

theorem integerExtensionTensorMap_zero (q : G →* Multiplicative ℤ)
    [IsCyclic (G ⧸ q.ker)] (t : G) (A : Rep ℤ G) (d : ℕ)
    (ha : normalHomologyMap ℤ q.ker A d t⁻¹ = 𝟙 _) :
    HomologicalComplex.homologyMap
      (integerExtensionTensorMap q t (Rep.barResolution ℤ q.ker) A) d = 0 := by
  classical
  let F := ((Rep.coinvariantsTensor ℤ G).obj A).mapHomologicalComplex (ComplexShape.down ℕ)
  let C := (quotientInducedResolution q.ker (Rep.barResolution ℤ q.ker)).complex
  let B : C ⟶ C := inducedBarTranslation q.ker t
  let E := inducedBarHomologyIso q.ker A d
  have hB : HomologicalComplex.homologyMap (F.map B) d = 𝟙 _ := by
    apply (cancel_mono E.hom).mp
    have he := inducedBarHomologyIso_translation q.ker A t d
    rw [ha, Category.comp_id] at he
    exact he.trans (Category.id_comp E.hom).symm
  have h := (((Rep.coinvariantsTensor ℤ G).obj A).mapHomotopy
    (integerExtensionBarHomotopy (t := t) q)).homologyMap_eq d
  change HomologicalComplex.homologyMap
      (integerExtensionTensorMap q t (Rep.barResolution ℤ q.ker) A) d =
    HomologicalComplex.homologyMap (F.map (B - 𝟙 C)) d at h
  rw [F.map_sub, F.map_id, HomologicalComplex.homologyMap_sub,
    HomologicalComplex.homologyMap_id, hB, sub_self] at h
  exact h

def cyclicInvariantTopHomologyIso (q : G →* Multiplicative ℤ)
    (t : G) (ht : q t = Multiplicative.ofAdd 1) (A : Rep ℤ G) (d : ℕ)
    (hv : IsZero (groupHomology (Rep.res q.ker.subtype A) (d + 1)))
    (ha : normalHomologyMap ℤ q.ker A d t⁻¹ = 𝟙 _) :
    groupHomology A (d + 1) ≅ groupHomology (Rep.res q.ker.subtype A) d := by
  classical
  letI := integerQuotient_isCyclic q t ht
  letI := integerQuotient_infinite q t ht
  let P := Rep.barResolution ℤ q.ker
  have hz := integerExtensionTensorMap_zero q t A d ha
  let E : kernel (HomologicalComplex.homologyMap (integerExtensionTensorMap q t P A) d) ≅
      ((normalInducedResolution ℤ q.ker P).complex.coinvariantsTensorObj A).homology d := by
    rw [hz]
    exact kernelZeroIsoSource
  exact integerExtensionHomologyKernelIso q t ht P A d hv ≪≫ E ≪≫
    inducedBarHomologyIso q.ker A d

end PolycyclicRecognition

end

end OAI
