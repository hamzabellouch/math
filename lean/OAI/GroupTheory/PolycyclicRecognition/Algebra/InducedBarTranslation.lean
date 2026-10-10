import OAI.GroupTheory.PolycyclicRecognition.Algebra.BarAutomorphism
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.IntegerExtensionHomology

namespace OAI

/-! # An explicit bar lift of translation in an infinite cyclic extension -/

noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {G : Type} [Group G] (N : Subgroup G) [N.Normal] (t : G)

local instance [IsCyclic (G ⧸ N)] : CommGroup (G ⧸ N) := IsCyclic.commGroup

def inducedBarTranslation :
    (normalInducedResolution ℤ N (Rep.barResolution ℤ N)).complex ⟶
      (normalInducedResolution ℤ N (Rep.barResolution ℤ N)).complex where
  f i := inducedSemilinearMap ℤ N t (Rep.free ℤ N (Fin i → N))
    (Rep.free ℤ N (Fin i → N))
    (barAutomorphismFreeMap (MulAut.conjNormal (H := N) t⁻¹) i)
  comm' i j _ := by
    change inducedSemilinearMap ℤ N t _ _
        ((barAutomorphismMap (MulAut.conjNormal (H := N) t⁻¹)).f i) ≫
          Rep.indMap N.subtype ((Rep.barComplex ℤ N).d i j) =
      Rep.indMap N.subtype ((Rep.barComplex ℤ N).d i j) ≫
        inducedSemilinearMap ℤ N t _ _
          ((barAutomorphismMap (MulAut.conjNormal (H := N) t⁻¹)).f j)
    rw [semilinear_comp_inductionMap, inductionMap_comp_semilinear]
    congr 1
    exact (barAutomorphismMap (MulAut.conjNormal (H := N) t⁻¹)).comm i j

theorem inducedBarTranslation_augmentation :
    (inducedBarTranslation N t).f 0 ≫ Rep.indMap N.subtype ((Rep.barResolution ℤ N).π.f 0) =
      Rep.indMap N.subtype ((Rep.barResolution ℤ N).π.f 0) ≫ inducedTrivialTranslation ℤ N t := by
  let P := Rep.barResolution ℤ N
  let b := barAutomorphismFreeMap (MulAut.conjNormal (H := N) t⁻¹) 0
  let p : P.complex.X 0 ⟶ Rep.trivial ℤ N ℤ := P.π.f 0
  change inducedSemilinearMap ℤ N t (P.complex.X 0) (P.complex.X 0) b ≫
      Rep.indMap N.subtype p = Rep.indMap N.subtype p ≫
        inducedSemilinearMap ℤ N t (Rep.trivial ℤ N ℤ) (Rep.trivial ℤ N ℤ)
          (𝟙 (Rep.trivial ℤ N ℤ))
  rw [semilinear_comp_inductionMap ℤ N t (A := P.complex.X 0)
    (B := P.complex.X 0) (C := Rep.trivial ℤ N ℤ) b p]
  have hb : b ≫ Rep.resMap (MulAut.conjNormal (H := N) t⁻¹).toMonoidHom p = p :=
    barAutomorphismFreeMap_augmentation _
  erw [hb, inductionMap_comp_semilinear ℤ N t (A := P.complex.X 0)
    (B := Rep.trivial ℤ N ℤ) (C := Rep.trivial ℤ N ℤ) p (𝟙 _), Category.comp_id]

theorem inducedBarTranslation_quotient_augmentation [IsCyclic (G ⧸ N)] :
    ((inducedBarTranslation N t - 𝟙 _).f 0) ≫
        (quotientInducedResolution N (Rep.barResolution ℤ N)).π.f 0 =
      (quotientInducedResolution N (Rep.barResolution ℤ N)).π.f 0 ≫
        Rep.resMap (QuotientGroup.mk' N)
          (cyclicDifference (G ⧸ N) (QuotientGroup.mk' N t)) := by
  let P := Rep.barResolution ℤ N
  let I : (normalInducedResolution ℤ N P).complex.X 0 ⟶
      Rep.ind N.subtype (Rep.trivial ℤ N ℤ) := Rep.indMap N.subtype (P.π.f 0)
  let e := (inductionTrivialIso ℤ N).hom
  let B := inducedBarTranslation N t
  let T := inducedTranslation ℤ N t P
  have hT : B.f 0 ≫ I = T.f 0 ≫ I :=
    (inducedBarTranslation_augmentation N t).trans
      (inducedTranslation_augmentation_zero ℤ N t P).symm
  have heq : (B - 𝟙 _).f 0 ≫ (quotientInducedResolution N P).π.f 0 =
      (T - 𝟙 _).f 0 ≫ (quotientInducedResolution N P).π.f 0 := by
    change (B.f 0 - 𝟙 _) ≫ (I ≫ e) = (T.f 0 - 𝟙 _) ≫ (I ≫ e)
    simp only [Preadditive.sub_comp, Category.id_comp, ← Category.assoc, hT]
    exact congrArg (fun z => (T.f 0 ≫ I) ≫ e - z ≫ e) (Category.id_comp I).symm
  exact heq.trans (inducedDifference_augmentation N t P)

def integerExtensionBarHomotopy (q : G →* Multiplicative ℤ)
    [IsCyclic (G ⧸ q.ker)] :
    Homotopy (integerExtensionMap q t (Rep.barResolution ℤ q.ker))
      (inducedBarTranslation q.ker t - 𝟙 _) := by
  letI : CommGroup (G ⧸ q.ker) := IsCyclic.commGroup
  let R := quotientInducedResolution q.ker (Rep.barResolution ℤ q.ker)
  let f := Rep.resMap (QuotientGroup.mk' q.ker)
    (cyclicDifference (G ⧸ q.ker) (QuotientGroup.mk' q.ker t))
  let u : ProjectiveResolution.Hom R R f :=
    ⟨inducedBarTranslation q.ker t - 𝟙 _, inducedBarTranslation_quotient_augmentation q.ker t⟩
  exact ProjectiveResolution.liftHomotopy f _ _ (ProjectiveResolution.lift_commutes f R R)
    u.hom_comp_π

end PolycyclicRecognition

end

end OAI
