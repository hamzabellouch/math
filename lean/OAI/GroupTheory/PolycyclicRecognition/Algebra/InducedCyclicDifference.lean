import OAI.GroupTheory.PolycyclicRecognition.Finiteness.InducedTranslationAugmentation
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.CyclicExtensionFiniteness
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.InducedCohomologyDifference

namespace OAI

/-! # The explicit translation difference lifts the cyclic augmentation map -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory Representation
open scoped MonoidAlgebra
attribute [local instance 2000] Rep.hV2

variable {G : Type} [Group G] (N : Subgroup G) [N.Normal] [IsCyclic (G ⧸ N)]

local instance : CommGroup (G ⧸ N) := IsCyclic.commGroup

theorem quotientRightTranslation_sub (t : G) :
    quotientRightTranslation ℤ N t - 𝟙 _ =
      Rep.resMap (QuotientGroup.mk' N) (cyclicDifference (G ⧸ N) (QuotientGroup.mk' N t)) := by
  apply Rep.hom_ext
  apply IntertwiningMap.ext
  apply MonoidAlgebra.lhom_ext'
  intro c
  apply LinearMap.ext_ring
  change (quotientRightTranslation ℤ N t).hom (MonoidAlgebra.single c 1) -
      MonoidAlgebra.single c 1 =
    Representation.leftRegular ℤ (G ⧸ N) (QuotientGroup.mk' N t) (MonoidAlgebra.single c 1) -
      MonoidAlgebra.single c 1
  rw [quotientRightTranslation_single, Representation.ofMulAction_single, smul_eq_mul, mul_comm]

def quotientInducedResolution (P : ProjectiveResolution (Rep.trivial ℤ N ℤ)) :=
  projectiveResolutionAlongIso (normalInducedResolution ℤ N P) (inductionTrivialIso ℤ N)

omit [IsCyclic (G ⧸ N)] in
theorem quotientInducedResolution_augmentation (P : ProjectiveResolution (Rep.trivial ℤ N ℤ)) :
    (quotientInducedResolution N P).π.f 0 =
      Rep.indMap N.subtype (P.π.f 0) ≫ (inductionTrivialIso ℤ N).hom := rfl

theorem inducedDifference_augmentation (t : G) (P : ProjectiveResolution (Rep.trivial ℤ N ℤ)) :
    ((inducedTranslation ℤ N t P - 𝟙 _).f 0) ≫ (quotientInducedResolution N P).π.f 0 =
      (quotientInducedResolution N P).π.f 0 ≫
        Rep.resMap (QuotientGroup.mk' N) (cyclicDifference (G ⧸ N) (QuotientGroup.mk' N t)) := by
  let p : P.complex.X 0 ⟶ Rep.trivial ℤ N ℤ := P.π.f 0
  let I := Rep.indMap N.subtype p
  let e := (inductionTrivialIso ℤ N).hom
  let U := inducedTrivialTranslation ℤ N t
  let Q := quotientRightTranslation ℤ N t
  let T : Rep.ind N.subtype (P.complex.X 0) ⟶ Rep.ind N.subtype (P.complex.X 0) :=
    (inducedTranslation ℤ N t P).f 0
  have hT : T ≫ I = I ≫ U := inducedTranslation_augmentation_zero ℤ N t P
  have hU : U ≫ e = e ≫ Q := inducedTrivialTranslation_quotient ℤ N t
  rw [quotientInducedResolution_augmentation, ← quotientRightTranslation_sub]
  change (T - 𝟙 (Rep.ind N.subtype (P.complex.X 0))) ≫ (I ≫ e) =
    (I ≫ e) ≫ (Q - 𝟙 (Rep.res (QuotientGroup.mk' N) (Rep.leftRegular ℤ (G ⧸ N))))
  calc
    (T - 𝟙 (Rep.ind N.subtype (P.complex.X 0))) ≫ (I ≫ e) = (T ≫ I) ≫ e - I ≫ e := by
      simp only [Preadditive.sub_comp, Category.id_comp, Category.assoc]
    _ = (I ≫ U) ≫ e - I ≫ e := by rw [hT]
    _ = (I ≫ e) ≫ Q - I ≫ e := by rw [Category.assoc, hU, ← Category.assoc]
    _ = (I ≫ e) ≫ (Q - 𝟙 (Rep.res (QuotientGroup.mk' N) (Rep.leftRegular ℤ (G ⧸ N)))) := by rw [Preadditive.comp_sub, Category.comp_id]

def inducedCyclicDifferenceHomotopy (t : G) (P : ProjectiveResolution (Rep.trivial ℤ N ℤ)) :
    Homotopy
      (ProjectiveResolution.lift
        (Rep.resMap (QuotientGroup.mk' N) (cyclicDifference (G ⧸ N) (QuotientGroup.mk' N t)))
        (quotientInducedResolution N P) (quotientInducedResolution N P))
      (inducedTranslation ℤ N t P - 𝟙 _) := by
  let R := quotientInducedResolution N P
  let f := Rep.resMap (QuotientGroup.mk' N)
    (cyclicDifference (G ⧸ N) (QuotientGroup.mk' N t))
  let u : ProjectiveResolution.Hom R R f :=
    ⟨inducedTranslation ℤ N t P - 𝟙 _, inducedDifference_augmentation N t P⟩
  exact ProjectiveResolution.liftHomotopy f _ _ (ProjectiveResolution.lift_commutes f R R)
    u.hom_comp_π

end PolycyclicRecognition

end

end OAI
