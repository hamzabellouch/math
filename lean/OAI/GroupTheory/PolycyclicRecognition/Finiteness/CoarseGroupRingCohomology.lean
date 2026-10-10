import OAI.GroupTheory.PolycyclicRecognition.Finiteness.ControlledCochainHomotopy
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.ControlledGroupCohomology

namespace OAI

/-! # Coarse invariance of group-ring cohomology

The maps need not be homomorphisms. Their finite coarse errors provide the
controlled prism homotopies, and hence inverse maps on group-ring cohomology.
-/

noncomputable section
namespace PolycyclicRecognition
open CategoryTheory
variable {G H R : Type} [Group G] [Group H] [CommRing R]

def GroupCoarseEquivalence.refl (G : Type) [Group G] : GroupCoarseEquivalence G G where
  toFun := id
  invFun := id
  bornologous_toFun := groupBornologous_hom (MonoidHom.id G)
  bornologous_invFun := groupBornologous_hom (MonoidHom.id G)
  left_error := by simp
  right_error := by simp

@[simp] theorem controlledCochainMap_refl :
    controlledCochainMap (R := R) (GroupCoarseEquivalence.refl G) =
      𝟙 (controlledCochainComplex R G) := by
  ext n c
  rfl

/-- The coarse inverse produces inverse controlled cochain maps up to homotopy. -/
def controlledCochainHomotopyEquiv (e : GroupCoarseEquivalence G H) :
    HomotopyEquiv (controlledCochainComplex R G) (controlledCochainComplex R H) where
  hom := controlledCochainMap e.symm
  inv := controlledCochainMap e
  homotopyHomInvId := by
    have h := (controlledCochainHomotopy (R := R) (GroupCoarseEquivalence.refl G)
      (e.trans e.symm) e.left_error).symm
    simpa only [controlledCochainMap_refl, controlledCochainMap_trans] using h
  homotopyInvHomId := by
    have h := (controlledCochainHomotopy (R := R) (GroupCoarseEquivalence.refl H)
      (e.symm.trans e) e.right_error).symm
    simpa only [controlledCochainMap_refl, controlledCochainMap_trans] using h

/-- Coarse-equivalent groups have isomorphic controlled scalar cohomology. -/
def controlledCohomologyIso (e : GroupCoarseEquivalence G H) (n : ℕ) :
    (controlledCochainComplex R G).homology n ≅ (controlledCochainComplex R H).homology n where
  hom := HomologicalComplex.homologyMap (controlledCochainMap e.symm) n
  inv := HomologicalComplex.homologyMap (controlledCochainMap e) n
  hom_inv_id := by
    rw [← HomologicalComplex.homologyMap_comp]
    exact ((controlledCochainHomotopyEquiv (R := R) e).homotopyHomInvId.homologyMap_eq n).trans
      (HomologicalComplex.homologyMap_id _ _)
  inv_hom_id := by
    rw [← HomologicalComplex.homologyMap_comp]
    exact ((controlledCochainHomotopyEquiv (R := R) e).homotopyInvHomId.homologyMap_eq n).trans
      (HomologicalComplex.homologyMap_id _ _)

/-- The group-ring case of coarse cohomology invariance, with the actual
left regular representations and standard group cohomology. -/
def coarseGroupRingCohomologyIso (e : GroupCoarseEquivalence G H) (n : ℕ) :
    groupCohomology (Rep.leftRegular R G) n ≅ groupCohomology (Rep.leftRegular R H) n :=
  (controlledGroupCohomologyIso n).symm ≪≫ controlledCohomologyIso e n ≪≫
    controlledGroupCohomologyIso n

end PolycyclicRecognition

end

end OAI
