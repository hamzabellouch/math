import OAI.GroupTheory.PolycyclicRecognition.Finiteness.HomogeneousRepresentationCochains
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.ControlledCochainComplex
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Basic

namespace OAI

/-! # Controlled cochains compute group-ring cohomology

Coefficient extraction identifies the whole controlled complex with the
Hom complex of the standard projective resolution, including its differential.
-/

noncomputable section
namespace PolycyclicRecognition
open CategoryTheory
variable {G R : Type} [Group G] [CommRing R] {n : ℕ}

theorem homogeneousGroupRingLinear_coboundary (c : controlledCochains R G n) :
    homogeneousGroupRingLinear (controlledCoboundary c) =
      (homogeneousGroupRingLinear c).comp (Rep.standardComplex.d R G (n + 1)) := by
  refine MonoidAlgebra.lhom_ext' fun x => LinearMap.ext_ring ?_
  simp only [LinearMap.comp_apply]
  ext h
  simp [homogeneousGroupRingLinear_single, homogeneousGroupRingValue_coeff,
    controlledCoboundary_apply, Function.comp_def]

theorem homogeneousRepresentationCochain_coboundary (c : controlledCochains R G n) :
    homogeneousRepresentationCochain (controlledCoboundary c) =
      (Rep.standardComplex R G).d (n + 1) n ≫ homogeneousRepresentationCochain c := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  change homogeneousGroupRingLinear (controlledCoboundary c) =
    (homogeneousGroupRingLinear c).comp ((Rep.standardComplex R G).d (n + 1) n).hom.toLinearMap
  rw [Rep.standardComplex.d_eq]
  exact homogeneousGroupRingLinear_coboundary c

/-- The controlled complex is the actual standard-resolution cochain complex. -/
def controlledStandardCochainIso :
    controlledCochainComplex R G ≅
      (Rep.standardComplex R G).linearYonedaObj R (Rep.leftRegular R G) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun _ => homogeneousRepresentationCochainEquiv.toModuleIso) (by
      rintro i j (h : i + 1 = j)
      subst j
      rw [controlledCochainComplex_d]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro c
      change (Rep.standardComplex R G).d (i + 1) i ≫ homogeneousRepresentationCochain c =
        homogeneousRepresentationCochain (controlledCoboundary c)
      exact (homogeneousRepresentationCochain_coboundary c).symm)

/-- Controlled scalar homogeneous cohomology is group-ring cohomology. -/
def controlledGroupCohomologyIso (n : ℕ) :
    (controlledCochainComplex R G).homology n ≅
      groupCohomology (Rep.leftRegular R G) n :=
  (HomologicalComplex.homologyFunctor (ModuleCat R) _ n).mapIso
    controlledStandardCochainIso ≪≫
      (groupCohomologyIso (Rep.leftRegular R G) n (Rep.standardResolution R G)).symm

end PolycyclicRecognition

end

end OAI
