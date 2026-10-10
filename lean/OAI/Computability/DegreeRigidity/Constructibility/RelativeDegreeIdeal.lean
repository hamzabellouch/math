import OAI.Computability.DegreeRigidity.SetModels.DegreeUniverseWithoutChoice
import OAI.Computability.DegreeRigidity.Constructibility.RelativeModelComparison
import OAI.Computability.DegreeRigidity.SetModels.ElementaryModelIdeal
import OAI.Computability.DegreeRigidity.Representation.NativeModelCompatibility

namespace OAI


namespace TuringRigidity.RelativeConstructible
open TransitiveNameModel BoundedSetTheory ElementaryModel SetDegreeDecoding
universe u

theorem ground_degreeUniverse_eq_idealSet (M : ZFSet.{u}) [Countable (Conditions M)]
    (hM : Transitive M) (hT : SourceT M) :
    degreeUniverse (groundReals M) = idealSet (modelIdeal M hM hT) := by
  have eq (A : Oracle) (hA : A ∈ modelReals M) :=
    degreeCode_eq_degreeSet M hM hT (groundReals M) (realCode_mem_groundReals M) hA
  apply ZFSet.ext; intro x
  rw [mem_degreeUniverse,mem_idealSet]
  constructor
  · rintro ⟨A,hA,rfl⟩
    have hAM := (realCode_mem_groundReals M A).mp hA
    exact ⟨degree A,⟨A,hAM,rfl⟩,eq A hAM⟩
  · rintro ⟨d,⟨A,hA,rfl⟩,rfl⟩
    exact ⟨A,(realCode_mem_groundReals M A).mpr hA,(eq A hA).symm⟩

theorem ground_degreeUniverse_mem_relativeModel (M : ZFSet.{u})
    (hM : Transitive M) (hT : SourceT M) :
    degreeUniverse (groundReals M) ∈ relativeModel M (groundReals M) := by
  let R := groundReals M
  let N := relativeModel M R
  have hR := groundReals_mem M hM hT
  have hRN : R ∈ N := (mem_relativeModel M R R hM hT hR).mpr (parameter_in_relativeModel M R hM hT)
  have hr (w : ZFSet.{u}) (hw : w ∈ R) : ∃ B : Oracle, realCode B = w :=
    ⟨decodeReal w,realCode_decodeReal ((mem_groundReals M w).mp hw).2⟩
  exact internal_degreeUniverse_without_choice N (relativeModel_transitive M R hM)
    (relativeModel_pairing M R hM hT hR) (relativeModel_union M R hM hT hR)
    (relativeModel_power_set M R hM hT hR)
    (relativeModel_bounded_separation M R hM hT hR)
    (ground_relativeModel_omega M hM hT) R hRN hr

theorem ground_idealSet_mem_relativeModel (M : ZFSet.{u}) [Countable (Conditions M)]
    (hM : Transitive M) (hT : SourceT M) :
    idealSet (modelIdeal M hM hT) ∈ relativeModel M (groundReals M) := by
  rw [←ground_degreeUniverse_eq_idealSet M hM hT]
  exact ground_degreeUniverse_mem_relativeModel M hM hT

end TuringRigidity.RelativeConstructible

end OAI
