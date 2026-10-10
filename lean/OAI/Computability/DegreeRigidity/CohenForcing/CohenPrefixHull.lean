import OAI.Computability.DegreeRigidity.CohenForcing.CohenPrefixReconstruction
import OAI.Computability.DegreeRigidity.Representation.RealGeneratedModel
import OAI.Computability.DegreeRigidity.SetModels.RegularTreeExtension

namespace OAI


namespace TuringRigidity.InternalCohen
open TransitiveNameModel BoundedSetTheory CohenBorelForcing CountableForcing
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

theorem prefix_extension_eq_hull (M : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (A : Oracle) (hA : AtomicForcing.GroundGeneric M (pushFilter (realFilter A))) :
    genericExtensionSet M conditions (pushFilter (realFilter A)).carrier =
      RealGeneratedModel.hull M (realCode A) := by
  obtain ⟨hN,hTN,hMN,_⟩ := RegularTreeExtension.extension_properties M conditions hM hT
    (conditions_mem M hM hT) (pushFilter (realFilter A)) hA
  have hAN : realCode A ∈ genericExtensionSet M conditions (pushFilter (realFilter A)).carrier :=
    (mem_extensionSet _ _ _ _).mpr ⟨realName,realName_internal M hM hT,val_realName A⟩
  symm
  apply RealGeneratedModel.hull_eq_of_least M _ _ ⟨hN,hTN,hMN,hAN⟩
  intro N hN
  exact InternalNameEvaluation.extension_subset M N hN.1 hN.2.1 hN.2.2.1 _
    (prefixFilterSet_mem N hN.1 hN.2.1 A hN.2.2.2)

theorem prefix_extension_eq_of_hull (M : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (A B : Oracle)
    (hA : AtomicForcing.GroundGeneric M (pushFilter (realFilter A)))
    (hB : AtomicForcing.GroundGeneric M (pushFilter (realFilter B)))
    (he : RealGeneratedModel.hull M (realCode A) = RealGeneratedModel.hull M (realCode B)) :
    genericExtensionSet M conditions (pushFilter (realFilter A)).carrier =
      genericExtensionSet M conditions (pushFilter (realFilter B)).carrier := by
  rw [prefix_extension_eq_hull M hM hT A hA,prefix_extension_eq_hull M hM hT B hB,he]

end TuringRigidity.InternalCohen

end OAI
