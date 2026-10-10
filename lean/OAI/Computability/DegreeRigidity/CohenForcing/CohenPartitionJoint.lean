import OAI.Computability.DegreeRigidity.CohenForcing.CohenPartitionBridge
import OAI.Computability.DegreeRigidity.SetModels.InternalOrderIsoTransport
import OAI.Computability.DegreeRigidity.CohenForcing.TaggedProductExtension

namespace OAI

namespace TuringRigidity.CohenPartitionJoint
open TransitiveNameModel BoundedSetTheory CountableForcing CohenGroundPoset
open TaggedProductConditions CohenProductSplitting InternalCohenFactor
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

theorem reassemble (M A B : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hA : A ∈ M) (hB : B ∈ M) (hBA : B ⊆ A)
    (J : GenericFilter (Conditions (conditions B))) (hJ : AtomicForcing.GroundGeneric M J)
    (R : GenericFilter (Conditions (conditions (A \ B))))
    (hR : AtomicForcing.GroundGeneric (genericExtensionSet M (conditions B) J.carrier) R) :
    ∃ U : GenericFilter (Conditions (conditions A)), AtomicForcing.GroundGeneric M U ∧
      genericExtensionSet M (conditions A) U.carrier =
        genericExtensionSet (genericExtensionSet M (conditions B) J.carrier)
          (conditions (A \ B)) R.carrier := by
  have hfac := factor_internal M A B hM hT hA hB
  have hcA := conditions_mem M A hM hT hA
  obtain ⟨c,hc,hcs,f,hf,_,hfs,_⟩ := internal_product M _ _ hM hT hfac.1 hfac.2.1
  let T := TaggedProductGeneric.joint _ _ c hcs J R
  have hTg := TaggedProductGeneric.joint_ground_generic M _ _ c hM hT hfac.1 hfac.2.1 hcs J hJ R hR
  have hTe := TaggedProductExtension.extension_eq M _ _ c hM hT hfac.1 hfac.2.1 hc hcs J hJ R hR
  let e := (productIso (conditions B) (conditions (A \ B)) c hcs).symm.trans (factorIso A B hBA).symm
  obtain ⟨g,hg,hge⟩ := CohenPartitionBridge.internal_union_iso M A B c f hM hT hA hB hBA hc hf hcs hfs
  refine ⟨AutomorphismName.mapFilter e T,
    InternalOrderIsoTransport.map_ground_generic M _ _ g hM hT hc hcA hg e hge T hTg,?_⟩
  exact (InternalOrderIsoTransport.extension_eq M _ _ g hM hT hc hcA hg e hge T hTg).trans hTe

end TuringRigidity.CohenPartitionJoint

end OAI
