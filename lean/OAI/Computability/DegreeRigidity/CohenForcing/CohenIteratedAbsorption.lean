import OAI.Computability.DegreeRigidity.CohenForcing.CohenAbsorptionGeneric
import OAI.Computability.DegreeRigidity.CohenForcing.TaggedProductExtension

namespace OAI

namespace TuringRigidity.CohenIteratedAbsorption
open TransitiveNameModel BoundedSetTheory CountableForcing TaggedProductConditions
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

theorem same_generics_absorption (M q : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hq : q ∈ M) (hct : InternallyCountable M q)
    (G : GenericFilter (Conditions q)) (hG : AtomicForcing.GroundGeneric M G)
    (H : GenericFilter (Conditions (CohenGroundPoset.conditions ZFSet.omega)))
    (hH : AtomicForcing.GroundGeneric (genericExtensionSet M q G.carrier) H) :
    ∃ W : GenericFilter (Conditions InternalCohen.conditions),
      AtomicForcing.GroundGeneric M W ∧
        genericExtensionSet M InternalCohen.conditions W.carrier =
          genericExtensionSet (genericExtensionSet M q G.carrier)
            (CohenGroundPoset.conditions ZFSet.omega) H.carrier := by
  obtain ⟨c,hc,hcs,habs⟩ := CohenAbsorptionGeneric.product_generic_absorption M q hM hT hq hct
  have hb := CohenGroundPoset.conditions_mem M ZFSet.omega hM hT (sourceT_omega_mem M hM hT)
  let J := TaggedProductGeneric.joint q (CohenGroundPoset.conditions ZFSet.omega) c hcs G H
  have hJ := TaggedProductGeneric.joint_ground_generic M q _ c hM hT hq hb hcs G hG H hH
  obtain ⟨W,hW,hWe⟩ := habs J hJ
  exact ⟨W,hW,hWe.trans (TaggedProductExtension.extension_eq M q _ c hM hT hq hb hc hcs G hG H hH)⟩

end TuringRigidity.CohenIteratedAbsorption

end OAI
