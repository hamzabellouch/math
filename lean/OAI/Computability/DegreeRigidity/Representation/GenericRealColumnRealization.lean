import OAI.Computability.DegreeRigidity.Effective.PrefixSingletonRealization
import OAI.Computability.DegreeRigidity.CohenForcing.CohenPartitionRealization
import OAI.Computability.DegreeRigidity.CohenForcing.CohenRemainderTransport
import OAI.Computability.DegreeRigidity.Representation.OriginalRealCohenFactorization
import OAI.Computability.DegreeRigidity.Representation.CommonExtensionProgram
import OAI.Computability.DegreeRigidity.SetModels.InternalShuffleGeneric

namespace OAI


namespace TuringRigidity.RelativeConstructible
open TransitiveNameModel BoundedSetTheory CountableForcing InternalCountableOrdinals
open CohenColumnRealName
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

theorem generic_real_column_realizes (M K a : ZFSet.{0})
    (hM : Transitive M) (hT : SourceT M) (hK : FirstUncountable M K) (ha : a ∈ K)
    (G : GenericFilter (Conditions (poset K))) (hG : AtomicForcing.GroundGeneric M G)
    (A : Oracle) (hAE : realCode A ∈ genericExtensionSet M (poset K) G.carrier)
    (hA : AtomicForcing.GroundGeneric M (InternalCohen.pushFilter (CohenBorelForcing.realFilter A))) :
    ColumnRealizesExtension M K a (genericExtensionSet M (poset K) G.carrier) A := by
  obtain ⟨hN,L,hL,hLe⟩ := OriginalRealCohenFactorization.real_factorization M K hM hT hK
    G hG (realCode A) hAE (realCode_subset A)
  have haM := hM K hK.2.1 a ha
  have hsingle := singleton_mem M hM hT.pairing haM
  have hsK : ({a} : ZFSet.{0}) ⊆ K := by
    intro x hx
    exact ZFSet.mem_singleton.mp hx ▸ ha
  obtain ⟨R,hR,hRe⟩ := CohenRemainderTransport.transport_to_remainder M _ K {a}
    hM hT hN.1 hN.2.1 hN.2.2.1 hK hsingle hsK
    (Or.inr (InternalCountableClosure.singleton_countable M a hM hT haM)) L hL
  obtain ⟨J,hJ,hJe,hJA⟩ := PrefixSingletonRealization.singleton_realization M a hM hT haM A hA
  have hRJ : AtomicForcing.GroundGeneric (genericExtensionSet M (poset {a}) J.carrier) R := by
    rw [hJe]
    exact hR
  obtain ⟨U,hU,hUe,hUA⟩ := CohenPartitionRealization.reassemble_column M K a hM hT hK.2.1 ha A
    J hJ hJA R hRJ
  refine ⟨U,hU,hUe.trans ?_,hUA⟩
  rw [hJe]
  exact hRe.trans hLe

theorem shuffled_real_column_realizes (M K a : ZFSet.{0})
    (hM : Transitive M) (hT : SourceT M) (hK : FirstUncountable M K) (ha : a ∈ K)
    (G : GenericFilter (Conditions (poset K))) (hG : AtomicForcing.GroundGeneric M G)
    (Y L : Oracle)
    (hYE : realCode Y ∈ genericExtensionSet M (poset K) G.carrier)
    (hLE : realCode L ∈ genericExtensionSet M (poset K) G.carrier)
    (hL : AtomicForcing.GroundGeneric M (InternalCohen.pushFilter (CohenBorelForcing.realFilter L))) :
    ColumnRealizesExtension M K a (genericExtensionSet M (poset K) G.carrier) (GenericCoding.code Y L) := by
  obtain ⟨hE,hTE,_,_⟩ := RegularTreeExtension.extension_properties M (poset K) hM hT
    (CohenGroundPoset.conditions_mem M _ hM hT
      (product_mem M hM hT.pairing hT.union hT.powerSet hT.separation.finitePrefix.bounded
        hK.2.1 (sourceT_omega_mem M hM hT))) G hG
  have hcode := sourceT_real_lower _ hE hTE (sourceT_real_join _ hE hTE hYE hLE)
    (GenericCoding.code_reduces Y L)
  exact generic_real_column_realizes M K a hM hT hK ha G hG _ hcode
    (InternalCohen.groundGeneric_shuffle M hM hT L hL Y)

end TuringRigidity.RelativeConstructible

end OAI
