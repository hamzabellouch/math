import OAI.Computability.DegreeRigidity.SetModels.InternalQuotientExtension
import OAI.Computability.DegreeRigidity.SetModels.InternalCountableClosure

namespace OAI

namespace TuringRigidity.InternalQuotientCountability
open TransitiveNameModel BoundedSetTheory CountableForcing
open InternalRegularOperations InternalRegularAlgebra InternalBooleanSyntax
open InternalProjectedGeneric InternalQuotientGeneric
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder
  codeOrder codePreorder

theorem countability_upward (M N c : ZFSet.{0}) (hMN : M ⊆ N)
    (hct : InternallyCountable M c) : InternallyCountable N c := by
  obtain ⟨E,hE,hfun,honto⟩ := hct
  exact ⟨E,hMN hE,hfun,honto⟩

theorem quotient_countable (M c B Q A : ZFSet.{0})
    (hM : Transitive M) (hT : SourceT M) (hc : c ∈ M) (hBM : B ∈ M) (hAM : A ∈ M)
    (hB : ∀ U, U ∈ B ↔ U ∈ M ∧ IsCode c U)
    (hQ : ∀ F, F ∈ Q ↔ F ∈ M ∧ F ⊆ B) (hA : Closed c B Q A)
    (hct : InternallyCountable M c)
    (G : GenericFilter (Conditions c)) (hG : AtomicForcing.GroundGeneric M G) :
    let H := projected M c B Q A hM hT hc hBM hAM hB hQ hA G
    let N := genericExtensionSet M (positive A) H.carrier
    let q := InternalQuotientConditions.conditions c A (genericFilterSet (positive A) H.carrier)
    InternallyCountable N q := by
  obtain ⟨hN,hTN,hMN,_,hqN,_⟩ := InternalQuotientExtension.intermediate_properties M c B Q A
    hM hT hc hBM hAM hB hQ hA G hG
  apply InternalCountableClosure.countable_subset _ c _ hN hTN (hMN hc) hqN
    (InternalQuotientConditions.conditions_subset c A _) (countability_upward M _ c hMN hct)
  obtain ⟨p,hp⟩ := G.nonempty
  exact ⟨label c p,InternalQuotientConditions.original_condition_mem M c B Q A
    hM hT hc hBM hAM hB hQ hA G p hp⟩

end TuringRigidity.InternalQuotientCountability

end OAI
