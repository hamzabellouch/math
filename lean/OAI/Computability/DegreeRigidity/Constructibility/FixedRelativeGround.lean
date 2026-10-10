import OAI.Computability.DegreeRigidity.SetModels.NoNewOrdinals
import OAI.Computability.DegreeRigidity.Constructibility.RelativeModelComparison
import OAI.Computability.DegreeRigidity.Representation.SourceTGenericPersistence

namespace OAI

namespace TuringRigidity.RelativeConstructible
open TransitiveNameModel BoundedSetTheory CountableForcing
universe u

theorem relativeModel_generic_fixed_parameter (M : ZFSet.{u})
    (hM : Transitive M) (hT : SourceT M) {R c o : ZFSet.{u}}
    [Preorder (Conditions c)] [OrderTop (Conditions c)] (hR : R ∈ M)
    (hc : c ∈ M) (ho : o ∈ M)
    (hos : ∀ r s : Conditions c, ZFSet.pair (label c r) (label c s) ∈ o ↔ r ≤ s)
    (G : GenericFilter (Conditions c)) (hG : AtomicForcing.GroundGeneric M G) :
    relativeModel (genericExtensionSet M c G.carrier) R = relativeModel M R := by
  obtain ⟨p,hp⟩ := G.nonempty
  have ht := G.upper le_top hp
  have hME := ground_inclusion_set M c hM hT.pairing hT.union hT.powerSet
    hT.separation.finitePrefix.bounded hT.replacement.finitePrefix hT.infinity hc G.carrier ht
  apply relativeModel_eq_of_same_ordinals _ M R
    (genericExtensionSet_transitive M c hM G.carrier)
    (extension_sourceT M hM hT hc ho hos G hG ht) (hME hR) hM hT hR
  intro δ
  exact ⟨extension_ordinal_ground M c hM hT G.carrier δ,fun hδ => hME hδ⟩

end TuringRigidity.RelativeConstructible

end OAI
