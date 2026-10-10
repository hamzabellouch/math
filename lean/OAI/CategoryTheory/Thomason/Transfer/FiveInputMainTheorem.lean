import OAI.CategoryTheory.Thomason.Simplicial.ConstructedExtensionLocalizer
import OAI.CategoryTheory.Thomason.Transfer.SemanticMainTheorem

namespace OAI

section

/-! # All dimensions after discharging the canonical-extension input -/

namespace Thomason.Construction

/-- The all-dimensions theorem with five published-input hypotheses.
The canonical-extension weak equivalence follows from the subdivision
homotopy and its realization comparison. -/
theorem main_with_five_published_inputs
    (G : RightGrayInput normalizedSimplexIdentities) (t : GrayTruncationInput G)
    (hk : PublishedAcyclicKanLifting)
    (transfer : PublishedThomasonReduction normalizedSimplexIdentities)
    (loc : PublishedStreetLocalizationInput normalizedSimplexIdentities) :
    let kq := kanQuillenInput_of_acyclic_kan_lifting hk
    Nonempty (ThomasonModelResult normalizedSimplexIdentities.thomasonLeft
      normalizedSimplexIdentities.streetNerve kq canonicalExtension_weak) ∧
      ∀ n, Nonempty (ThomasonModelResult
        ((constructedFiniteReflection n).thomasonLeft normalizedSimplexIdentities)
        (normalizedSimplexIdentities.finiteStreetNerve (n+1)) kq canonicalExtension_weak) :=
  main_with_acyclic_kan_lifting G t hk canonicalExtension_weak transfer loc

end Thomason.Construction

end

end OAI
