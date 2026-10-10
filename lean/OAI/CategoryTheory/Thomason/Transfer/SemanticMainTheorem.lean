import OAI.CategoryTheory.Thomason.Gray.GrayFinitePosetUnits
import OAI.CategoryTheory.Thomason.Gray.SimplexCylinderGeneration
import OAI.CategoryTheory.Thomason.Simplicial.PosetSieveNaturality
import OAI.CategoryTheory.Thomason.Simplicial.SimplicialSpanFactorization
import OAI.CategoryTheory.Thomason.Strict.StreetSingularWeakReflection
import OAI.CategoryTheory.Thomason.Strict.UnderlyingCategory
import OAI.CategoryTheory.Thomason.Transfer.HornAttachmentWeakEquivalences
import OAI.CategoryTheory.Thomason.Transfer.KanQuillenLiftingReduction
import OAI.CategoryTheory.Thomason.Transfer.SimplicialRangeGluing
import OAI.CategoryTheory.Thomason.Transfer.ThomasonQuillenBridge

namespace OAI

section

/-! # The main theorem with concrete chain, fibre and finite-reflection inputs

Normalized chains construct the orientals, their ordinal maps and the
interval diagonal. Contractions and two-sieve induction show that the
finite-poset adjunction units are weak equivalences. Finite reflection
commutes with zero fibres; simplexwise clamping proves poset-sieve
preservation. Strong deformations and algebraic boundary factorization
give simplicial gluing. A semantic quotient of finite formal cells
constructs small strict colimits.
-/

namespace Thomason.Construction

/-- All dimensions of the main theorem after discharging the normalized-chain
and Alexander–Whitney identities, constructing the oriental edges and proving
the finite-poset units, zero-fibre adjunctions, intelligent finite reflection,
simplicial gluing from geometric deformation, and poset-sieve preservation.
The published-input hypotheses are explicit. -/
theorem main_with_remaining_published_inputs
    (G : RightGrayInput normalizedSimplexIdentities) (t : GrayTruncationInput G)
    (kq : KanQuillenPublishedInput.{0})
    (hj : ∀ X : SSet.{0}, realizationWeakEquivalences (canonicalExtension.app X))
    (transfer : PublishedThomasonReduction normalizedSimplexIdentities)
    (loc : PublishedStreetLocalizationInput normalizedSimplexIdentities) :
    Nonempty (ThomasonModelResult normalizedSimplexIdentities.thomasonLeft
      normalizedSimplexIdentities.streetNerve kq hj) ∧
      ∀ n, Nonempty (ThomasonModelResult ((constructedFiniteReflection n).thomasonLeft normalizedSimplexIdentities)
        (normalizedSimplexIdentities.finiteStreetNerve (n + 1)) kq hj) :=
  conditional_main_all_dimensions normalizedSimplexIdentities G t constructedFiniteReflection
    (SimplexComplex.alexanderWhitneyInput normalizedSimplexIdentities)
    normalizedSimplexIdentities.constructedOmegaPosetSieveInput.allDimensions
    constructedSimplicialGluingUnconditional kq hj
    (normalizedSimplexIdentities.finitePosetUnitInput_fromGray G t
      (SimplexComplex.alexanderWhitneyInput normalizedSimplexIdentities)) transfer loc

end Thomason.Construction

end

section

/-! # All dimensions after the direct realization two-out-of-three proof

The Kan–Quillen hypotheses are its two semantic class
identifications (Goerss–Jardine, I.11.3–I.11.4 and Corollary II.8.6). Neither model-category axioms nor
two-out-of-three are assumed by this specialization of the main theorem.
-/

namespace Thomason.Construction

open CategoryTheory CategoryTheory.MorphismProperty SSet.modelCategoryQuillen

/-- The main theorem assuming the two published semantic class identifications. -/
theorem main_with_semantic_class_inputs
    (G : RightGrayInput normalizedSimplexIdentities) (t : GrayTruncationInput G)
    (hb : I.rlp = J.rlp ⊓ realizationWeakEquivalences.{0})
    (hh : SSet.anodyneExtensions.{0} = monomorphisms SSet.{0} ⊓ realizationWeakEquivalences)
    (hj : ∀ X : SSet.{0}, realizationWeakEquivalences (canonicalExtension.app X))
    (transfer : PublishedThomasonReduction normalizedSimplexIdentities)
    (loc : PublishedStreetLocalizationInput normalizedSimplexIdentities) :
    let kq := kanQuillenInput_of_class_identifications hb hh
    Nonempty (ThomasonModelResult normalizedSimplexIdentities.thomasonLeft
      normalizedSimplexIdentities.streetNerve kq hj) ∧
      ∀ n, Nonempty (ThomasonModelResult
        ((constructedFiniteReflection n).thomasonLeft normalizedSimplexIdentities)
        (normalizedSimplexIdentities.finiteStreetNerve (n+1)) kq hj) :=
  main_with_remaining_published_inputs G t
    (kanQuillenInput_of_class_identifications hb hh) hj transfer loc

/-- The main theorem assuming the published anodyne characterization. -/
theorem main_with_anodyne_input
    (G : RightGrayInput normalizedSimplexIdentities) (t : GrayTruncationInput G)
    (hh : SSet.anodyneExtensions.{0} = monomorphisms SSet.{0} ⊓ realizationWeakEquivalences)
    (hj : ∀ X : SSet.{0}, realizationWeakEquivalences (canonicalExtension.app X))
    (transfer : PublishedThomasonReduction normalizedSimplexIdentities)
    (loc : PublishedStreetLocalizationInput normalizedSimplexIdentities) :
    let kq := kanQuillenInput_of_anodyne_class hh
    Nonempty (ThomasonModelResult normalizedSimplexIdentities.thomasonLeft
      normalizedSimplexIdentities.streetNerve kq hj) ∧
      ∀ n, Nonempty (ThomasonModelResult
        ((constructedFiniteReflection n).thomasonLeft normalizedSimplexIdentities)
        (normalizedSimplexIdentities.finiteStreetNerve (n+1)) kq hj) :=
  main_with_remaining_published_inputs G t
    (kanQuillenInput_of_anodyne_class hh) hj transfer loc

/-- The main theorem assuming acyclic Kan lifting, as in Goerss–Jardine,
Theorems I.11.3–I.11.4 and Corollary II.8.6. -/
theorem main_with_acyclic_kan_lifting
    (G : RightGrayInput normalizedSimplexIdentities) (t : GrayTruncationInput G)
    (hk : PublishedAcyclicKanLifting)
    (hj : ∀ X : SSet.{0}, realizationWeakEquivalences (canonicalExtension.app X))
    (transfer : PublishedThomasonReduction normalizedSimplexIdentities)
    (loc : PublishedStreetLocalizationInput normalizedSimplexIdentities) :
    let kq := kanQuillenInput_of_acyclic_kan_lifting hk
    Nonempty (ThomasonModelResult normalizedSimplexIdentities.thomasonLeft
      normalizedSimplexIdentities.streetNerve kq hj) ∧
      ∀ n, Nonempty (ThomasonModelResult
        ((constructedFiniteReflection n).thomasonLeft normalizedSimplexIdentities)
        (normalizedSimplexIdentities.finiteStreetNerve (n+1)) kq hj) :=
  main_with_remaining_published_inputs G t
    (kanQuillenInput_of_acyclic_kan_lifting hk) hj transfer loc

end Thomason.Construction

end

end OAI
