import OAI.CategoryTheory.Thomason.Chains.FinalPositiveSimplexSupport
import OAI.CategoryTheory.Thomason.Chains.NormalizedCubicalLifting
import OAI.CategoryTheory.Thomason.Chains.NormalizedTuples
import OAI.CategoryTheory.Thomason.Chains.SimplexBasisHeight
import OAI.CategoryTheory.Thomason.Gray.ConstructedRightGray
import OAI.CategoryTheory.Thomason.Gray.CylinderAssembly
import OAI.CategoryTheory.Thomason.Gray.DirectedGlobeFaces
import OAI.CategoryTheory.Thomason.Gray.DirectedGlobeUniversal
import OAI.CategoryTheory.Thomason.Gray.GlobePastingDensity
import OAI.CategoryTheory.Thomason.Gray.GrayChainGlobeRestriction
import OAI.CategoryTheory.Thomason.Gray.GrayMappingEndpointEvaluation
import OAI.CategoryTheory.Thomason.Gray.GrayMappingInterchangeEvaluation
import OAI.CategoryTheory.Thomason.Gray.GraySimplexProjection
import OAI.CategoryTheory.Thomason.Gray.GraySingularPathComparison
import OAI.CategoryTheory.Thomason.Gray.GridGlobeCylinderComparison
import OAI.CategoryTheory.Thomason.Gray.OrderedAtomGrouping
import OAI.CategoryTheory.Thomason.Gray.PastingGlobeChains
import OAI.CategoryTheory.Thomason.Gray.PastingGlobeCylinderPath
import OAI.CategoryTheory.Thomason.Gray.PastingGlobeCylinderRetractions
import OAI.CategoryTheory.Thomason.Gray.PosetPrismEndpoints
import OAI.CategoryTheory.Thomason.Gray.PrismSimplexNaturality
import OAI.CategoryTheory.Thomason.Gray.RightCylinderPrism
import OAI.CategoryTheory.Thomason.Gray.SimplexCylinderGeneration
import OAI.CategoryTheory.Thomason.Gray.SimplicialHomotopyWhiskering
import OAI.CategoryTheory.Thomason.Gray.SingularCylinderEquivalence
import OAI.CategoryTheory.Thomason.Gray.StrictAbelianization
import OAI.CategoryTheory.Thomason.Gray.TopologicalConePrism
import OAI.CategoryTheory.Thomason.Gray.TopologicalIntervalCylinder
import OAI.CategoryTheory.Thomason.Gray.TripleGlobeRetractions
import OAI.CategoryTheory.Thomason.Simplicial.AcyclicKanSimplexLifting
import OAI.CategoryTheory.Thomason.Simplicial.BarycentricSortedCoordinates
import OAI.CategoryTheory.Thomason.Simplicial.BarycentricSupportInclusion
import OAI.CategoryTheory.Thomason.Simplicial.CanonicalExtensionAnodyneHorn
import OAI.CategoryTheory.Thomason.Simplicial.CanonicalExtensionCartesian
import OAI.CategoryTheory.Thomason.Simplicial.CanonicalExtensionImageLattice
import OAI.CategoryTheory.Thomason.Simplicial.ConstructedExtensionLocalizer
import OAI.CategoryTheory.Thomason.Simplicial.ConstructedPosetCosieves
import OAI.CategoryTheory.Thomason.Simplicial.DoubleSubdivisionStability
import OAI.CategoryTheory.Thomason.Simplicial.ExhaustionWeakEquivalence
import OAI.CategoryTheory.Thomason.Simplicial.FaceSimplexLift
import OAI.CategoryTheory.Thomason.Simplicial.FiniteKanBaseChangeApproximation
import OAI.CategoryTheory.Thomason.Simplicial.FinitePosetCoordinates
import OAI.CategoryTheory.Thomason.Simplicial.FinitePosetUnitReduction
import OAI.CategoryTheory.Thomason.Simplicial.FiniteRelativeRealizationLifting
import OAI.CategoryTheory.Thomason.Simplicial.FiniteSingularRelativeLifting
import OAI.CategoryTheory.Thomason.Simplicial.FixedInternalPathMaps
import OAI.CategoryTheory.Thomason.Simplicial.HomotopyFiberPathEquivalence
import OAI.CategoryTheory.Thomason.Simplicial.HornWeakEquivalences
import OAI.CategoryTheory.Thomason.Simplicial.InfiniteExtensionBaseChange
import OAI.CategoryTheory.Thomason.Simplicial.InfiniteExtensionKan
import OAI.CategoryTheory.Thomason.Simplicial.KanBaseChangeExhaustion
import OAI.CategoryTheory.Thomason.Simplicial.KanContractedFamilyLifting
import OAI.CategoryTheory.Thomason.Simplicial.KanFiberComponentTransport
import OAI.CategoryTheory.Thomason.Simplicial.KanFinitePosetExtension
import OAI.CategoryTheory.Thomason.Simplicial.KanRealizedEdgeComposition
import OAI.CategoryTheory.Thomason.Simplicial.KanSimplexContinuousFibers
import OAI.CategoryTheory.Thomason.Simplicial.LastVertexWeakEquivalence
import OAI.CategoryTheory.Thomason.Simplicial.NonsingularFaceCarriers
import OAI.CategoryTheory.Thomason.Simplicial.RealizationCellClosure
import OAI.CategoryTheory.Thomason.Simplicial.RealizationSubcomplexSemantics
import OAI.CategoryTheory.Thomason.Simplicial.RealizationTopology
import OAI.CategoryTheory.Thomason.Simplicial.RealizedSimplexWeakEquivalences
import OAI.CategoryTheory.Thomason.Simplicial.SieveFiberPresentation
import OAI.CategoryTheory.Thomason.Simplicial.SimplexCubeRetract
import OAI.CategoryTheory.Thomason.Simplicial.SimplicialApproximation
import OAI.CategoryTheory.Thomason.Simplicial.SimplicialSpanFactorization
import OAI.CategoryTheory.Thomason.Simplicial.SingularAcyclicFibers
import OAI.CategoryTheory.Thomason.Simplicial.SingularCounitSurjectivity
import OAI.CategoryTheory.Thomason.Simplicial.SingularCubeNaturality
import OAI.CategoryTheory.Thomason.Simplicial.SingularKanComplex
import OAI.CategoryTheory.Thomason.Simplicial.SingularPathSpaceAdjunction
import OAI.CategoryTheory.Thomason.Simplicial.SkeletalWeakEquivalences
import OAI.CategoryTheory.Thomason.Simplicial.SubcomplexFaceLifting
import OAI.CategoryTheory.Thomason.Simplicial.SubdivisionFaceImages
import OAI.CategoryTheory.Thomason.Simplicial.SubdivisionUnions
import OAI.CategoryTheory.Thomason.Simplicial.SubdivisionWeakLifting
import OAI.CategoryTheory.Thomason.Simplicial.TopologicalDeformationTransport
import OAI.CategoryTheory.Thomason.Simplicial.TruncatedLocalPresentability
import OAI.CategoryTheory.Thomason.Simplicial.TruncationCongruence
import OAI.CategoryTheory.Thomason.Simplicial.TruncationQuotientComposition
import OAI.CategoryTheory.Thomason.Simplicial.WeakPathSurjectivity
import OAI.CategoryTheory.Thomason.Strict.FiniteCosieveMembership
import OAI.CategoryTheory.Thomason.Strict.FiniteLabelledPresentation
import OAI.CategoryTheory.Thomason.Strict.FiniteSieveWeakEquivalenceBridge
import OAI.CategoryTheory.Thomason.Strict.OrientalFiniteCells
import OAI.CategoryTheory.Thomason.Strict.OrientalLabelFibers
import OAI.CategoryTheory.Thomason.Strict.StreetFilteredColimits
import OAI.CategoryTheory.Thomason.Strict.StreetSingularWeakReflection
import OAI.CategoryTheory.Thomason.Strict.StreetWhitehead
import OAI.CategoryTheory.Thomason.Strict.StrictCompositeListReplacement
import OAI.CategoryTheory.Thomason.Strict.StrictIsomorphisms
import OAI.CategoryTheory.Thomason.Strict.StrictPosetStarSemantics
import OAI.CategoryTheory.Thomason.Strict.StrictPosetWeakEquivalences
import OAI.CategoryTheory.Thomason.Strict.StrictTerminalConeCategory
import OAI.CategoryTheory.Thomason.Strict.StrictTerminalConeFunctor
import OAI.CategoryTheory.Thomason.Strict.UnderlyingCategory
import OAI.CategoryTheory.Thomason.Transfer.FiniteCosieveAttachmentComparison
import OAI.CategoryTheory.Thomason.Transfer.FiniteEmptyAttachmentFibers
import OAI.CategoryTheory.Thomason.Transfer.FiniteStreetSievePushouts
import OAI.CategoryTheory.Thomason.Transfer.FiveInputMainTheorem
import OAI.CategoryTheory.Thomason.Transfer.HornAttachmentWeakEquivalences
import OAI.CategoryTheory.Thomason.Transfer.NonsingularFaceGluing
import OAI.CategoryTheory.Thomason.Transfer.PastingGlobeCylinderPushout
import OAI.CategoryTheory.Thomason.Transfer.SemanticMainTheorem
import OAI.CategoryTheory.Thomason.Transfer.SimplicialRangeGluing
import OAI.CategoryTheory.Thomason.Transfer.StreetLocalizationFromModel
import OAI.CategoryTheory.Thomason.Transfer.StrictPushoutGeneration
import OAI.CategoryTheory.Thomason.Transfer.ThomasonLeftProperness
import OAI.CategoryTheory.Thomason.Transfer.ThomasonQuillenBridge
import OAI.CategoryTheory.Thomason.Transfer.ThomasonSmallObject
import OAI.CategoryTheory.Thomason.Transfer.TripleGlobeCylinderPushout
import OAI.CategoryTheory.Thomason.Transfer.WeakFactorizationRecognition

namespace OAI

section

/-! # Acyclic attachments of literal twice-subdivided simplex subcomplexes -/

namespace Thomason.Construction

open CategoryTheory CategoryTheory.Limits PartialOrder StrictOmegaCategory
open FiniteSubsetAttachments
open scoped Simplicial

noncomputable section

namespace NormalizedSimplexIdentities

variable (h : NormalizedSimplexIdentities) [StrictColimitsInput]

/-- The actual Thomason image of an acyclic simplex-subcomplex inclusion
remains a Street weak equivalence under every individual attachment. -/
theorem subcomplex_attachment_acyclic
    (G : RightGrayInput h) (aw : SimplexComplex.AlexanderWhitneyInput h)
    (s : PublishedPosetSieveInput h) (g : PublishedSimplicialGluingInput)
    (kq : KanQuillenPublishedInput.{0})
    {m : ℕ} (A : (Δ[m] : SSet.{0}).Subcomplex)
    (hA : realizationWeakEquivalences A.ι) :
    cobaseWeak h.streetWeakEquivalences (h.thomasonLeft.map A.ι) := by
  let : Finite (DoubleSubdivisionPairs.Faces m) := finite_nonemptyFiniteChains _
  let S := DoubleSubdivisionPairs.oldFaces A
  let : Finite (NonemptyFiniteChains (DoubleSubdivisionPairs.Faces m)) :=
    finite_nonemptyFiniteChains _
  have wi : realizationWeakEquivalences
      (nerveMap (subposetInclusion (ChainSieve.old S)).monotone.functor) :=
    (DoubleSubdivisionPairs.map_property_iff (𝟭 SSet) realizationWeakEquivalences A).mp
      ((subdivision_twice_weak_iff A.ι).mpr hA)
  have wci : h.streetWeakEquivalences (h.posetMap (subposetInclusion (ChainSieve.old S))) :=
    (h.finite_poset_map_weakEquivalence_iff G aw s g kq _).mpr wi
  have : Mono (h.streetNerve.map (h.categorification.map
      (nerveMap (subposetInclusion (ChainSieve.old S)).monotone.functor))) :=
    s.omega_nerve_mono (ChainSieve.old S) (ChainSieve.old_lower S)
  change cobaseWeak h.streetWeakEquivalences
    (h.categorification.map (SSet.sd.map (SSet.sd.map A.ι)))
  apply (DoubleSubdivisionPairs.map_property_iff h.categorification
    (cobaseWeak h.streetWeakEquivalences) A).mpr
  rw [cobaseWeak_iff]
  intro X Y a b j hp
  exact attachment_weak_of_nerve_comparison h.streetNerve kq hp wci
    (h.finite_chain_attachment_comparison G aw s g kq S hp)

end NormalizedSimplexIdentities

namespace FiniteReflectionInput

variable {n : ℕ} (r : FiniteReflectionInput n)
  (h : NormalizedSimplexIdentities) [StrictColimitsInput]

/-- Finite reflection retains the same acyclic attachment theorem in the
original category of strict `(n+1)`-categories. -/
theorem subcomplex_attachment_acyclic
    (G : RightGrayInput h) (t : GrayTruncationInput G)
    (aw : SimplexComplex.AlexanderWhitneyInput h)
    (s : PublishedPosetSieveInput h) (g : PublishedSimplicialGluingInput)
    (kq : KanQuillenPublishedInput.{0})
    {m : ℕ} (A : (Δ[m] : SSet.{0}).Subcomplex)
    (hA : realizationWeakEquivalences A.ι) :
    cobaseWeak (thomasonWeakEquivalences (n := n) h) ((r.thomasonLeft h).map A.ι) := by
  let : Finite (DoubleSubdivisionPairs.Faces m) := finite_nonemptyFiniteChains _
  let S := DoubleSubdivisionPairs.oldFaces A
  let : Finite (NonemptyFiniteChains (DoubleSubdivisionPairs.Faces m)) :=
    finite_nonemptyFiniteChains _
  have wi : realizationWeakEquivalences
      (nerveMap (subposetInclusion (ChainSieve.old S)).monotone.functor) :=
    (DoubleSubdivisionPairs.map_property_iff (𝟭 SSet) realizationWeakEquivalences A).mp
      ((subdivision_twice_weak_iff A.ι).mpr hA)
  have wci : thomasonWeakEquivalences (n := n) h
      (r.reflect.map (h.posetMap (subposetInclusion (ChainSieve.old S)))) :=
    (r.finite_poset_map_weakEquivalence_iff h G t aw s g kq _).mpr wi
  have : Mono ((h.finiteStreetNerve (n+1)).map ((r.categorification h).map
      (nerveMap (subposetInclusion (ChainSieve.old S)).monotone.functor))) :=
    r.posetSieve_nerve_mono h s (ChainSieve.old S) (ChainSieve.old_lower S)
  change cobaseWeak (thomasonWeakEquivalences (n := n) h)
    ((r.categorification h).map (SSet.sd.map (SSet.sd.map A.ι)))
  apply (DoubleSubdivisionPairs.map_property_iff (r.categorification h)
    (cobaseWeak (thomasonWeakEquivalences (n := n) h)) A).mpr
  rw [cobaseWeak_iff]
  intro X Y a b j hp
  exact attachment_weak_of_nerve_comparison (h.finiteStreetNerve (n+1)) kq hp wci
    (r.finite_chain_attachment_comparison h G t aw s g kq S hp)

end FiniteReflectionInput

end

end Thomason.Construction

end

section

/-! # Proper combinatorial axioms from the explicit attachment geometry

The original boundary and horn generators satisfy the two local tests.
Their cellular closure and factorization properties are already constructed.
-/

namespace Thomason.Construction

open CategoryTheory CategoryTheory.MorphismProperty StrictOmegaCategory
open CobaseChangeCellularClosure FiniteSubsetAttachments

namespace NormalizedSimplexIdentities

variable (h : NormalizedSimplexIdentities) [StrictColimitsInput]

/-- The literal generating boundaries universally preserve Street weak maps. -/
theorem imageBoundaries_universal
    (G : RightGrayInput h) (aw : SimplexComplex.AlexanderWhitneyInput h)
    (s : PublishedPosetSieveInput h) (g : PublishedSimplicialGluingInput)
    (kq : KanQuillenPublishedInput.{0}) :
    imageBoundaries h.thomasonLeft ≤ universalWeakPreserving h.streetWeakEquivalences := by
  rw [imageBoundaries, ofHoms_le_iff]
  intro m
  exact h.subcomplex_attachment_universal G aw s g kq (SSet.boundary m)

/-- Every individual generating horn attachment is a Street weak equivalence. -/
theorem imageHorns_pushouts_weak
    (G : RightGrayInput h) (aw : SimplexComplex.AlexanderWhitneyInput h)
    (s : PublishedPosetSieveInput h) (g : PublishedSimplicialGluingInput)
    (kq : KanQuillenPublishedInput.{0}) :
    (imageHorns h.thomasonLeft).pushouts ≤ h.streetWeakEquivalences := by
  have hi : imageHorns h.thomasonLeft ≤ cobaseWeak h.streetWeakEquivalences := by
    rw [imageHorns, ofHoms_le_iff]
    intro p
    exact h.subcomplex_attachment_acyclic G aw s g kq (SSet.horn (p.1+1) p.2)
      (realization_horn_weak p.2)
  exact (pushouts_le_iff.mpr hi).trans (SimultaneousAttachments.cobaseWeak_le _)

/-- The proper combinatorial structure is proved directly from the actual
horn and boundary geometry, with no abstract transfer input. -/
theorem geometric_model_axioms
    (G : RightGrayInput h) (aw : SimplexComplex.AlexanderWhitneyInput h)
    (s : PublishedPosetSieveInput h) (g : PublishedSimplicialGluingInput)
    (kq : KanQuillenPublishedInput.{0}) :
    ProperCombinatorialAxioms StrictOmegaCategory.{0} h.streetWeakEquivalences h.thomasonFibrations :=
  h.properCombinatorialAxioms_of_individual_attachments
    (h.imageBoundaries_universal G aw s g kq) (h.imageHorns_pushouts_weak G aw s g kq)

end NormalizedSimplexIdentities

namespace FiniteReflectionInput

variable {n : ℕ} (r : FiniteReflectionInput n)
  (h : NormalizedSimplexIdentities) [StrictColimitsInput]

include r

/-- The literal finite-dimensional generating boundary test. -/
theorem imageBoundaries_universal
    (G : RightGrayInput h) (t : GrayTruncationInput G)
    (aw : SimplexComplex.AlexanderWhitneyInput h)
    (s : PublishedPosetSieveInput h) (g : PublishedSimplicialGluingInput)
    (kq : KanQuillenPublishedInput.{0}) :
    imageBoundaries (r.thomasonLeft h) ≤
      universalWeakPreserving (thomasonWeakEquivalences (n := n) h) := by
  rw [imageBoundaries, ofHoms_le_iff]
  intro m
  exact r.subcomplex_attachment_universal h G t aw s g kq (SSet.boundary m)

/-- Every original finite-dimensional generating horn attachment is weak. -/
theorem imageHorns_pushouts_weak
    (G : RightGrayInput h) (t : GrayTruncationInput G)
    (aw : SimplexComplex.AlexanderWhitneyInput h)
    (s : PublishedPosetSieveInput h) (g : PublishedSimplicialGluingInput)
    (kq : KanQuillenPublishedInput.{0}) :
    (imageHorns (r.thomasonLeft h)).pushouts ≤ thomasonWeakEquivalences (n := n) h := by
  have hi : imageHorns (r.thomasonLeft h) ≤ cobaseWeak (thomasonWeakEquivalences (n := n) h) := by
    rw [imageHorns, ofHoms_le_iff]
    intro p
    exact r.subcomplex_attachment_acyclic h G t aw s g kq (SSet.horn (p.1+1) p.2)
      (realization_horn_weak p.2)
  exact (pushouts_le_iff.mpr hi).trans (SimultaneousAttachments.cobaseWeak_le _)

/-- The actual proper combinatorial axioms in each positive finite dimension. -/
theorem geometric_model_axioms
    (G : RightGrayInput h) (t : GrayTruncationInput G)
    (aw : SimplexComplex.AlexanderWhitneyInput h)
    (s : PublishedPosetSieveInput h) (g : PublishedSimplicialGluingInput)
    (kq : KanQuillenPublishedInput.{0}) :
    ProperCombinatorialAxioms (Truncated.{0} (n+1))
      (thomasonWeakEquivalences (n := n) h) (thomasonFibrations (n := n) h) :=
  r.properCombinatorialAxioms_of_individual_attachments h
    (r.imageBoundaries_universal h G t aw s g kq) (r.imageHorns_pushouts_weak h G t aw s g kq)

end FiniteReflectionInput

end Thomason.Construction

end

section

/-! # The complete main theorem after explicit transfer and localization

The right Gray interval construction and its finite truncation
compatibility imply transfer and localization through boundary and horn
attachments and the adjunction units.
-/

namespace Thomason.Construction

namespace NormalizedSimplexIdentities

variable (h : NormalizedSimplexIdentities) [StrictColimitsInput]

noncomputable def main_from_gray
    (G : RightGrayInput h) (aw : SimplexComplex.AlexanderWhitneyInput h)
    (s : PublishedPosetSieveInput h) (g : PublishedSimplicialGluingInput)
    (kq : KanQuillenPublishedInput.{0}) :
    ThomasonModelResult h.thomasonLeft h.streetNerve kq canonicalExtension_weak where
  axioms := h.geometric_model_axioms G aw s g kq
  adjunction := h.thomasonAdjunction
  boundaryLifting := h.thomason_trivialFibrations_eq_generating_rlp kq canonicalExtension_weak
  hornLifting := h.thomasonFibrations_eq_generating_rlp
  derivedEquivalence := h.thomason_localized_equivalence kq
    (h.geometric_model_axioms G aw s g kq) (h.unit_finite_poset G aw s g kq)

end NormalizedSimplexIdentities

namespace FiniteReflectionInput

variable {n : ℕ} (r : FiniteReflectionInput n)
  (h : NormalizedSimplexIdentities) [StrictColimitsInput]

noncomputable def main_from_gray
    (G : RightGrayInput h) (t : GrayTruncationInput G)
    (aw : SimplexComplex.AlexanderWhitneyInput h)
    (s : PublishedPosetSieveInput h) (g : PublishedSimplicialGluingInput)
    (kq : KanQuillenPublishedInput.{0}) :
    ThomasonModelResult (r.thomasonLeft h) (h.finiteStreetNerve (n+1)) kq canonicalExtension_weak where
  axioms := r.geometric_model_axioms h G t aw s g kq
  adjunction := r.thomasonAdjunction h
  boundaryLifting := r.thomason_trivialFibrations_eq_generating_rlp h kq canonicalExtension_weak
  hornLifting := r.thomasonFibrations_eq_generating_rlp h
  derivedEquivalence := r.thomason_localized_equivalence h kq
    (r.geometric_model_axioms h G t aw s g kq) (r.unit_finite_poset h G t aw s g kq)

end FiniteReflectionInput

/-- The omega and positive finite theorem family assuming
Ara--Maltsiniotis's right Gray construction and Proposition A.29. -/
theorem main_with_two_published_inputs
    (G : RightGrayInput normalizedSimplexIdentities) (t : GrayTruncationInput G) :
    Nonempty (ThomasonModelResult normalizedSimplexIdentities.thomasonLeft
      normalizedSimplexIdentities.streetNerve constructedKanQuillenInput canonicalExtension_weak) ∧
      ∀ n, Nonempty (ThomasonModelResult
        ((constructedFiniteReflection n).thomasonLeft normalizedSimplexIdentities)
        (normalizedSimplexIdentities.finiteStreetNerve (n+1))
        constructedKanQuillenInput canonicalExtension_weak) := by
  let h := normalizedSimplexIdentities
  let aw := SimplexComplex.alexanderWhitneyInput h
  let s := h.constructedOmegaPosetSieveInput.allDimensions
  let g := constructedSimplicialGluingUnconditional
  exact ⟨⟨h.main_from_gray G aw s g constructedKanQuillenInput⟩,
    fun n => ⟨(constructedFiniteReflection n).main_from_gray h G t aw s g constructedKanQuillenInput⟩⟩

end Thomason.Construction

end

section

/-! # Thomason model structures in every strict higher dimension

The right interval construction and its truncation compatibility give
the proper combinatorial model structures in omega and every positive
finite dimension.
-/

namespace Thomason.Construction

/-- Proper combinatorial Thomason model structures and derived equivalences
for strict omega categories and every positive finite dimension. -/
theorem thomason_model_structures_all_dimensions :
    Nonempty (ThomasonModelResult normalizedSimplexIdentities.thomasonLeft
      normalizedSimplexIdentities.streetNerve constructedKanQuillenInput canonicalExtension_weak) ∧
      ∀ n, Nonempty (ThomasonModelResult
        ((constructedFiniteReflection n).thomasonLeft normalizedSimplexIdentities)
        (normalizedSimplexIdentities.finiteStreetNerve (n+1))
        constructedKanQuillenInput canonicalExtension_weak) :=
  main_with_two_published_inputs normalizedSimplexIdentities.constructedRightGrayInput
    normalizedSimplexIdentities.constructedRightGrayTruncation

end Thomason.Construction

end

section

/-!
# Thomason structures in every strict higher dimension

Couniversality of Street weak equivalences follows from finite
poset deletion and the resulting pushout squares of Street nerves.
-/

open CategoryTheory

namespace Thomason.Construction

universe u

variable {E : Type u} [PartialOrder E] [Finite E] {A : Set E}

/-- The finite deletion step in the couniversality proof gives an actual
two-piece cover of the ordinary nerve. This is the ordinary-nerve side of
the map of spans in Section 5 of the manuscript. -/
theorem finite_deletion_nerve_cover (R : SieveRetraction A)
    (hne : (Aᶜ).Nonempty)
    (hgreatest : ¬ ∃ x, SieveRetraction.GreatestNew (A := A) x) :
    ∃ x y : E, x ∉ A ∧ y ∉ A ∧ x ≠ y ∧
      fullSubposetComplex {e : E | e ≠ x} ⊔
        fullSubposetComplex {e : E | e ≠ y} = ⊤ := by
  obtain ⟨x, y, hx, hy, hxy, hS, hT, _, _, hcover⟩ :=
    R.finite_two_sieve_cover hne hgreatest
  exact ⟨x, y, hx, hy, hxy, sieve_nerve_cover hS hT hcover⟩

/-- The same deletion step is a pushout square in actual simplicial sets. -/
theorem finite_deletion_nerve_pushout (R : SieveRetraction A)
    (hne : (Aᶜ).Nonempty)
    (hgreatest : ¬ ∃ x, SieveRetraction.GreatestNew (A := A) x) :
    ∃ (S T : Set E), A ⊆ S ∧ A ⊆ T ∧ IsLowerSet S ∧ IsLowerSet T ∧
      IsPushout
        (SSet.Subcomplex.homOfLE (show fullSubposetComplex (S ∩ T) ≤
          fullSubposetComplex S from fun _ _ h i => (h i).1))
        (SSet.Subcomplex.homOfLE (show fullSubposetComplex (S ∩ T) ≤
          fullSubposetComplex T from fun _ _ h i => (h i).2))
        (fullSubposetComplex S).ι (fullSubposetComplex T).ι := by
  obtain ⟨x, y, _, _, _, hS, hT, hAS, hAT, hcover⟩ :=
    R.finite_two_sieve_cover hne hgreatest
  exact ⟨{e | e ≠ x}, {e | e ≠ y}, hAS, hAT, hS, hT,
    sieve_nerve_isPushout hS hT hcover⟩

end Thomason.Construction

end

end OAI
