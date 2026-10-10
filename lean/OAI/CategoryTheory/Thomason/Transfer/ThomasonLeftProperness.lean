import OAI.CategoryTheory.Thomason.Simplicial.CobaseChangeCellularClosure
import OAI.CategoryTheory.Thomason.Simplicial.TruncatedLocalPresentability
import OAI.CategoryTheory.Thomason.Transfer.FiniteCosieveAttachmentComparison
import OAI.CategoryTheory.Thomason.Transfer.SimplicialRangeGluing
import OAI.CategoryTheory.Thomason.Transfer.StreetLocalizationFromModel
import OAI.CategoryTheory.Thomason.Transfer.ThomasonQuillenBridge
import OAI.CategoryTheory.Thomason.Transfer.ThomasonSmallObject

namespace OAI

section

/-! # Weak preservation from the actual nerve attachment comparison -/

namespace Thomason.Construction

open CategoryTheory CategoryTheory.Limits
open CobaseChangeCellularClosure

universe u

variable {C : Type u} [Category.{0} C] [HasColimitsOfSize.{0,0} C]
  (N : C ⥤ SSet.{0}) (g : PublishedSimplicialGluingInput)
  (kq : KanQuillenPublishedInput.{0})

omit [HasColimitsOfSize.{0,0} C] in
include kq in
/-- A weak attaching nerve and the actual weak comparison give a weak
attachment in the original category. -/
theorem attachment_weak_of_nerve_comparison
    {A B X Y : C} {i : A ⟶ B} {a : A ⟶ X} {b : B ⟶ Y} {j : X ⟶ Y}
    (hp : IsPushout i a b j) [Mono (N.map i)]
    (wi : realizationWeakEquivalences (N.map i))
    (wc : realizationWeakEquivalences (nervePushoutComparison N hp)) :
    realizationWeakEquivalences (N.map j) := by
  have := kq.twoOutOfThree
  have winc := kq.pushout_weakEquivalence (IsPushout.of_hasPushout (N.map i) (N.map a)) wi
  have hw := realizationWeakEquivalences.comp_mem _ _ winc wc
  simpa only [nervePushoutComparison, pushout.inr_desc] using hw

include g kq in
/-- Weak nerve comparisons for all attachments imply universal preservation
of weak equivalences. This is the local geometric input to left properness. -/
theorem universalWeakPreserving_of_nerve_comparisons
    {A B : C} (i : A ⟶ B) [Mono (N.map i)]
    (hcomp : ∀ {X Y : C} {a : A ⟶ X} {b : B ⟶ Y} {j : X ⟶ Y}
      (hp : IsPushout i a b j), realizationWeakEquivalences (nervePushoutComparison N hp)) :
    universalWeakPreserving (realizationWeakEquivalences.inverseImage N) i := by
  have := kq.twoOutOfThree
  apply of_comparison_weak (realizationWeakEquivalences.inverseImage N) i
  intro X Y a w hw
  let P := pushout (N.map i) (N.map a)
  let Q := pushout (N.map i) (N.map (a ≫ w))
  let d : P ⟶ Q := pushout.desc (pushout.inl (N.map i) (N.map (a ≫ w)))
    (N.map w ≫ pushout.inr (N.map i) (N.map (a ≫ w))) (by
      exact (show N.map i ≫ pushout.inl (N.map i) (N.map (a ≫ w)) =
        N.map (a ≫ w) ≫ pushout.inr (N.map i) (N.map (a ≫ w)) from pushout.condition).trans
        ((congrArg (fun f => f ≫ pushout.inr (N.map i) (N.map (a ≫ w)))
          (N.map_comp a w)).trans (Category.assoc _ _ _)))
  have wd : realizationWeakEquivalences d := by
    apply g.glue (IsPushout.of_hasPushout (N.map i) (N.map a))
      (IsPushout.of_hasPushout (N.map i) (N.map (a ≫ w)))
      (𝟙 _) (𝟙 _) (N.map w) d
    · simp
    · simp [N.map_comp]
    · exact (pushout.inl_desc _ _ _).trans (Category.id_comp _).symm
    · exact pushout.inr_desc _ _ _
    · exact realizationWeakEquivalences.id_mem _
    · exact realizationWeakEquivalences.id_mem _
    · exact hw
  have he : d ≫ nervePushoutComparison N (IsPushout.of_hasPushout i (a ≫ w)) =
      nervePushoutComparison N (IsPushout.of_hasPushout i a) ≫ N.map (comparison i a w) := by
    apply pushout.hom_ext
    · simp only [d, pushout.inl_desc_assoc, nervePushoutComparison_inl]
      rw [← Category.assoc, nervePushoutComparison_inl, ← N.map_comp, inl_comparison]
    · simp only [d, pushout.inr_desc_assoc]
      rw [Category.assoc, nervePushoutComparison_inr,
        ← Category.assoc, nervePushoutComparison_inr]
      exact ((N.map_comp (pushout.inr i a) (comparison i a w)).symm.trans
        ((congrArg N.map (inr_comparison i a w)).trans
          (N.map_comp w (pushout.inr i (a ≫ w))))).symm
  apply realizationWeakEquivalences.of_precomp
    (nervePushoutComparison N (IsPushout.of_hasPushout i a)) _
    (hcomp (IsPushout.of_hasPushout i a))
  rw [← he]
  exact realizationWeakEquivalences.comp_mem _ _ wd
    (hcomp (IsPushout.of_hasPushout i (a ≫ w)))

end Thomason.Construction

end

section

/-! # Universal weak preservation for actual finite face-chain attachments -/

namespace Thomason.Construction

open CategoryTheory PartialOrder StrictOmegaCategory CobaseChangeCellularClosure

namespace NormalizedSimplexIdentities

variable (h : NormalizedSimplexIdentities) [StrictColimitsInput]

theorem finite_chain_attachment_universal
    (G : RightGrayInput h) (aw : SimplexComplex.AlexanderWhitneyInput h)
    (s : PublishedPosetSieveInput h) (g : PublishedSimplicialGluingInput)
    (kq : KanQuillenPublishedInput.{0})
    {P : Type} [PartialOrder P] [Finite P] (S : Set P) :
    universalWeakPreserving h.streetWeakEquivalences
      (h.posetMap (subposetInclusion (ChainSieve.old S))) := by
  let : Finite (NonemptyFiniteChains P) := finite_nonemptyFiniteChains P
  have := s.omega_nerve_mono (ChainSieve.old S) (ChainSieve.old_lower S)
  exact universalWeakPreserving_of_nerve_comparisons h.streetNerve g kq _
    (fun hp => h.finite_chain_attachment_comparison G aw s g kq S hp)

end NormalizedSimplexIdentities

namespace FiniteReflectionInput

variable {n : ℕ} (r : FiniteReflectionInput n)
  (h : NormalizedSimplexIdentities) [StrictColimitsInput]

theorem finite_chain_attachment_universal
    (G : RightGrayInput h) (t : GrayTruncationInput G)
    (aw : SimplexComplex.AlexanderWhitneyInput h)
    (s : PublishedPosetSieveInput h) (g : PublishedSimplicialGluingInput)
    (kq : KanQuillenPublishedInput.{0})
    {P : Type} [PartialOrder P] [Finite P] (S : Set P) :
    universalWeakPreserving (thomasonWeakEquivalences (n := n) h)
      (r.reflect.map (h.posetMap (subposetInclusion (ChainSieve.old S)))) := by
  let : Finite (NonemptyFiniteChains P) := finite_nonemptyFiniteChains P
  have := r.posetSieve_nerve_mono h s (ChainSieve.old S) (ChainSieve.old_lower S)
  exact universalWeakPreserving_of_nerve_comparisons (h.finiteStreetNerve (n+1)) g kq _
    (fun hp => r.finite_chain_attachment_comparison h G t aw s g kq S hp)

end FiniteReflectionInput

end Thomason.Construction

end

section

/-! # Left properness and model axioms from individual attachments

The geometric criteria concern single generators: universal weak
preservation for boundary attachments and weak equivalence for horn
attachments. The small object argument extends them to cofibrations
and acyclic cofibrations.
-/

namespace Thomason.Construction

open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty
open CobaseChangeCellularClosure

namespace NormalizedSimplexIdentities

variable (h : NormalizedSimplexIdentities)

local instance : h.streetWeakEquivalences.IsMultiplicative := by
  change (realizationWeakEquivalences.inverseImage h.streetNerve).IsMultiplicative
  exact { toContainsIdentities := inferInstance, toIsStableUnderComposition := inferInstance }
local instance : h.streetWeakEquivalences.RespectsIso :=
  inferInstanceAs (realizationWeakEquivalences.inverseImage h.streetNerve).RespectsIso
local instance : h.streetWeakEquivalences.IsStableUnderRetracts :=
  inferInstanceAs (realizationWeakEquivalences.inverseImage h.streetNerve).IsStableUnderRetracts

theorem thomason_leftProper_of_individual_boundaries
    (hb : imageBoundaries h.thomasonLeft ≤ universalWeakPreserving h.streetWeakEquivalences) :
    h.streetWeakEquivalences.IsStableUnderCobaseChangeAgainst
      (h.thomasonFibrations ⊓ h.streetWeakEquivalences).llp := by
  rw [h.thomason_trivialFibrations_eq_boundary_lifting
    (kanQuillenInput_of_acyclic_kan_lifting acyclicKanLifting_unconditional)
    canonicalExtension_weak, ← imageBoundaries_rlp h.thomasonAdjunction]
  let : (imageBoundaries h.thomasonLeft).HasSmallObjectArgument.{0} :=
    smallFamily_hasSmallObjectArgument (fun n : ℕ => h.thomasonLeft.map (SSet.boundary n).ι)
  exact generated_left_preserves_weak (imageBoundaries h.thomasonLeft) h.streetWeakEquivalences hb

/-- The complete proper combinatorial axioms follow from the two individual
geometric attachment tests, with no abstract transfer theorem. -/
theorem properCombinatorialAxioms_of_individual_attachments
    (hb : imageBoundaries h.thomasonLeft ≤ universalWeakPreserving h.streetWeakEquivalences)
    (hj : (imageHorns h.thomasonLeft).pushouts ≤ h.streetWeakEquivalences) :
    ProperCombinatorialAxioms StrictOmegaCategory.{0} h.streetWeakEquivalences
      h.thomasonFibrations where
  finiteLimits := inferInstance
  finiteColimits := inferInstance
  locallyPresentable := inferInstance
  cofibrationFactorization := h.thomason_cofibrationFactorization
  fibrationFactorization := h.weakCofibration_factorization_of_individual_attachments hj
  leftProper := h.thomason_leftProper_of_individual_boundaries hb
  rightProper := h.thomason_rightProper

end NormalizedSimplexIdentities

namespace FiniteReflectionInput

variable {n : ℕ} (r : FiniteReflectionInput n) (h : NormalizedSimplexIdentities)

local instance : (thomasonWeakEquivalences (n := n) h).IsMultiplicative := by
  change (realizationWeakEquivalences.inverseImage (h.finiteStreetNerve (n+1))).IsMultiplicative
  exact { toContainsIdentities := inferInstance, toIsStableUnderComposition := inferInstance }
local instance : (thomasonWeakEquivalences (n := n) h).RespectsIso :=
  inferInstanceAs (realizationWeakEquivalences.inverseImage (h.finiteStreetNerve (n+1))).RespectsIso
local instance : (thomasonWeakEquivalences (n := n) h).IsStableUnderRetracts :=
  inferInstanceAs (realizationWeakEquivalences.inverseImage (h.finiteStreetNerve (n+1))).IsStableUnderRetracts

include r in
theorem thomason_leftProper_of_individual_boundaries
    (hb : imageBoundaries (thomasonLeft r h) ≤
      universalWeakPreserving (thomasonWeakEquivalences (n := n) h)) :
    (thomasonWeakEquivalences (n := n) h).IsStableUnderCobaseChangeAgainst
      (thomasonFibrations (n := n) h ⊓ thomasonWeakEquivalences (n := n) h).llp := by
  rw [r.thomason_trivialFibrations_eq_generating_rlp h
    (kanQuillenInput_of_acyclic_kan_lifting acyclicKanLifting_unconditional)
    canonicalExtension_weak,
    thomasonGeneratingCofibrations, rlp_map_eq_inverseImage (r.thomasonAdjunction h),
    ← imageBoundaries_rlp (r.thomasonAdjunction h)]
  let : (imageBoundaries (thomasonLeft r h)).HasSmallObjectArgument.{0} :=
    smallFamily_hasSmallObjectArgument
      (fun m : ℕ => (thomasonLeft r h).map (SSet.boundary m).ι)
  exact generated_left_preserves_weak (imageBoundaries (thomasonLeft r h))
    (thomasonWeakEquivalences (n := n) h) hb

include r in
/-- The same single-generator tests give the prescribed proper model axioms
in every positive finite dimension. -/
theorem properCombinatorialAxioms_of_individual_attachments
    (hb : imageBoundaries (thomasonLeft r h) ≤
      universalWeakPreserving (thomasonWeakEquivalences (n := n) h))
    (hj : (imageHorns (thomasonLeft r h)).pushouts ≤ thomasonWeakEquivalences (n := n) h) :
    ProperCombinatorialAxioms (StrictOmegaCategory.Truncated.{0} (n+1))
      (thomasonWeakEquivalences (n := n) h) (thomasonFibrations (n := n) h) where
  finiteLimits := inferInstance
  finiteColimits := inferInstance
  locallyPresentable := inferInstance
  cofibrationFactorization := r.thomason_cofibrationFactorization h
  fibrationFactorization := r.weakCofibration_factorization_of_individual_attachments h hj
  leftProper := r.thomason_leftProper_of_individual_boundaries h hb
  rightProper := r.thomason_rightProper h

end FiniteReflectionInput

end Thomason.Construction

end

end OAI
