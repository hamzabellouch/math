import OAI.CategoryTheory.Thomason.Simplicial.ConstructedExtensionLocalizer
import OAI.CategoryTheory.Thomason.Simplicial.FiniteKanBaseChangeApproximation
import OAI.CategoryTheory.Thomason.Simplicial.FinitePosetUnitReduction
import OAI.CategoryTheory.Thomason.Simplicial.TruncatedLocalPresentability
import OAI.CategoryTheory.Thomason.Strict.StreetSingularWeakReflection
import OAI.CategoryTheory.Thomason.Strict.UnderlyingCategory
import OAI.CategoryTheory.Thomason.Transfer.FiveInputMainTheorem
import OAI.CategoryTheory.Thomason.Transfer.NonsingularFaceGluing
import OAI.CategoryTheory.Thomason.Transfer.ThomasonQuillenBridge
import OAI.CategoryTheory.Thomason.Transfer.WeakFactorizationRecognition
import Mathlib.CategoryTheory.Presentable.Presheaf
import Mathlib.CategoryTheory.Presentable.Type

namespace OAI

section

/-! # All dimensions with the actual Kan–Quillen input constructed

Acyclic Kan lifting for realization weak equivalences supplies the
Kan–Quillen axioms in the conditional strict-category theorem.
-/

namespace Thomason.Construction

theorem constructedKanQuillenInput : KanQuillenPublishedInput.{0} :=
  kanQuillenInput_of_acyclic_kan_lifting acyclicKanLifting_unconditional

/-- The complete main theorem family after discharging acyclic Kan lifting. -/
theorem main_with_four_published_inputs
    (G : RightGrayInput normalizedSimplexIdentities) (t : GrayTruncationInput G)
    (transfer : PublishedThomasonReduction normalizedSimplexIdentities)
    (loc : PublishedStreetLocalizationInput normalizedSimplexIdentities) :
    Nonempty (ThomasonModelResult normalizedSimplexIdentities.thomasonLeft
      normalizedSimplexIdentities.streetNerve constructedKanQuillenInput canonicalExtension_weak) ∧
      ∀ n, Nonempty (ThomasonModelResult
        ((constructedFiniteReflection n).thomasonLeft normalizedSimplexIdentities)
        (normalizedSimplexIdentities.finiteStreetNerve (n+1))
        constructedKanQuillenInput canonicalExtension_weak) :=
  main_with_five_published_inputs G t acyclicKanLifting_unconditional transfer loc

end Thomason.Construction

end

section

/-! # Properness of the actual Kan–Quillen weak equivalences

The gluing theorem proves stability under every pushout along a monomorphism.
For pullbacks along Kan fibrations, horn factorization reduces a weak
equivalence to the already constructed anodyne base changes and to a
boundary-lifting map. All weak equivalences below use actual realization.
-/

namespace Thomason.Construction

open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty
open SSet.modelCategoryQuillen

noncomputable section

/-- A boundary-lifting map remains weak under arbitrary base change. -/
theorem boundary_rlp_kanBaseChangeWeak {A B : SSet.{0}} (f : A ⟶ B)
    (hf : I.rlp f) : kanBaseChangeWeak f := by
  intro E p _
  exact boundary_rlp_weak _ (I.rlp.pullback_fst p f hf)

/-- Every actual realization weak equivalence is weak after arbitrary
base change along a Kan fibration. -/
theorem realization_weak_kanBaseChangeWeak {A B : SSet.{0}} (f : A ⟶ B)
    (hf : realizationWeakEquivalences f) : kanBaseChangeWeak f := by
  have := horn_weakFactorizationSystem
  let d := factorizationData SSet.anodyneExtensions J.rlp f
  have hiw : realizationWeakEquivalences d.i := anodyne_realization_weak d.i d.hi
  have hpw : realizationWeakEquivalences d.p := by
    apply realizationWeakEquivalences.of_precomp d.i d.p hiw
    simpa only [d.fac] using hf
  have hp : I.rlp d.p := acyclicKanLifting_unconditional d.p ⟨d.hp, hpw⟩
  rw [← d.fac]
  exact kanBaseChangeWeak_comp (anodyne_kanBaseChangeWeak d.i d.hi).2
    (boundary_rlp_kanBaseChangeWeak d.p hp)

/-- Right properness, retaining any specified cartesian square. -/
theorem realization_weak_of_kan_pullback {A B A' B' : SSet.{0}}
    {f : A ⟶ B} {f' : A' ⟶ B'} {a : A' ⟶ A} {p : B' ⟶ B}
    [HomotopicalAlgebra.Fibration p]
    (sq : IsPullback f' a p f) (hf : realizationWeakEquivalences f) :
    realizationWeakEquivalences f' :=
  (realization_weak_kanBaseChangeWeak f hf).of_isPullback sq

/-- The canonical pullback projection satisfies the same unrestricted test. -/
theorem kan_pullback_weak {A B E : SSet.{0}} (f : A ⟶ B)
    (hf : realizationWeakEquivalences f) (p : E ⟶ B)
    [HomotopicalAlgebra.Fibration p] :
    realizationWeakEquivalences (pullback.fst p f) :=
  realization_weak_kanBaseChangeWeak f hf E p inferInstance

/-- Actual realization weak equivalences are stable under all base changes
along the horn-lifting class. -/
instance realizationWeakEquivalences_rightProper :
    realizationWeakEquivalences.{0}.IsStableUnderBaseChangeAgainst J.rlp where
  isStableUnderBaseChangeAlong {_ _} p hp := by
    have : HomotopicalAlgebra.Fibration p := (fibration_iff p).mpr hp
    exact ⟨fun sq hf => realization_weak_of_kan_pullback sq.flip hf⟩

/-- Left properness, retaining any specified cocartesian square. -/
theorem realization_weak_pushout_mono {A B C P : SSet.{0}}
    {i : A ⟶ B} {f : A ⟶ C} {b : B ⟶ P} {j : C ⟶ P}
    [Mono i] (sq : IsPushout i f b j) (hf : realizationWeakEquivalences f) :
    realizationWeakEquivalences b := by
  have top : IsPushout i (𝟙 A) (𝟙 B) i := IsPushout.of_id_snd
  exact constructedSimplicialGluingUnconditional.glue top sq (𝟙 A) (𝟙 B) f b
    (by simp) (by simp) (by simp) sq.w
    (realizationWeakEquivalences.id_mem _) (realizationWeakEquivalences.id_mem _) hf

/-- The canonical pushout of a weak equivalence along any monomorphism is weak. -/
theorem mono_pushout_weak {A B C : SSet.{0}} (i : A ⟶ B) [Mono i]
    (f : A ⟶ C) (hf : realizationWeakEquivalences f) :
    realizationWeakEquivalences (pushout.inl i f) :=
  realization_weak_pushout_mono (IsPushout.of_hasPushout i f) hf

/-- Actual realization weak equivalences are stable under all cobase changes
along monomorphisms. -/
instance realizationWeakEquivalences_leftProper :
    realizationWeakEquivalences.{0}.IsStableUnderCobaseChangeAgainst
      (monomorphisms SSet.{0}) where
  isStableUnderCobaseChangeAlong {_ _} i hi := by
    have : Mono i := hi
    exact ⟨fun sq hf => realization_weak_pushout_mono sq hf⟩

end

end Thomason.Construction

end

section

/-! # The constructed proper combinatorial Kan–Quillen model axioms

This packages the actual weak equivalences, horn fibrations, boundary
factorization, unrestricted properness and presheaf local presentability.
It has no published-input parameters.
-/

namespace Thomason.Construction

open CategoryTheory CategoryTheory.MorphismProperty
open SSet.modelCategoryQuillen

/-- The lifting definition of cofibration agrees with monomorphisms for
the actual realization weak equivalences and horn fibrations. -/
theorem kanQuillenCofibrations_eq_monomorphisms :
    (J.rlp ⊓ realizationWeakEquivalences.{0}).llp = monomorphisms SSet.{0} := by
  rw [← boundary_class_of_acyclic_kan_lifting acyclicKanLifting_unconditional]
  exact boundary_left_class

/-- All the prescribed proper combinatorial model axioms on simplicial
sets, constructed without an assumed model structure or properness theorem. -/
theorem kanQuillenProperCombinatorialAxioms :
    ProperCombinatorialAxioms SSet.{0} realizationWeakEquivalences J.rlp where
  finiteLimits := inferInstance
  finiteColimits := inferInstance
  locallyPresentable := inferInstance
  cofibrationFactorization := by
    rw [kanQuillenCofibrations_eq_monomorphisms]
    exact (kanQuillenInput_of_acyclic_kan_lifting
      acyclicKanLifting_unconditional).cofibrationFactorization
  fibrationFactorization := by
    rw [kanQuillenCofibrations_eq_monomorphisms]
    exact (kanQuillenInput_of_acyclic_kan_lifting
      acyclicKanLifting_unconditional).fibrationFactorization
  leftProper := by
    rw [kanQuillenCofibrations_eq_monomorphisms]
    infer_instance
  rightProper := inferInstance

end Thomason.Construction

end

section

/-! # Right properness of the actual higher Thomason classes

The constructed right adjoints preserve pullbacks. Twice extension detects
the same realization weak equivalences as the Street nerve, so simplicial
right properness proves the required higher-category statement directly.
No higher model structure or abstract transfer theorem is used.
-/

namespace Thomason.Construction

open CategoryTheory CategoryTheory.Limits
open SSet.modelCategoryQuillen

universe v u

/-- Pullback preservation transfers the proved simplicial right-properness
statement to the exact inverse-image classes. -/
theorem realization_inverseImage_rightProper {C : Type u} [Category.{v} C]
    (R : C ⥤ SSet.{0}) [PreservesLimitsOfShape WalkingCospan R] :
    (realizationWeakEquivalences.inverseImage R).IsStableUnderBaseChangeAgainst
      (J.rlp.inverseImage R) where
  isStableUnderBaseChangeAlong {_ _} p hp := by
    have : HomotopicalAlgebra.Fibration (R.map p) := (fibration_iff _).mpr hp
    refine ⟨fun sq hf => ?_⟩
    exact realization_weak_of_kan_pullback (R.map_isPullback sq.flip) hf

namespace NormalizedSimplexIdentities

variable (h : NormalizedSimplexIdentities)

/-- Twice extension does not change the Street weak-equivalence class. -/
theorem streetWeakEquivalences_eq_thomasonRight :
    h.streetWeakEquivalences = realizationWeakEquivalences.inverseImage h.thomasonRight := by
  apply CategoryTheory.MorphismProperty.ext
  intro A B f
  change realizationWeakEquivalences (h.streetNerve.map f) ↔
    realizationWeakEquivalences (SSet.ex.map (SSet.ex.map (h.streetNerve.map f)))
  exact (realization_ex_twice_iff canonicalExtension_weak (h.streetNerve.map f)).symm

/-- All pullbacks of Street weak equivalences along the prescribed Thomason
fibrations are Street weak equivalences, in omega dimension. -/
theorem thomason_rightProper :
    h.streetWeakEquivalences.IsStableUnderBaseChangeAgainst h.thomasonFibrations := by
  let : PreservesLimits h.thomasonRight := h.thomasonAdjunction.rightAdjoint_preservesLimits
  rw [h.streetWeakEquivalences_eq_thomasonRight]
  exact realization_inverseImage_rightProper h.thomasonRight

end NormalizedSimplexIdentities

namespace FiniteReflectionInput

variable {n : ℕ} (r : FiniteReflectionInput n) (h : NormalizedSimplexIdentities)

theorem thomasonWeakEquivalences_eq_thomasonRight :
    thomasonWeakEquivalences (n := n) h =
      realizationWeakEquivalences.inverseImage (thomasonRight (n := n) h) := by
  apply CategoryTheory.MorphismProperty.ext
  intro A B f
  change realizationWeakEquivalences ((h.finiteStreetNerve (n + 1)).map f) ↔
    realizationWeakEquivalences
      (SSet.ex.map (SSet.ex.map ((h.finiteStreetNerve (n + 1)).map f)))
  exact (realization_ex_twice_iff canonicalExtension_weak
    ((h.finiteStreetNerve (n + 1)).map f)).symm

include r in
/-- The same actual right-properness statement holds in every positive
finite dimension, using the specified reflection adjunction. -/
theorem thomason_rightProper :
    (thomasonWeakEquivalences (n := n) h).IsStableUnderBaseChangeAgainst
      (thomasonFibrations (n := n) h) := by
  let : PreservesLimits (thomasonRight (n := n) h) :=
    (r.thomasonAdjunction h).rightAdjoint_preservesLimits
  rw [thomasonWeakEquivalences_eq_thomasonRight h]
  exact realization_inverseImage_rightProper (thomasonRight (n := n) h)

end FiniteReflectionInput

/-- In finite dimension the reflection used above is the constructed
intelligent truncation, so there is no reflection hypothesis. -/
theorem finite_thomason_rightProper (h : NormalizedSimplexIdentities) (n : ℕ) :
    (FiniteReflectionInput.thomasonWeakEquivalences (n := n) h).IsStableUnderBaseChangeAgainst
      (FiniteReflectionInput.thomasonFibrations (n := n) h) :=
  (constructedFiniteReflection n).thomason_rightProper h

end Thomason.Construction

end

section

/-! # The two actual Thomason generating weak factorization systems

The literal images of the boundary and horn families are small. Their
right lifting classes agree with the existing adjunction-defined classes,
including the arrow-isomorphism closure in `MorphismProperty.map`.
No acyclicity assertion for higher-category horn attachments is used.
-/

namespace Thomason.Construction

open CategoryTheory CategoryTheory.Limits
open SSet.modelCategoryQuillen
open scoped Simplicial

universe u

section Adjunction

variable {C : Type u} [Category.{0} C] [IsLocallyPresentable.{0} C]
    {L : SSet.{0} ⥤ C} {R : C ⥤ SSet.{0}} (adj : L ⊣ R)

/-- The small family consists of the literal images of simplex boundaries. -/
noncomputable def imageBoundaries (L : SSet.{0} ⥤ C) : MorphismProperty C :=
  .ofHoms (fun n : ℕ => L.map ∂Δ[n].ι)

/-- A single countable index type packages the literal images of all horns. -/
noncomputable def imageHorns (L : SSet.{0} ⥤ C) : MorphismProperty C :=
  .ofHoms (fun p : Σ n : ℕ, Fin (n + 2) => L.map Λ[p.1 + 1, p.2].ι)

include adj

omit [IsLocallyPresentable.{0} C] in
theorem imageBoundaries_rlp : (imageBoundaries L).rlp = I.rlp.inverseImage R := by
  apply MorphismProperty.ext
  intro X Y p
  constructor
  · intro hp A B i hi
    obtain ⟨n⟩ := hi
    exact (adj.hasLiftingProperty_iff _ p).mp (hp _ ⟨n⟩)
  · intro hp A B i hi
    obtain ⟨n⟩ := hi
    exact (adj.hasLiftingProperty_iff _ p).mpr (hp _ ⟨n⟩)

omit [IsLocallyPresentable.{0} C] in
theorem imageHorns_rlp : (imageHorns L).rlp = J.rlp.inverseImage R := by
  apply MorphismProperty.ext
  intro X Y p
  constructor
  · intro hp A B i hi
    simp only [J, MorphismProperty.iSup_iff] at hi
    obtain ⟨n, ⟨k⟩⟩ := hi
    have hm : imageHorns L (L.map Λ[n + 1, k].ι) := by
      change (MorphismProperty.ofHoms
        (fun q : Σ m : ℕ, Fin (m + 2) => L.map Λ[q.1 + 1, q.2].ι)) _
      exact MorphismProperty.ofHoms.mk (⟨n, k⟩ : Σ m : ℕ, Fin (m + 2))
    exact (adj.hasLiftingProperty_iff _ p).mp (hp _ hm)
  · intro hp A B i hi
    obtain ⟨⟨n, k⟩⟩ := hi
    apply (adj.hasLiftingProperty_iff _ p).mpr
    exact hp _ (horn_ι_mem_J (n + 1) k)

theorem boundaryInverseImage_weakFactorizationSystem :
    MorphismProperty.IsWeakFactorizationSystem
      (I.rlp.inverseImage R).llp (I.rlp.inverseImage R) := by
  rw [← imageBoundaries_rlp adj]
  exact smallFamily_weakFactorizationSystem (fun n : ℕ => L.map ∂Δ[n].ι)

theorem hornInverseImage_weakFactorizationSystem :
    MorphismProperty.IsWeakFactorizationSystem
      (J.rlp.inverseImage R).llp (J.rlp.inverseImage R) := by
  rw [← imageHorns_rlp adj]
  exact smallFamily_weakFactorizationSystem
    (fun p : Σ n : ℕ, Fin (n + 2) => L.map Λ[p.1 + 1, p.2].ι)

end Adjunction

namespace NormalizedSimplexIdentities

variable (h : NormalizedSimplexIdentities)

/-- The prescribed trivial fibrations and their left lifting class form
the first Thomason weak factorization system unconditionally. -/
theorem thomason_cofibrationFactorization :
    MorphismProperty.IsWeakFactorizationSystem
      (h.thomasonFibrations ⊓ h.streetWeakEquivalences).llp
      (h.thomasonFibrations ⊓ h.streetWeakEquivalences) := by
  rw [h.thomason_trivialFibrations_eq_boundary_lifting
    (kanQuillenInput_of_acyclic_kan_lifting acyclicKanLifting_unconditional)
    canonicalExtension_weak]
  exact boundaryInverseImage_weakFactorizationSystem h.thomasonAdjunction

/-- The higher horn-generated left lifting class and prescribed fibrations
form a weak factorization system, before identifying that left class as weak. -/
theorem thomason_hornFactorization :
    MorphismProperty.IsWeakFactorizationSystem
      h.thomasonFibrations.llp h.thomasonFibrations :=
  hornInverseImage_weakFactorizationSystem h.thomasonAdjunction

end NormalizedSimplexIdentities

namespace FiniteReflectionInput

variable {n : ℕ} (r : FiniteReflectionInput n) (h : NormalizedSimplexIdentities)

include r

theorem thomason_cofibrationFactorization :
    MorphismProperty.IsWeakFactorizationSystem
      (thomasonFibrations (n := n) h ⊓ thomasonWeakEquivalences (n := n) h).llp
      (thomasonFibrations (n := n) h ⊓ thomasonWeakEquivalences (n := n) h) := by
  rw [r.thomason_trivialFibrations_eq_generating_rlp h
    (kanQuillenInput_of_acyclic_kan_lifting acyclicKanLifting_unconditional)
    canonicalExtension_weak,
    thomasonGeneratingCofibrations, rlp_map_eq_inverseImage (r.thomasonAdjunction h)]
  exact boundaryInverseImage_weakFactorizationSystem (r.thomasonAdjunction h)

theorem thomason_hornFactorization :
    MorphismProperty.IsWeakFactorizationSystem
      (thomasonFibrations (n := n) h).llp (thomasonFibrations (n := n) h) :=
  hornInverseImage_weakFactorizationSystem (r.thomasonAdjunction h)

end FiniteReflectionInput

end Thomason.Construction

end

end OAI
