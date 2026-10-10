import OAI.CategoryTheory.Thomason.Simplicial.LoopDimensionShift
import OAI.CategoryTheory.Thomason.Simplicial.SimplicialSpanFactorization
import OAI.CategoryTheory.Thomason.Simplicial.TruncatedLocalPresentability
import OAI.CategoryTheory.Thomason.Strict.StrictCompositeListReplacement
import OAI.CategoryTheory.Thomason.Transfer.FiniteEmptyAttachmentFibers
import OAI.CategoryTheory.Thomason.Transfer.ThomasonQuillenBridge
import OAI.CategoryTheory.Thomason.Transfer.WeakFactorizationRecognition
import Mathlib.CategoryTheory.Localization.LocalizerMorphism
import Mathlib.SetTheory.Cardinal.NatCard

namespace OAI

section

/-! # Couniversality for finite posets in omega dimension

The induction is over the ambient finite poset. The greatest-new case uses
the constructed stationary Gray prisms; otherwise two maximal deletions
and their intersection give three smaller arbitrary attachments. Their
actual full-fibre cover and the simplicial gluing bridge complete the step.
-/

namespace Thomason.Construction.NormalizedSimplexIdentities

open CategoryTheory CategoryTheory.Limits StrictOmegaCategory

variable (h : NormalizedSimplexIdentities) [StrictColimitsInput]

/-- Every categorified finite-poset sieve with a right-adjoint retraction is
an actual couniversal Street weak equivalence. No assumption on the target
or attaching functor is made. -/
theorem finite_poset_couniversal
    (G : RightGrayInput h) (aw : SimplexComplex.AlexanderWhitneyInput h)
    (s : PublishedPosetSieveInput h)
    (g : PublishedSimplicialGluingInput)
    (kq : KanQuillenPublishedInput.{0})
    {P : Type} [PartialOrder P] [Finite P] (A : Set P) (R : SieveRetraction A) :
    h.CouniversalStreetWeakEquivalence (h.posetMap (subposetInclusion A)) := by
  classical
  have main : ∀ k : ℕ, ∀ {P : Type} [PartialOrder P] [Finite P], Nat.card P ≤ k →
      ∀ (A : Set P) (R : SieveRetraction A),
        h.CouniversalStreetWeakEquivalence (h.posetMap (subposetInclusion A)) := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro P _ _ hcard A R
      by_cases hall : ∀ x, x ∈ A
      · have := h.posetMap_isIso_of_all A hall
        exact h.couniversal_of_isIso kq _
      by_cases hgreat : ∃ x, SieveRetraction.GreatestNew (A := A) x
      · obtain ⟨x, hx⟩ := hgreat
        exact h.greatestNew_couniversal R hx G aw kq
      have hne : Aᶜ.Nonempty := by
        obtain ⟨x, hx⟩ := not_forall.mp hall
        exact ⟨x, hx⟩
      obtain ⟨x, y, _, _, _, hU, hV, hAU, hAV, hcover⟩ := R.finite_two_sieve_cover hne hgreat
      have small (S : Set P) (hAS : A ⊆ S) (z : P) (hz : z ∉ S) :
          h.CouniversalStreetWeakEquivalence (h.posetMap (subposetInclusionWithin A S hAS)) := by
        have hc : Nat.card S < k := (Finite.card_subtype_lt hz).trans_le hcard
        have hw : h.CouniversalStreetWeakEquivalence
            (h.posetMap (subposetInclusion {e : S | e.val ∈ A})) :=
          ih (Nat.card S) hc (P := S) le_rfl {e : S | e.val ∈ A} (R.restrict S hAS)
        rw [← h.restrictedOldIso_fac A S hAS]
        intro X Y a b j hp
        exact h.couniversal_precompose_iso (h.posetMapIso (restrictedOldIso A S hAS)) _
          (fun hp' => hw hp') hp
      exact h.couniversal_of_two_sieve_cover s g kq A
        {e | e ≠ x} {e | e ≠ y} hU hV hAU hAV hcover
        (small _ hAU x (by simp)) (small _ hAV y (by simp))
        (small ({e : P | e ≠ x} ∩ {e : P | e ≠ y})
          (fun _e he => ⟨hAU he, hAV he⟩) x (by simp))
  intro X Y a b j hp
  exact main (Nat.card P) (P := P) le_rfl A R hp

/-- The finite-poset theorem applied to a specified actual attaching pushout. -/
theorem finite_poset_pushout_weakEquivalence
    (G : RightGrayInput h) (aw : SimplexComplex.AlexanderWhitneyInput h)
    (s : PublishedPosetSieveInput h)
    (g : PublishedSimplicialGluingInput)
    (kq : KanQuillenPublishedInput.{0})
    {P : Type} [PartialOrder P] [Finite P] (A : Set P) (R : SieveRetraction A)
    {X Y : StrictOmegaCategory.{0}} {a : h.categorification.obj (nerve A) ⟶ X}
    {b : h.categorification.obj (nerve P) ⟶ Y} {j : X ⟶ Y}
    (hp : IsPushout (h.posetMap (subposetInclusion A)) a b j) : h.streetWeakEquivalences j :=
  h.finite_poset_couniversal G aw s g kq A R hp

end Thomason.Construction.NormalizedSimplexIdentities

end

section

/-! # Finite-poset couniversality in every positive finite dimension

This repeats the cardinal induction in the actual finite category. Only
the Street-cover test is performed in the ambient omega-category.
-/

namespace Thomason.Construction

open CategoryTheory CategoryTheory.Limits StrictOmegaCategory

namespace NormalizedSimplexIdentities

variable (h : NormalizedSimplexIdentities) (n : ℕ)

/-- Renaming the finite attaching source preserves couniversality. -/
theorem finite_couniversal_precompose_iso {A A' B : Truncated.{0} (n + 1)}
    (e : A' ≅ A) (i : A ⟶ B) (hi : h.FiniteCouniversalStreetWeakEquivalence n i) :
    h.FiniteCouniversalStreetWeakEquivalence n (e.hom ≫ i) := by
  intro X Y a b j hp
  have hp' : IsPushout i (e.inv ≫ a) b j := hp.of_iso e (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by simp) (by simp) (by simp) (by simp)
  exact hi hp'

/-- A finite-category isomorphism remains a Street equivalence under attachment. -/
theorem finite_couniversal_of_isIso (kq : KanQuillenPublishedInput.{0})
    {A B : Truncated.{0} (n + 1)} (i : A ⟶ B) [IsIso (C := Truncated (n + 1)) i] :
    h.FiniteCouniversalStreetWeakEquivalence n i := by
  intro X Y a b j hp
  have := hp.isIso_inr_of_isIso
  have := kq.weakEquivalences_retracts
  exact realizationWeakEquivalences.of_isIso (h.streetNerve.map ((StrictOmegaCategory.inclusion (n + 1)).map j))

end NormalizedSimplexIdentities

namespace FiniteReflectionInput

variable {n : ℕ} (r : FiniteReflectionInput n)
  (h : NormalizedSimplexIdentities) [StrictColimitsInput]

/-- Every finite-poset sieve retraction is couniversally a Street weak
 equivalence in dimension `n + 1`, with arbitrary attaching maps and targets. -/
theorem finite_poset_couniversal
    (G : RightGrayInput h) (t : GrayTruncationInput G)
    (aw : SimplexComplex.AlexanderWhitneyInput h)
    (s : PublishedPosetSieveInput h)
    (g : PublishedSimplicialGluingInput)
    (kq : KanQuillenPublishedInput.{0})
    {P : Type} [PartialOrder P] [Finite P] (A : Set P) (R : SieveRetraction A) :
    h.FiniteCouniversalStreetWeakEquivalence n
      (r.reflect.map (h.posetMap (subposetInclusion A))) := by
  classical
  have main : ∀ k : ℕ, ∀ {P : Type} [PartialOrder P] [Finite P], Nat.card P ≤ k →
      ∀ (A : Set P) (R : SieveRetraction A),
        h.FiniteCouniversalStreetWeakEquivalence n
          (r.reflect.map (h.posetMap (subposetInclusion A))) := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro P _ _ hcard A R
      by_cases hall : ∀ x, x ∈ A
      · have := h.posetMap_isIso_of_all A hall
        exact h.finite_couniversal_of_isIso n kq _
      by_cases hgreat : ∃ x, SieveRetraction.GreatestNew (A := A) x
      · obtain ⟨x, hx⟩ := hgreat
        exact r.greatestNew_couniversal h R hx G t aw kq
      have hne : Aᶜ.Nonempty := by
        obtain ⟨x, hx⟩ := not_forall.mp hall
        exact ⟨x, hx⟩
      obtain ⟨x, y, _, _, _, hU, hV, hAU, hAV, hcover⟩ := R.finite_two_sieve_cover hne hgreat
      have small (S : Set P) (hAS : A ⊆ S) (z : P) (hz : z ∉ S) :
          h.FiniteCouniversalStreetWeakEquivalence n
            (r.reflect.map (h.posetMap (subposetInclusionWithin A S hAS))) := by
        have hc : Nat.card S < k := (Finite.card_subtype_lt hz).trans_le hcard
        have hw : h.FiniteCouniversalStreetWeakEquivalence n
            (r.reflect.map (h.posetMap (subposetInclusion {e : S | e.val ∈ A}))) :=
          ih (Nat.card S) hc (P := S) le_rfl {e : S | e.val ∈ A} (R.restrict S hAS)
        have he : (r.reflect.mapIso (h.posetMapIso (restrictedOldIso A S hAS))).hom ≫
            r.reflect.map (h.posetMap (subposetInclusion {e : S | e.val ∈ A})) =
            r.reflect.map (h.posetMap (subposetInclusionWithin A S hAS)) := by
          exact (r.reflect.map_comp _ _).symm.trans
            (congrArg r.reflect.map (h.restrictedOldIso_fac A S hAS))
        rw [← he]
        intro X Y a b j hp
        exact h.finite_couniversal_precompose_iso n
          (r.reflect.mapIso (h.posetMapIso (restrictedOldIso A S hAS))) _
          (fun hp' => hw hp') hp
      exact r.couniversal_of_two_sieve_cover h s g kq A
        {e | e ≠ x} {e | e ≠ y} hU hV hAU hAV hcover
        (small _ hAU x (by simp)) (small _ hAV y (by simp))
        (small ({e : P | e ≠ x} ∩ {e : P | e ≠ y})
          (fun _e he => ⟨hAU he, hAV he⟩) x (by simp))
  intro X Y a b j hp
  exact main (Nat.card P) (P := P) le_rfl A R hp

/-- The resulting bridge for a specified finite-dimensional pushout. -/
theorem finite_poset_pushout_weakEquivalence
    (G : RightGrayInput h) (t : GrayTruncationInput G)
    (aw : SimplexComplex.AlexanderWhitneyInput h)
    (s : PublishedPosetSieveInput h)
    (g : PublishedSimplicialGluingInput)
    (kq : KanQuillenPublishedInput.{0})
    {P : Type} [PartialOrder P] [Finite P] (A : Set P) (R : SieveRetraction A)
    {X Y : Truncated.{0} (n + 1)}
    {a : (r.categorification h).obj (nerve A) ⟶ X}
    {b : (r.categorification h).obj (nerve P) ⟶ Y} {j : X ⟶ Y}
    (hp : IsPushout (r.reflect.map (h.posetMap (subposetInclusion A))) a b j) :
    h.streetWeakEquivalences ((StrictOmegaCategory.inclusion (n + 1)).map j) :=
  r.finite_poset_couniversal h G t aw s g kq A R hp

end FiniteReflectionInput
end Thomason.Construction

end

section

/-! # The actual nerve-pushout comparison for retracting sieve attachments

A couniversal weak equivalence with monomorphic nerve gives a weak
comparison from the pushout of nerves to the nerve of the pushout. The
simplicial pushout leg is acyclic by the existing Kan--Quillen WFS.
-/

namespace Thomason.Construction

open CategoryTheory CategoryTheory.Limits StrictOmegaCategory

namespace KanQuillenPublishedInput

/-- Pushouts of monomorphic realization weak equivalences remain weak equivalences. -/
theorem pushout_weakEquivalence (kq : KanQuillenPublishedInput.{0})
    {A B X Y : SSet.{0}} {i : A ⟶ B} {a : A ⟶ X} {b : B ⟶ Y} {j : X ⟶ Y}
    (hp : IsPushout i a b j) [Mono i] (wi : realizationWeakEquivalences i) :
    realizationWeakEquivalences j := by
  have := kq.fibrationFactorization
  have hs : (MorphismProperty.monomorphisms SSet.{0} ⊓ realizationWeakEquivalences).IsStableUnderCobaseChange := by
    rw [← MorphismProperty.llp_eq_of_wfs
      (MorphismProperty.monomorphisms SSet.{0} ⊓ realizationWeakEquivalences) SSet.modelCategoryQuillen.J.rlp]
    infer_instance
  exact ((MorphismProperty.monomorphisms SSet.{0} ⊓ realizationWeakEquivalences).of_isPushout
    hp.flip ⟨inferInstance, wi⟩).2

end KanQuillenPublishedInput

section Comparison

variable {C : Type*} [Category* C] (N : C ⥤ SSet.{0})
  {A B X Y : C} {i : A ⟶ B} {a : A ⟶ X} {b : B ⟶ Y} {j : X ⟶ Y}

/-- The canonical comparison retains the two original structure maps. -/
noncomputable def nervePushoutComparison (hp : IsPushout i a b j) :
    pushout (N.map i) (N.map a) ⟶ N.obj Y :=
  pushout.desc (N.map b) (N.map j)
    ((N.map_comp i b).symm.trans ((congrArg N.map hp.w).trans (N.map_comp a j)))

/-- Once both attaching legs are weak, the canonical comparison is weak.
This applies to actual nerves and to arbitrary attaching maps. -/
theorem nervePushoutComparison_weakEquivalence (kq : KanQuillenPublishedInput.{0})
    (hp : IsPushout i a b j) [Mono (N.map i)]
    (wi : realizationWeakEquivalences (N.map i))
    (wj : realizationWeakEquivalences (N.map j)) :
    realizationWeakEquivalences (nervePushoutComparison N hp) := by
  have := kq.twoOutOfThree
  have winc := kq.pushout_weakEquivalence
    (IsPushout.of_hasPushout (N.map i) (N.map a)) wi
  apply realizationWeakEquivalences.of_precomp (pushout.inr (N.map i) (N.map a)) _ winc
  simpa only [nervePushoutComparison, pushout.inr_desc] using wj

end Comparison

namespace NormalizedSimplexIdentities

variable (h : NormalizedSimplexIdentities) [StrictColimitsInput]

/-- The comparison for every finite-poset sieve retraction in omega dimension. -/
theorem finite_poset_attachment_comparison
    (G : RightGrayInput h) (aw : SimplexComplex.AlexanderWhitneyInput h)
    (s : PublishedPosetSieveInput h)
    (g : PublishedSimplicialGluingInput)
    (kq : KanQuillenPublishedInput.{0})
    {P : Type} [PartialOrder P] [Finite P] (A : Set P) (R : SieveRetraction A)
    {X Y : StrictOmegaCategory.{0}} {a : h.categorification.obj (nerve A) ⟶ X}
    {b : h.categorification.obj (nerve P) ⟶ Y} {j : X ⟶ Y}
    (hp : IsPushout (h.posetMap (subposetInclusion A)) a b j) :
    realizationWeakEquivalences (nervePushoutComparison h.streetNerve hp) := by
  have := s.omega_nerve_mono A R.lower
  have hw : h.CouniversalStreetWeakEquivalence (h.posetMap (subposetInclusion A)) :=
    h.finite_poset_couniversal G aw s g kq A R
  have hid : IsPushout (h.posetMap (subposetInclusion A)) (𝟙 _) (𝟙 _)
      (h.posetMap (subposetInclusion A)) := IsPushout.of_id_snd
  exact nervePushoutComparison_weakEquivalence h.streetNerve kq hp (hw hid) (hw hp)

end NormalizedSimplexIdentities
namespace FiniteReflectionInput

variable {n : ℕ} (r : FiniteReflectionInput n)
  (h : NormalizedSimplexIdentities) [StrictColimitsInput]

/-- The original reflected sieve has monomorphic Street nerve. -/
theorem posetSieve_nerve_mono (s : PublishedPosetSieveInput h)
    {P : Type} [PartialOrder P] [Finite P] (A : Set P) (hA : IsLowerSet A) :
    Mono ((h.finiteStreetNerve (n + 1)).map (r.reflect.map (h.posetMap (subposetInclusion A)))) := by
  let e : (r.categorification h).obj (nerve A) ≅
      finiteLabelFiber (r.membershipLabel h A hA) 0 :=
    @asIso (Truncated (n + 1)) _ _ _ (r.posetFiberMap h A hA) (s.finite n r A hA)
  let e' := (StrictOmegaCategory.inclusion (n + 1)).mapIso e
  have he : (h.finiteStreetNerve (n + 1)).map (r.reflect.map (h.posetMap (subposetInclusion A))) =
      h.streetNerve.map e'.hom ≫ h.streetNerve.map (labelFiberInclusion (r.membershipLabel h A hA) 0) := by
    have hf : (StrictOmegaCategory.inclusion (n + 1)).map (r.reflect.map (h.posetMap (subposetInclusion A))) =
        e'.hom ≫ labelFiberInclusion (r.membershipLabel h A hA) 0 := by
      apply Hom.ext
      rfl
    exact (congrArg h.streetNerve.map hf).trans (h.streetNerve.map_comp _ _)
  have hm₁ : Mono (h.streetNerve.map e'.hom) := inferInstance
  have hm₂ : Mono (h.streetNerve.map (labelFiberInclusion (r.membershipLabel h A hA) 0)) := inferInstance
  rw [he]
  exact mono_comp' hm₁ hm₂

/-- The same canonical comparison is weak for finite-dimensional retracting attachments. -/
theorem finite_poset_attachment_comparison
    (G : RightGrayInput h) (t : GrayTruncationInput G)
    (aw : SimplexComplex.AlexanderWhitneyInput h)
    (s : PublishedPosetSieveInput h)
    (g : PublishedSimplicialGluingInput)
    (kq : KanQuillenPublishedInput.{0})
    {P : Type} [PartialOrder P] [Finite P] (A : Set P) (R : SieveRetraction A)
    {X Y : Truncated.{0} (n + 1)} {a : (r.categorification h).obj (nerve A) ⟶ X}
    {b : (r.categorification h).obj (nerve P) ⟶ Y} {j : X ⟶ Y}
    (hp : IsPushout (r.reflect.map (h.posetMap (subposetInclusion A))) a b j) :
    realizationWeakEquivalences (nervePushoutComparison (h.finiteStreetNerve (n + 1)) hp) := by
  have := r.posetSieve_nerve_mono h s A R.lower
  have hw : h.FiniteCouniversalStreetWeakEquivalence n
      (r.reflect.map (h.posetMap (subposetInclusion A))) :=
    r.finite_poset_couniversal h G t aw s g kq A R
  have hid : IsPushout (r.reflect.map (h.posetMap (subposetInclusion A))) (𝟙 _) (𝟙 _)
      (r.reflect.map (h.posetMap (subposetInclusion A))) := IsPushout.of_id_snd
  exact nervePushoutComparison_weakEquivalence (h.finiteStreetNerve (n + 1)) kq hp (hw hid) (hw hp)

end FiniteReflectionInput
end Thomason.Construction

end

section

/-! # Extending an attachment comparison across a cosieve cover

This is the pushout reassociation step used after the actual full-fibre
identifications. Only the comparison on the containing piece is needed.
-/

namespace Thomason.Construction

open CategoryTheory CategoryTheory.Limits

variable {C : Type*} [Category* C] (N : C ⥤ SSet.{0})

theorem nervePushoutComparison_weak_iff {A B X Y : C}
    {i i' : A ⟶ B} {a : A ⟶ X} {b : B ⟶ Y} {j : X ⟶ Y}
    (hi : i = i') (hp : IsPushout i a b j) (hp' : IsPushout i' a b j) :
    realizationWeakEquivalences (nervePushoutComparison N hp) ↔
      realizationWeakEquivalences (nervePushoutComparison N hp') := by
  subst i'
  rfl

theorem nervePushoutComparison_inl {A B X Y : C}
    {i : A ⟶ B} {a : A ⟶ X} {b : B ⟶ Y} {j : X ⟶ Y}
    (hp : IsPushout i a b j) :
    pushout.inl (N.map i) (N.map a) ≫ nervePushoutComparison N hp = N.map b :=
  pushout.inl_desc _ _ _

theorem nervePushoutComparison_inr {A B X Y : C}
    {i : A ⟶ B} {a : A ⟶ X} {b : B ⟶ Y} {j : X ⟶ Y}
    (hp : IsPushout i a b j) :
    pushout.inr (N.map i) (N.map a) ≫ nervePushoutComparison N hp = N.map j :=
  pushout.inr_desc _ _ _

/-- A weak comparison for the containing piece extends over a two-piece
cover when the other piece and the intersection stay unchanged. -/
theorem nervePushoutComparison_weak_of_cosieve_cover
    (g : PublishedSimplicialGluingInput)
    {A Z B T U X V Y : C}
    {i : A ⟶ Z} {u : Z ⟶ B} {t : T ⟶ Z} {v : T ⟶ U} {c : U ⟶ B}
    {a : A ⟶ X} {b : B ⟶ Y} {j : X ⟶ Y}
    {d : Z ⟶ V} {e : X ⟶ V} {k : V ⟶ Y}
    (hp : IsPushout (i ≫ u) a b j) (hz : IsPushout i a d e)
    (hk : d ≫ k = u ≫ b) (he : e ≫ k = j)
    (hs : IsPushout (N.map t) (N.map v) (N.map u) (N.map c))
    (ht : IsPushout (N.map (t ≫ d)) (N.map v) (N.map k) (N.map (c ≫ b)))
    [Mono (N.map v)]
    (wz : realizationWeakEquivalences (nervePushoutComparison N hz)) :
    realizationWeakEquivalences (nervePushoutComparison N hp) := by
  let iB := N.map (i ≫ u)
  let aa := N.map a
  let r : pushout (N.map i) aa ⟶ pushout iB aa :=
    pushout.desc (N.map u ≫ pushout.inl iB aa) (pushout.inr iB aa) (by
      rw [← Category.assoc, ← N.map_comp]
      exact pushout.condition)
  have hPZ := IsPushout.of_hasPushout (N.map i) aa
  have hPB : IsPushout (N.map i ≫ N.map u) aa
      (pushout.inl iB aa) (pushout.inr iB aa) := by
    simpa only [iB, Functor.map_comp] using IsPushout.of_hasPushout iB aa
  have hr : N.map u ≫ pushout.inl iB aa = pushout.inl (N.map i) aa ≫ r := by
    change _ = _ ≫ pushout.desc _ _ _
    exact (pushout.inl_desc _ _ _).symm
  have hr' : pushout.inr (N.map i) aa ≫ r = pushout.inr iB aa := by
    change _ ≫ pushout.desc _ _ _ = _
    exact pushout.inr_desc _ _ _
  have hPB' : IsPushout (N.map i ≫ N.map u) aa
      (pushout.inl iB aa) (pushout.inr (N.map i) aa ≫ r) := by
    rw [hr']
    exact hPB
  have hup := hs.paste_horiz (hPB'.of_left hr hPZ).flip
  have hrf : r ≫ nervePushoutComparison N hp = nervePushoutComparison N hz ≫ N.map k := by
    apply pushout.hom_ext
    · calc
        pushout.inl (N.map i) aa ≫ (r ≫ nervePushoutComparison N hp) =
            (N.map u ≫ pushout.inl iB aa) ≫ nervePushoutComparison N hp := by
          rw [← Category.assoc, ← hr]
        _ = N.map u ≫ N.map b := by
          rw [Category.assoc, nervePushoutComparison_inl]
        _ = N.map d ≫ N.map k := by
          simpa only [Functor.map_comp] using congrArg N.map hk.symm
        _ = pushout.inl (N.map i) aa ≫ (nervePushoutComparison N hz ≫ N.map k) := by
          rw [← Category.assoc, nervePushoutComparison_inl]
    · calc
        pushout.inr (N.map i) aa ≫ (r ≫ nervePushoutComparison N hp) =
            pushout.inr iB aa ≫ nervePushoutComparison N hp := by
          rw [← Category.assoc, hr']
        _ = N.map j := nervePushoutComparison_inr N hp
        _ = N.map e ≫ N.map k := by
          simpa only [Functor.map_comp] using congrArg N.map he.symm
        _ = pushout.inr (N.map i) aa ≫ (nervePushoutComparison N hz ≫ N.map k) := by
          rw [← Category.assoc, nervePushoutComparison_inr]
  apply g.glue hup.flip ht.flip (𝟙 _) (𝟙 _)
    (nervePushoutComparison N hz) (nervePushoutComparison N hp)
  · simp
  · rw [Category.assoc, nervePushoutComparison_inl, Category.id_comp, N.map_comp]
  · rw [Category.assoc, nervePushoutComparison_inl, Category.id_comp, N.map_comp]
  · exact hrf
  · exact realizationWeakEquivalences.of_isIso _
  · exact realizationWeakEquivalences.of_isIso _
  · exact wz

end Thomason.Construction

end

section

/-! # Pushout comparison for the actual Thomason right adjoint

The right adjoint is Ex² of the Street nerve. For a retracting finite-poset
attachment its canonical comparison from the pushout of these right-adjoint
images is a realization weak equivalence. The proof uses the actual
Kan–Quillen acyclic-cofibration class; it does not require Ex to preserve
pushouts.
-/

namespace Thomason.Construction

open CategoryTheory CategoryTheory.Limits StrictOmegaCategory

section Comparison

variable {C : Type*} [Category* C] (N : C ⥤ SSet.{0})
  {A B X Y : C} {i : A ⟶ B} {a : A ⟶ X} {b : B ⟶ Y} {j : X ⟶ Y}

/-- The canonical comparison for Ex²N is weak under the same acyclic-attachment
criterion as the original nerve. -/
theorem extendedNervePushoutComparison_weakEquivalence (kq : KanQuillenPublishedInput.{0})
    (hj : ∀ X : SSet.{0}, realizationWeakEquivalences (canonicalExtension.app X))
    (hp : IsPushout i a b j) [Mono (N.map i)]
    (wi : realizationWeakEquivalences (N.map i))
    (wj : realizationWeakEquivalences (N.map j)) :
    realizationWeakEquivalences (nervePushoutComparison (N ⋙ SSet.ex ⋙ SSet.ex) hp) := by
  have : realizationWeakEquivalences.{0}.HasTwoOutOfThreeProperty := kq.twoOutOfThree
  have hmono : Mono ((N ⋙ SSet.ex ⋙ SSet.ex).map i) := by
    change Mono (SSet.ex.map (SSet.ex.map (N.map i)))
    infer_instance
  exact nervePushoutComparison_weakEquivalence (N ⋙ SSet.ex ⋙ SSet.ex) kq hp
    ((realization_ex_twice_iff hj (N.map i)).mpr wi)
    ((realization_ex_twice_iff hj (N.map j)).mpr wj)

end Comparison

namespace NormalizedSimplexIdentities

variable (h : NormalizedSimplexIdentities) [StrictColimitsInput]

/-- Finite-poset attachments have weak comparison under the actual omega
Thomason right adjoint, with the interval identity supplied by its proof. -/
theorem finite_poset_extended_attachment_comparison
    (G : RightGrayInput h)
    (s : PublishedPosetSieveInput h)
    (g : PublishedSimplicialGluingInput)
    (kq : KanQuillenPublishedInput.{0})
    (hj : ∀ X : SSet.{0}, realizationWeakEquivalences (canonicalExtension.app X))
    {P : Type} [PartialOrder P] [Finite P] (A : Set P) (R : SieveRetraction A)
    {X Y : StrictOmegaCategory.{0}} {a : h.categorification.obj (nerve A) ⟶ X}
    {b : h.categorification.obj (nerve P) ⟶ Y} {j : X ⟶ Y}
    (hp : IsPushout (h.posetMap (subposetInclusion A)) a b j) :
    realizationWeakEquivalences
      (nervePushoutComparison (h.streetNerve ⋙ SSet.ex ⋙ SSet.ex) hp) := by
  have := s.omega_nerve_mono A R.lower
  have hw : h.CouniversalStreetWeakEquivalence (h.posetMap (subposetInclusion A)) :=
    h.finite_poset_couniversal G (SimplexComplex.alexanderWhitneyInput h) s g kq A R
  have hid : IsPushout (h.posetMap (subposetInclusion A)) (𝟙 _) (𝟙 _)
      (h.posetMap (subposetInclusion A)) := IsPushout.of_id_snd
  exact extendedNervePushoutComparison_weakEquivalence h.streetNerve kq hj hp (hw hid) (hw hp)

end NormalizedSimplexIdentities

namespace FiniteReflectionInput

variable {n : ℕ} (r : FiniteReflectionInput n)
  (h : NormalizedSimplexIdentities) [StrictColimitsInput]

/-- The same actual-right-adjoint comparison is weak in every positive finite dimension. -/
theorem finite_poset_extended_attachment_comparison
    (G : RightGrayInput h) (t : GrayTruncationInput G)
    (s : PublishedPosetSieveInput h)
    (g : PublishedSimplicialGluingInput)
    (kq : KanQuillenPublishedInput.{0})
    (hj : ∀ X : SSet.{0}, realizationWeakEquivalences (canonicalExtension.app X))
    {P : Type} [PartialOrder P] [Finite P] (A : Set P) (R : SieveRetraction A)
    {X Y : Truncated.{0} (n + 1)} {a : (r.categorification h).obj (nerve A) ⟶ X}
    {b : (r.categorification h).obj (nerve P) ⟶ Y} {j : X ⟶ Y}
    (hp : IsPushout (r.reflect.map (h.posetMap (subposetInclusion A))) a b j) :
    realizationWeakEquivalences
      (nervePushoutComparison (h.finiteStreetNerve (n + 1) ⋙ SSet.ex ⋙ SSet.ex) hp) := by
  have := r.posetSieve_nerve_mono h s A R.lower
  have hw : h.FiniteCouniversalStreetWeakEquivalence n
      (r.reflect.map (h.posetMap (subposetInclusion A))) :=
    r.finite_poset_couniversal h G t (SimplexComplex.alexanderWhitneyInput h) s g kq A R
  have hid : IsPushout (r.reflect.map (h.posetMap (subposetInclusion A))) (𝟙 _) (𝟙 _)
      (r.reflect.map (h.posetMap (subposetInclusion A))) := IsPushout.of_id_snd
  exact extendedNervePushoutComparison_weakEquivalence
    (h.finiteStreetNerve (n + 1)) kq hj hp (hw hid) (hw hp)

end FiniteReflectionInput
end Thomason.Construction

end

section

/-! # The published abstract Thomason reduction

Ara--Maltsiniotis (2014), Theorem 4.11, Proposition 5.13 and Scholie 5.14,
with Remark 4.13: for the actual Street adjunction, finite-poset
couniversality (d') and the finite-poset unit condition (e) imply the proper
combinatorial model axioms. The finite restriction is explicitly allowed
by Remark 4.13. This implication is a published input; its couniversality
premise is proved in this development, not assumed as a new-paper result.

The unit input is the finite-poset specialization of Gagna (2018),
Theorem 6.9, equivalently Ara--Maltsiniotis (2015), Corollary 10.11.
Sources: https://arxiv.org/pdf/1305.5086v3, pp.23--25,32;
https://arxiv.org/pdf/1612.04450v2, Theorem 6.9.
-/

namespace Thomason.Construction

open CategoryTheory

/-- Only the published unit comparison on finite posets, in the actual adjunctions. -/
structure PublishedFinitePosetUnitInput (h : NormalizedSimplexIdentities)
    [StrictColimitsInput] : Prop where
  omega (P : Type) [PartialOrder P] [Finite P] :
    realizationWeakEquivalences (h.categorificationAdjunction.unit.app (nerve P))
  finite (n : ℕ) (r : FiniteReflectionInput n) (P : Type) [PartialOrder P] [Finite P] :
    realizationWeakEquivalences ((r.categorificationAdjunction h).unit.app (nerve P))

/-- The precise published reduction, leaving both (d') and (e) as premises.
No model conclusion is assumed without those premises. -/
structure PublishedThomasonReduction (h : NormalizedSimplexIdentities)
    [StrictColimitsInput] : Prop where
  omega
    (d : ∀ {P : Type} [PartialOrder P] [Finite P] (A : Set P) (_R : SieveRetraction A),
      h.CouniversalStreetWeakEquivalence (h.posetMap (subposetInclusion A)))
    (e : ∀ (P : Type) [PartialOrder P] [Finite P],
      realizationWeakEquivalences (h.categorificationAdjunction.unit.app (nerve P))) :
    ProperCombinatorialAxioms StrictOmegaCategory.{0} h.streetWeakEquivalences h.thomasonFibrations
  finite (n : ℕ) (r : FiniteReflectionInput n)
    (d : ∀ {P : Type} [PartialOrder P] [Finite P] (A : Set P) (_R : SieveRetraction A),
      h.FiniteCouniversalStreetWeakEquivalence n (r.reflect.map (h.posetMap (subposetInclusion A))))
    (e : ∀ (P : Type) [PartialOrder P] [Finite P],
      realizationWeakEquivalences ((r.categorificationAdjunction h).unit.app (nerve P))) :
    ProperCombinatorialAxioms (StrictOmegaCategory.Truncated.{0} (n + 1))
      (FiniteReflectionInput.thomasonWeakEquivalences (n := n) h)
      (FiniteReflectionInput.thomasonFibrations (n := n) h)

namespace NormalizedSimplexIdentities

variable (h : NormalizedSimplexIdentities) [StrictColimitsInput]

/-- Conditional proper combinatorial model axioms in omega dimension.
The new couniversality condition is discharged by the constructed prisms
and finite-poset induction; only precisely cited published inputs remain. -/
theorem conditional_model_axioms
    (G : RightGrayInput h) (aw : SimplexComplex.AlexanderWhitneyInput h)
    (s : PublishedPosetSieveInput h)
    (g : PublishedSimplicialGluingInput)
    (kq : KanQuillenPublishedInput.{0})
    (units : PublishedFinitePosetUnitInput h) (transfer : PublishedThomasonReduction h) :
    ProperCombinatorialAxioms StrictOmegaCategory.{0} h.streetWeakEquivalences h.thomasonFibrations := by
  apply transfer.omega
  · intro P _ _ A R X Y a b j hp
    exact h.finite_poset_pushout_weakEquivalence G aw s g kq A R hp
  · exact units.omega

end NormalizedSimplexIdentities

namespace FiniteReflectionInput

variable {n : ℕ} (r : FiniteReflectionInput n)
  (h : NormalizedSimplexIdentities) [StrictColimitsInput]

include r

/-- The same conditional proper combinatorial model axioms in dimension n+1. -/
theorem conditional_model_axioms
    (G : RightGrayInput h) (t : GrayTruncationInput G)
    (aw : SimplexComplex.AlexanderWhitneyInput h)
    (s : PublishedPosetSieveInput h)
    (g : PublishedSimplicialGluingInput)
    (kq : KanQuillenPublishedInput.{0})
    (units : PublishedFinitePosetUnitInput h) (transfer : PublishedThomasonReduction h) :
    ProperCombinatorialAxioms (StrictOmegaCategory.Truncated.{0} (n + 1))
      (thomasonWeakEquivalences (n := n) h) (thomasonFibrations (n := n) h) := by
  apply transfer.finite n r
  · intro P _ _ A R X Y a b j hp
    exact r.finite_poset_pushout_weakEquivalence h G t aw s g kq A R hp
  · exact units.finite n r

end FiniteReflectionInput
end Thomason.Construction

end

section

/-! # Extension and the actual localized Street nerve

The classical extension coaugmentation makes extension an equivalence of
localized categories. Composing with it twice therefore preserves the
published Street-nerve equivalence of homotopy categories. This is a
compatibility theorem about the actual `Ex² N` functor.
-/

namespace Thomason.Construction

open CategoryTheory

/-- Any nerve with its inverse-image weak equivalences is a morphism of localizers. -/
noncomputable def nerveLocalizer {C : Type*} [Category* C] (N : C ⥤ SSet.{0}) :
    LocalizerMorphism (realizationWeakEquivalences.inverseImage N) realizationWeakEquivalences :=
  LocalizerMorphism.ofEq rfl

/-- The actual extension functor preserves realization weak equivalences. -/
noncomputable def extensionLocalizer (kq : KanQuillenPublishedInput.{0})
    (hj : ∀ X, realizationWeakEquivalences (canonicalExtension.app X)) :
    LocalizerMorphism realizationWeakEquivalences realizationWeakEquivalences where
  functor := SSet.ex
  map := by
    have := kq.twoOutOfThree
    intro X Y f hf
    exact (ex_map_iff realizationWeakEquivalences canonicalExtension hj f).mpr hf

/-- Extension induces an equivalence on the actual localization at realization W. -/
theorem extensionLocalizer_isLocalizedEquivalence (kq : KanQuillenPublishedInput.{0})
    (hj : ∀ X, realizationWeakEquivalences (canonicalExtension.app X)) :
    (extensionLocalizer kq hj).IsLocalizedEquivalence := by
  let Φ := extensionLocalizer kq hj
  let Ψ := LocalizerMorphism.id realizationWeakEquivalences
  apply Φ.isLocalizedEquivalence_of_unit_of_unit Ψ
    (canonicalExtension ≫ (Functor.rightUnitor SSet.ex).inv)
    (canonicalExtension ≫ (Functor.leftUnitor SSet.ex).inv)
  · intro X
    change realizationWeakEquivalences (canonicalExtension.app X ≫ 𝟙 _)
    simpa using hj X
  · intro X
    change realizationWeakEquivalences (canonicalExtension.app X ≫ 𝟙 _)
    simpa using hj X

/-- The morphism of localizers underlying the actual Thomason right adjoint. -/
noncomputable def thomasonRightLocalizer {C : Type*} [Category* C] (N : C ⥤ SSet.{0})
    (kq : KanQuillenPublishedInput.{0})
    (hj : ∀ X, realizationWeakEquivalences (canonicalExtension.app X)) :
    LocalizerMorphism (realizationWeakEquivalences.inverseImage N) realizationWeakEquivalences :=
  ((nerveLocalizer N).comp (extensionLocalizer kq hj)).comp (extensionLocalizer kq hj)

/-- A Street-nerve equivalence of homotopy categories passes to `Ex² N`. -/
theorem thomasonRightLocalizer_isLocalizedEquivalence {C : Type*} [Category* C]
    (N : C ⥤ SSet.{0}) (kq : KanQuillenPublishedInput.{0})
    (hj : ∀ X, realizationWeakEquivalences (canonicalExtension.app X))
    (hN : (nerveLocalizer N).IsLocalizedEquivalence) :
    (thomasonRightLocalizer N kq hj).IsLocalizedEquivalence := by
  have := hN
  have := extensionLocalizer_isLocalizedEquivalence kq hj
  exact LocalizerMorphism.IsLocalizedEquivalence.comp _ _

/-- Gagna (2018), Theorem 5.6: the Street nerve induces an equivalence of
homotopy categories for every positive finite dimension and omega.
Original source: https://arxiv.org/pdf/1612.04450v2, p.12. -/
structure PublishedStreetLocalizationInput (h : NormalizedSimplexIdentities) : Prop where
  omega : (nerveLocalizer h.streetNerve).IsLocalizedEquivalence
  finite (n : ℕ) : (nerveLocalizer (h.finiteStreetNerve (n + 1))).IsLocalizedEquivalence

end Thomason.Construction

end

section

/-! # A localizer adjunction with weak unit and counit

These statements use the actual localized functors. No assertion about
localization equivalence is used as a premise.
-/

namespace Thomason.Construction

open CategoryTheory CategoryTheory.Functor

universe u₁ u₂ v₁ v₂

section

variable {C₁ : Type u₁} {C₂ : Type u₂} [Category.{v₁} C₁] [Category.{v₂} C₂]
    {W₁ : MorphismProperty C₁} {W₂ : MorphismProperty C₂}
    (Φ : LocalizerMorphism W₁ W₂) (Ψ : LocalizerMorphism W₂ W₁)
    (adj : Ψ.functor ⊣ Φ.functor)

/-- An adjunction whose unit and counit are weak gives an equivalence
between the actual localized categories. -/
theorem localizer_equivalence_of_weak_unit_counit
    (hu : ∀ X, W₂ (adj.unit.app X)) (hc : ∀ X, W₁ (adj.counit.app X)) :
    Φ.IsLocalizedEquivalence where
  isEquivalence := by
    have : IsIso (whiskerRight adj.unit W₂.Q) := by
      rw [NatTrans.isIso_iff_isIso_app]
      exact fun X => Localization.inverts W₂.Q W₂ _ (hu X)
    have : IsIso (whiskerRight adj.counit W₁.Q) := by
      rw [NatTrans.isIso_iff_isIso_app]
      exact fun X => Localization.inverts W₁.Q W₁ _ (hc X)
    refine (Localization.equivalence W₁.Q W₁ W₂.Q W₂ (Φ.functor ⋙ W₂.Q)
      (Φ.localizedFunctor W₁.Q W₂.Q)
      (Ψ.functor ⋙ W₁.Q) (Ψ.localizedFunctor W₂.Q W₁.Q) ?_ ?_).isEquivalence_functor
    · exact Functor.associator _ _ _ ≪≫
        isoWhiskerLeft _ (CatCommSq.iso Ψ.functor W₂.Q W₁.Q _).symm ≪≫
        (Functor.associator _ _ _).symm ≪≫
        asIso (whiskerRight adj.counit W₁.Q) ≪≫ Functor.leftUnitor _
    · exact Functor.associator _ _ _ ≪≫
        isoWhiskerLeft _ (CatCommSq.iso Φ.functor W₁.Q W₂.Q _).symm ≪≫
        (Functor.associator _ _ _).symm ≪≫
        (asIso (whiskerRight adj.unit W₂.Q)).symm ≪≫ Functor.leftUnitor _

end

/-- The triangle identity forces the right-adjoint image of the counit
weak as soon as the actual unit is weak. -/
theorem right_counit_weak_of_unit
    {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
    (W : MorphismProperty C) [W.HasTwoOutOfThreeProperty] [W.ContainsIdentities]
    (hu : ∀ X, W (adj.unit.app X)) (Y : D) :
    W (R.map (adj.counit.app Y)) := by
  apply W.of_precomp (adj.unit.app (R.obj Y)) _ (hu _)
  rw [adj.right_triangle_components]
  exact W.id_mem _

end Thomason.Construction

end

section

/-! # Conditional main theorem in all strict higher dimensions

The result contains the actual model category, its prescribed generating
classes, properness and local presentability, and the actual adjunction
whose right derived functor is an equivalence. The latter is the derived
formulation of Quillen equivalence (Hovey, Proposition 1.3.13).

The strict Gray-prism and Street-cover construction proves the
finite-poset couniversality hypothesis of the transfer theorem.
-/

namespace Thomason.Construction

open CategoryTheory HomotopicalAlgebra
open SSet.modelCategoryQuillen

/-- The main conclusion in the usual derived formulation of Quillen
equivalence. Weak equivalences, fibrations, and both generators are fixed
by the actual Street nerve and twice-subdivided left adjoint. -/
structure ThomasonModelResult {C : Type 1} [Category.{0} C]
    (L : SSet.{0} ⥤ C) (N : C ⥤ SSet.{0})
    (kq : KanQuillenPublishedInput.{0})
    (hj : ∀ X, realizationWeakEquivalences (canonicalExtension.app X)) where
  axioms : ProperCombinatorialAxioms C (realizationWeakEquivalences.inverseImage N)
    (J.rlp.inverseImage (N ⋙ SSet.ex ⋙ SSet.ex))
  adjunction : L ⊣ (N ⋙ SSet.ex ⋙ SSet.ex)
  boundaryLifting : J.rlp.inverseImage (N ⋙ SSet.ex ⋙ SSet.ex) ⊓
      realizationWeakEquivalences.inverseImage N = (I.map L).rlp
  hornLifting : J.rlp.inverseImage (N ⋙ SSet.ex ⋙ SSet.ex) = (J.map L).rlp
  derivedEquivalence : (thomasonRightLocalizer N kq hj).IsLocalizedEquivalence

namespace ThomasonModelResult

variable {C : Type 1} [Category.{0} C]
  {L : SSet.{0} ⥤ C} {N : C ⥤ SSet.{0}}
  {kq : KanQuillenPublishedInput.{0}}
  {hj : ∀ X, realizationWeakEquivalences (canonicalExtension.app X)}
  (m : ThomasonModelResult L N kq hj)

/-- The conditional result supplies a genuine Mathlib model category. -/
@[instance_reducible]
noncomputable def model : ModelCategory C := by
  have := kq.twoOutOfThree
  exact m.axioms.model

/-- Its cofibrations are generated by the actual twice-subdivided boundaries. -/
theorem cofibrations_eq_generated :
    @cofibrations C _ m.model.categoryWithCofibrations = (I.map L).rlp.llp := by
  change (J.rlp.inverseImage (N ⋙ SSet.ex ⋙ SSet.ex) ⊓
    realizationWeakEquivalences.inverseImage N).llp = _
  rw [m.boundaryLifting]

include kq hj in
/-- The right adjoint preserves trivial fibrations for the actual KQ classes. -/
theorem right_preserves_trivialFibrations :
    (J.rlp.inverseImage (N ⋙ SSet.ex ⋙ SSet.ex) ⊓ realizationWeakEquivalences.inverseImage N) ≤
      (J.rlp ⊓ realizationWeakEquivalences).inverseImage (N ⋙ SSet.ex ⋙ SSet.ex) := by
  have := kq.twoOutOfThree
  intro X Y f hf
  refine ⟨hf.1, ?_⟩
  exact (realization_ex_twice_iff hj (N.map f)).mpr hf.2

/-- Right fibrations are preserved by their prescribed definition. -/
theorem right_preserves_fibrations :
    J.rlp.inverseImage (N ⋙ SSet.ex ⋙ SSet.ex) ≤
      J.rlp.inverseImage (N ⋙ SSet.ex ⋙ SSet.ex) := le_rfl

end ThomasonModelResult

end Thomason.Construction

end

section

/-! # The conditional main theorem in all strict higher dimensions -/

namespace Thomason.Construction

open CategoryTheory

namespace NormalizedSimplexIdentities

variable (h : NormalizedSimplexIdentities) [StrictColimitsInput]

/-- The conditional main model and Quillen-equivalence conclusion in omega dimension. -/
noncomputable def conditional_main
    (G : RightGrayInput h) (aw : SimplexComplex.AlexanderWhitneyInput h)
    (s : PublishedPosetSieveInput h)
    (g : PublishedSimplicialGluingInput)
    (kq : KanQuillenPublishedInput.{0})
    (hj : ∀ X, realizationWeakEquivalences (canonicalExtension.app X))
    (units : PublishedFinitePosetUnitInput h) (transfer : PublishedThomasonReduction h)
    (loc : PublishedStreetLocalizationInput h) :
    ThomasonModelResult h.thomasonLeft h.streetNerve kq hj where
  axioms := h.conditional_model_axioms G aw s g kq units transfer
  adjunction := h.thomasonAdjunction
  boundaryLifting := h.thomason_trivialFibrations_eq_generating_rlp kq hj
  hornLifting := h.thomasonFibrations_eq_generating_rlp
  derivedEquivalence := thomasonRightLocalizer_isLocalizedEquivalence h.streetNerve kq hj loc.omega

end NormalizedSimplexIdentities

namespace FiniteReflectionInput

variable {n : ℕ} (r : FiniteReflectionInput n)
  (h : NormalizedSimplexIdentities) [StrictColimitsInput]

/-- The conditional main theorem in each positive finite dimension n+1. -/
noncomputable def conditional_main
    (G : RightGrayInput h) (t : GrayTruncationInput G)
    (aw : SimplexComplex.AlexanderWhitneyInput h)
    (s : PublishedPosetSieveInput h)
    (g : PublishedSimplicialGluingInput)
    (kq : KanQuillenPublishedInput.{0})
    (hj : ∀ X, realizationWeakEquivalences (canonicalExtension.app X))
    (units : PublishedFinitePosetUnitInput h) (transfer : PublishedThomasonReduction h)
    (loc : PublishedStreetLocalizationInput h) :
    ThomasonModelResult (r.thomasonLeft h) (h.finiteStreetNerve (n + 1)) kq hj where
  axioms := r.conditional_model_axioms h G t aw s g kq units transfer
  adjunction := r.thomasonAdjunction h
  boundaryLifting := r.thomason_trivialFibrations_eq_generating_rlp h kq hj
  hornLifting := r.thomasonFibrations_eq_generating_rlp h
  derivedEquivalence := thomasonRightLocalizer_isLocalizedEquivalence
    (h.finiteStreetNerve (n + 1)) kq hj (loc.finite n)

end FiniteReflectionInput
end Thomason.Construction
namespace Thomason.Construction

/-- The main result, simultaneously for omega and all positive finite dimensions,
conditional only on the explicitly stated published inputs. -/
theorem conditional_main_all_dimensions
    (h : NormalizedSimplexIdentities) [StrictColimitsInput]
    (G : RightGrayInput h) (t : GrayTruncationInput G)
    (r : ∀ n, FiniteReflectionInput n)
    (aw : SimplexComplex.AlexanderWhitneyInput h)
    (s : PublishedPosetSieveInput h)
    (g : PublishedSimplicialGluingInput)
    (kq : KanQuillenPublishedInput.{0})
    (hj : ∀ X, realizationWeakEquivalences (canonicalExtension.app X))
    (units : PublishedFinitePosetUnitInput h) (transfer : PublishedThomasonReduction h)
    (loc : PublishedStreetLocalizationInput h) :
    Nonempty (ThomasonModelResult h.thomasonLeft h.streetNerve kq hj) ∧
      ∀ n, Nonempty (ThomasonModelResult ((r n).thomasonLeft h)
        (h.finiteStreetNerve (n + 1)) kq hj) :=
  ⟨⟨h.conditional_main G aw s g kq hj units transfer loc⟩,
    fun n => ⟨(r n).conditional_main h G t aw s g kq hj units transfer loc⟩⟩

end Thomason.Construction

end

section

/-! # Actual simplicial pushouts from covers of images

The criterion below transports the pushout of subcomplexes back to the
original monomorphisms. It is used for the two sides of the finite-poset
adjunction-unit comparison, retaining the original maps throughout.
-/

namespace Thomason.Construction

open CategoryTheory CategoryTheory.Limits

/-- A square of monomorphisms is a pushout when its two images cover the
target and their intersection is the image of the common source. -/
theorem simplicial_isPushout_of_ranges
    {I S T P : SSet.{0}} (i : I ⟶ S) (j : I ⟶ T) (b : S ⟶ P) (c : T ⟶ P)
    [Mono b] [Mono c] [Mono (i ≫ b)] (hw : i ≫ b = j ≫ c)
    (hcover : SSet.Subcomplex.range b ⊔ SSet.Subcomplex.range c = ⊤)
    (hinter : SSet.Subcomplex.range (i ≫ b) =
      SSet.Subcomplex.range b ⊓ SSet.Subcomplex.range c) : IsPushout i j b c := by
  let U := SSet.Subcomplex.range (i ≫ b)
  let V := SSet.Subcomplex.range b
  let W := SSet.Subcomplex.range c
  have sq : SSet.Subcomplex.BicartSq U V W ⊤ := ⟨hcover, hinter.symm⟩
  have hp : IsPushout (SSet.Subcomplex.homOfLE sq.le₁₂)
      (SSet.Subcomplex.homOfLE sq.le₁₃) V.ι W.ι :=
    sq.isPushout.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (SSet.Subcomplex.topIso P) (by simp) (by simp) (by simp) (by simp)
  apply hp.of_iso' (asIso (SSet.Subcomplex.toRange (i ≫ b)))
    (asIso (SSet.Subcomplex.toRange b)) (asIso (SSet.Subcomplex.toRange c)) (Iso.refl P)
  · apply (cancel_mono V.ι).mp
    change i ≫ b = i ≫ b
    rfl
  · apply (cancel_mono W.ι).mp
    change i ≫ b = j ≫ c
    exact hw
  · exact SSet.Subcomplex.toRange_ι b
  · exact SSet.Subcomplex.toRange_ι c

/-- The original nerve map of a full subposet is monic. -/
instance nerve_subposetInclusion_mono {P : Type} [PartialOrder P] (A : Set P) :
    Mono (nerveMap (subposetInclusion A).monotone.functor) := by
  rw [NatTrans.mono_iff_mono_app]
  intro m
  apply (CategoryTheory.mono_iff_injective _).mpr
  intro x y he
  apply nerve.ext_of_isThin
  funext k
  exact Subtype.ext (congrArg (fun z => z.obj k) he)

theorem nerve_subposetInclusion_range {P : Type} [PartialOrder P] (A : Set P) :
    SSet.Subcomplex.range (nerveMap (subposetInclusion A).monotone.functor) =
      fullSubposetComplex A := by
  rw [fullSubposetComplex_eq_range]
  congr 1

def interLeft {P : Type} [PartialOrder P] (A B : Set P) : (A ∩ B : Set P) →o A where
  toFun x := ⟨x.val, x.property.1⟩
  monotone' := fun _ _ h => h

def interRight {P : Type} [PartialOrder P] (A B : Set P) : (A ∩ B : Set P) →o B where
  toFun x := ⟨x.val, x.property.2⟩
  monotone' := fun _ _ h => h

theorem interLeft_comp {P : Type} [PartialOrder P] (A B : Set P) :
    (subposetInclusion A).comp (interLeft A B) = subposetInclusion (A ∩ B) := rfl

theorem interRight_comp {P : Type} [PartialOrder P] (A B : Set P) :
    (subposetInclusion B).comp (interRight A B) = subposetInclusion (A ∩ B) := rfl

/-- The full-sieve cover is a pushout of the actual ordinary nerve maps. -/
theorem sieve_nerve_maps_isPushout {P : Type} [PartialOrder P]
    (A B : Set P) (hA : IsLowerSet A) (hB : IsLowerSet B)
    (hcover : ∀ x, x ∈ A ∨ x ∈ B) :
    IsPushout (nerveMap (interLeft A B).monotone.functor)
      (nerveMap (interRight A B).monotone.functor)
      (nerveMap (subposetInclusion A).monotone.functor)
      (nerveMap (subposetInclusion B).monotone.functor) := by
  have hi : nerveMap (interLeft A B).monotone.functor ≫
      nerveMap (subposetInclusion A).monotone.functor =
      nerveMap (subposetInclusion (A ∩ B)).monotone.functor :=
    (orderNerveMap_comp _ _).symm
  have hj : nerveMap (interRight A B).monotone.functor ≫
      nerveMap (subposetInclusion B).monotone.functor =
      nerveMap (subposetInclusion (A ∩ B)).monotone.functor :=
    (orderNerveMap_comp _ _).symm
  have : Mono (nerveMap (interLeft A B).monotone.functor ≫
      nerveMap (subposetInclusion A).monotone.functor) := by rw [hi]; infer_instance
  apply simplicial_isPushout_of_ranges _ _ _ _ (hi.trans hj.symm)
  · rw [nerve_subposetInclusion_range, nerve_subposetInclusion_range]
    exact sieve_nerve_cover hA hB hcover
  · rw [hi, nerve_subposetInclusion_range, nerve_subposetInclusion_range,
      nerve_subposetInclusion_range, fullSubposetComplex_inter]

end Thomason.Construction

end

end OAI
