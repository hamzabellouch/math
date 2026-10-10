import OAI.CategoryTheory.Thomason.Simplicial.FinitePosetUnitReduction
import OAI.CategoryTheory.Thomason.Simplicial.SubdivisionWeakLifting
import OAI.CategoryTheory.Thomason.Strict.StreetFilteredColimits
import OAI.CategoryTheory.Thomason.Transfer.SimplicialRangeGluing
import OAI.CategoryTheory.Thomason.Transfer.ThomasonQuillenBridge
import OAI.CategoryTheory.Thomason.Transfer.ThomasonSmallObject
import OAI.CategoryTheory.Thomason.Transfer.WeakFactorizationRecognition
import Mathlib.CategoryTheory.Limits.Shapes.WidePullbacks

namespace OAI

section

/-! # Transfinite closure and the horn-attachment criterion

The actual Street weak class is stable under transfinite composition and
retracts. Thus the small object argument reduces horn-left acyclicity to
weakness of pushouts of simultaneous literal horn attachments. The horn-attachment premise expresses the local acyclicity criterion.
-/

namespace Thomason.Construction

open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty

universe u

theorem smallObject_leftLifting_weak {C : Type u} [Category.{0} C]
    [HasColimitsOfSize.{0,0} C] (I W : MorphismProperty C)
    [I.HasSmallObjectArgument.{0}] [W.IsStableUnderRetracts]
    [W.IsStableUnderTransfiniteComposition.{0}]
    (h : (coproducts.{0} I).pushouts ≤ W) : I.rlp.llp ≤ W := by
  rw [I.llp_rlp_of_hasSmallObjectArgument, retracts_le_iff]
  exact (transfiniteCompositions_monotone.{0} h).trans W.transfiniteCompositions_le

namespace NormalizedSimplexIdentities

variable (h : NormalizedSimplexIdentities)

local instance : h.streetWeakEquivalences.IsMultiplicative := by
  change (realizationWeakEquivalences.inverseImage h.streetNerve).IsMultiplicative
  exact { toContainsIdentities := inferInstance, toIsStableUnderComposition := inferInstance }
local instance : h.streetWeakEquivalences.RespectsIso :=
  inferInstanceAs (realizationWeakEquivalences.inverseImage h.streetNerve).RespectsIso
local instance : h.streetWeakEquivalences.IsStableUnderRetracts :=
  inferInstanceAs (realizationWeakEquivalences.inverseImage h.streetNerve).IsStableUnderRetracts
local instance : h.streetWeakEquivalences.HasTwoOutOfThreeProperty :=
  inferInstanceAs (realizationWeakEquivalences.inverseImage h.streetNerve).HasTwoOutOfThreeProperty

theorem streetWeak_transfinite {J : Type} [LinearOrder J] [SuccOrder J]
    [OrderBot J] [WellFoundedLT J] {X Y : StrictOmegaCategory.{0}} {f : X ⟶ Y}
    (hf : h.streetWeakEquivalences.TransfiniteCompositionOfShape J f) :
    h.streetWeakEquivalences f :=
  h.streetWeakEquivalences.transfiniteCompositionsOfShape_le J f hf.mem

theorem horn_left_weak_of_simultaneous_attachments
    (ha : (coproducts.{0} (imageHorns h.thomasonLeft)).pushouts ≤ h.streetWeakEquivalences) :
    h.thomasonFibrations.llp ≤ h.streetWeakEquivalences := by
  change (SSet.modelCategoryQuillen.J.rlp.inverseImage h.thomasonRight).llp ≤ _
  rw [← imageHorns_rlp h.thomasonAdjunction]
  let : (imageHorns h.thomasonLeft).HasSmallObjectArgument.{0} := smallFamily_hasSmallObjectArgument
    (fun p : Σ n : ℕ, Fin (n+2) => h.thomasonLeft.map (SSet.horn (p.1+1) p.2).ι)
  exact smallObject_leftLifting_weak (imageHorns h.thomasonLeft) h.streetWeakEquivalences ha

theorem weakCofibration_factorization_of_simultaneous_attachments
    (ha : (coproducts.{0} (imageHorns h.thomasonLeft)).pushouts ≤ h.streetWeakEquivalences) :
    IsWeakFactorizationSystem
      ((h.thomasonFibrations ⊓ h.streetWeakEquivalences).llp ⊓ h.streetWeakEquivalences)
      h.thomasonFibrations := by
  let := h.thomason_hornFactorization
  exact weakCofibration_factorization_of_leftLifting_weak _ _
    (h.horn_left_weak_of_simultaneous_attachments ha)

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
local instance : (thomasonWeakEquivalences (n := n) h).HasTwoOutOfThreeProperty :=
  inferInstanceAs (realizationWeakEquivalences.inverseImage (h.finiteStreetNerve (n+1))).HasTwoOutOfThreeProperty

theorem thomasonWeak_transfinite {J : Type} [LinearOrder J] [SuccOrder J]
    [OrderBot J] [WellFoundedLT J] {X Y : StrictOmegaCategory.Truncated.{0} (n+1)}
    {f : X ⟶ Y}
    (hf : (thomasonWeakEquivalences (n := n) h).TransfiniteCompositionOfShape J f) :
    thomasonWeakEquivalences (n := n) h f :=
  (thomasonWeakEquivalences (n := n) h).transfiniteCompositionsOfShape_le J f hf.mem

include r in
theorem horn_left_weak_of_simultaneous_attachments
    (ha : (coproducts.{0} (imageHorns (thomasonLeft r h))).pushouts ≤
      thomasonWeakEquivalences (n := n) h) :
    (thomasonFibrations (n := n) h).llp ≤ thomasonWeakEquivalences (n := n) h := by
  change (SSet.modelCategoryQuillen.J.rlp.inverseImage
    (h.finiteStreetNerve (n+1) ⋙ SSet.ex ⋙ SSet.ex)).llp ≤ _
  rw [← imageHorns_rlp (r.thomasonAdjunction h)]
  let : (imageHorns (thomasonLeft r h)).HasSmallObjectArgument.{0} := smallFamily_hasSmallObjectArgument
    (fun p : Σ m : ℕ, Fin (m+2) => (thomasonLeft r h).map (SSet.horn (p.1+1) p.2).ι)
  exact smallObject_leftLifting_weak (imageHorns (thomasonLeft r h))
    (thomasonWeakEquivalences (n := n) h) ha

include r in
theorem weakCofibration_factorization_of_simultaneous_attachments
    (ha : (coproducts.{0} (imageHorns (thomasonLeft r h))).pushouts ≤
      thomasonWeakEquivalences (n := n) h) :
    IsWeakFactorizationSystem
      (((thomasonFibrations (n := n) h ⊓ thomasonWeakEquivalences (n := n) h).llp) ⊓
        thomasonWeakEquivalences (n := n) h)
      (thomasonFibrations (n := n) h) := by
  let := r.thomason_hornFactorization h
  exact weakCofibration_factorization_of_leftLifting_weak _ _
    (r.horn_left_weak_of_simultaneous_attachments h ha)

end FiniteReflectionInput

end Thomason.Construction

end

section

/-! # Simultaneous attachments as filtered unions of finite attachments

Finite subfamilies form a filtered diagram of wide pushouts. Adding one
member is its ordinary cobase change. The full wide pushout is the colimit
of this diagram, including its specified map from the common source.
-/

namespace Thomason.Construction.FiniteSubsetAttachments

open CategoryTheory CategoryTheory.Limits

universe u

variable {C : Type u} [Category.{0} C] [HasColimitsOfSize.{0,0} C]
    {α : Type} {X : C} {Y : α → C} (q : ∀ a, X ⟶ Y a)

noncomputable section

abbrev object (S : Finset α) : C := widePushout X (fun a : S => Y a.val) (fun a => q a.val)

abbrev head (S : Finset α) : X ⟶ object q S := WidePushout.head (fun a : S => q a.val)

abbrev leg (S : Finset α) (a : S) : Y a.val ⟶ object q S :=
  WidePushout.ι (fun a : S => q a.val) a

@[reassoc, simp] theorem arrow_leg (S : Finset α) (a : S) :
    q a.val ≫ leg q S a = head q S :=
  WidePushout.arrow_ι (fun a : S => q a.val) a

def map {S T : Finset α} (h : S ⊆ T) : object q S ⟶ object q T :=
  WidePushout.desc (head q T) (fun a => leg q T ⟨a.val, h a.property⟩)
    (fun a => arrow_leg q T ⟨a.val, h a.property⟩)

@[reassoc, simp] theorem head_map {S T : Finset α} (h : S ⊆ T) :
    head q S ≫ map q h = head q T := by
  exact WidePushout.head_desc (fun a : S => q a.val) _ _ _

@[reassoc, simp] theorem leg_map {S T : Finset α} (h : S ⊆ T) (a : S) :
    leg q S a ≫ map q h = leg q T ⟨a.val, h a.property⟩ :=
  WidePushout.ι_desc (fun a : S => q a.val) _ _ _ a

abbrev diagram : Finset α ⥤ C where
  obj := object q
  map f := map q (leOfHom f)
  map_id S := by
    apply WidePushout.hom_ext
    · intro a
      change leg q S a ≫ map q _ = leg q S a ≫ 𝟙 _
      simp only [leg_map, Category.comp_id]
    · change head q S ≫ map q _ = head q S ≫ 𝟙 _
      simp only [head_map, Category.comp_id]
  map_comp {S T U} f g := by
    apply WidePushout.hom_ext
    · intro a
      change leg q S a ≫ map q _ = leg q S a ≫ (map q _ ≫ map q _)
      simp only [leg_map, leg_map_assoc]
    · change head q S ≫ map q _ = head q S ≫ (map q _ ≫ map q _)
      simp only [head_map, head_map_assoc]

def heads : (Functor.const (Finset α)).obj X ⟶ diagram q where
  app := head q
  naturality S T f := by
    change 𝟙 X ≫ head q T = head q S ≫ map q (leOfHom f)
    rw [Category.id_comp, head_map]

def emptyIso : X ≅ object q ∅ where
  hom := head q ∅
  inv := WidePushout.desc (𝟙 X) (fun a => False.elim (Finset.notMem_empty a.val a.property))
    (fun a => False.elim (Finset.notMem_empty a.val a.property))
  hom_inv_id := WidePushout.head_desc _ _ _ _
  inv_hom_id := by
    apply WidePushout.hom_ext
    · intro a; exact False.elim (Finset.notMem_empty a.val a.property)
    · simp [WidePushout.head_desc_assoc]

def insertLeg [DecidableEq α] (S : Finset α) (i : α) (_hi : i ∉ S)
    (s : PushoutCocone (head q S) (q i)) (a : ↥(insert i S)) : Y a.val ⟶ s.pt := by
  rcases a with ⟨a, ha⟩
  by_cases h : a = i
  · subst a; exact s.inr
  · exact leg q S ⟨a, (Finset.mem_insert.mp ha).resolve_left h⟩ ≫ s.inl

theorem insertLeg_condition [DecidableEq α] (S : Finset α) (i : α) (hi : i ∉ S)
    (s : PushoutCocone (head q S) (q i)) (a : ↥(insert i S)) :
    q a.val ≫ insertLeg q S i hi s a = head q S ≫ s.inl := by
  rcases a with ⟨a, ha⟩
  by_cases h : a = i
  · subst a
    simpa [insertLeg] using s.condition.symm
  · simp only [insertLeg, dite_eq_right h]
    exact arrow_leg_assoc q S ⟨a, (Finset.mem_insert.mp ha).resolve_left h⟩ s.inl

def insertDesc [DecidableEq α] (S : Finset α) (i : α) (hi : i ∉ S)
    (s : PushoutCocone (head q S) (q i)) : object q (insert i S) ⟶ s.pt :=
  WidePushout.desc (head q S ≫ s.inl) (insertLeg q S i hi s)
    (insertLeg_condition q S i hi s)

theorem insertDesc_map [DecidableEq α] (S : Finset α) (i : α) (hi : i ∉ S)
    (s : PushoutCocone (head q S) (q i)) :
    map q (Finset.subset_insert i S) ≫ insertDesc q S i hi s = s.inl := by
  apply WidePushout.hom_ext
  · intro a
    have ha : a.val ≠ i := by intro h; exact hi (h ▸ a.property)
    change leg q S a ≫ (map q _ ≫ insertDesc q S i hi s) = leg q S a ≫ s.inl
    rw [leg_map_assoc]
    simp only [insertDesc, leg, WidePushout.ι_desc, insertLeg, dite_eq_right ha]
  · change head q S ≫ (map q _ ≫ insertDesc q S i hi s) = head q S ≫ s.inl
    rw [head_map_assoc]
    exact WidePushout.head_desc (fun a : ↥(insert i S) => q a.val) _ _ _

theorem insertDesc_leg [DecidableEq α] (S : Finset α) (i : α) (hi : i ∉ S)
    (s : PushoutCocone (head q S) (q i)) :
    leg q (insert i S) ⟨i, Finset.mem_insert_self i S⟩ ≫ insertDesc q S i hi s = s.inr := by
  simp [insertDesc, insertLeg, WidePushout.ι_desc]

theorem insert_isPushout [DecidableEq α] (S : Finset α) (i : α) (hi : i ∉ S) :
    IsPushout (head q S) (q i) (map q (Finset.subset_insert i S))
      (leg q (insert i S) ⟨i, Finset.mem_insert_self i S⟩) := by
  have eq : head q S ≫ map q (Finset.subset_insert i S) =
      q i ≫ leg q (insert i S) ⟨i, Finset.mem_insert_self i S⟩ :=
    (head_map q _).trans (arrow_leg q _ ⟨i, Finset.mem_insert_self i S⟩).symm
  apply IsPushout.of_isColimit (c := PushoutCocone.mk
    (map q (Finset.subset_insert i S))
    (leg q (insert i S) ⟨i, Finset.mem_insert_self i S⟩) eq)
  refine PushoutCocone.IsColimit.mk _ (insertDesc q S i hi)
    (insertDesc_map q S i hi) (insertDesc_leg q S i hi) ?_
  intro s m hm₁ hm₂
  apply WidePushout.hom_ext
  · rintro ⟨a, ha⟩
    by_cases h : a = i
    · subst a
      change leg q (insert i S) ⟨i, ha⟩ ≫ m =
        leg q (insert i S) ⟨i, ha⟩ ≫ insertDesc q S i hi s
      rw [insertDesc_leg]
      exact hm₂
    · let aS : S := ⟨a, (Finset.mem_insert.mp ha).resolve_left h⟩
      have hh := congrArg (fun f => leg q S aS ≫ f) hm₁
      change leg q S aS ≫ (map q _ ≫ m) = leg q S aS ≫ s.inl at hh
      rw [leg_map_assoc] at hh
      change leg q (insert i S) ⟨a, ha⟩ ≫ m =
        leg q (insert i S) ⟨a, ha⟩ ≫ insertDesc q S i hi s
      rw [show leg q (insert i S) ⟨a, ha⟩ ≫ insertDesc q S i hi s =
        leg q S aS ≫ s.inl by
          simp only [insertDesc, leg, WidePushout.ι_desc, insertLeg, dite_eq_right h]
          rfl]
      exact hh
  · have hh := congrArg (fun f => head q S ≫ f) hm₁
    change head q S ≫ (map q _ ≫ m) = head q S ≫ s.inl at hh
    rw [head_map_assoc] at hh
    change head q (insert i S) ≫ m = head q (insert i S) ≫ insertDesc q S i hi s
    rw [show head q (insert i S) ≫ insertDesc q S i hi s = head q S ≫ s.inl from
      WidePushout.head_desc (fun a : ↥(insert i S) => q a.val) _ _ _]
    exact hh

def fullLeg (S : Finset α) : object q S ⟶ widePushout X Y q :=
  WidePushout.desc (WidePushout.head q) (fun a => WidePushout.ι q a.val)
    (fun a => WidePushout.arrow_ι q a.val)

@[reassoc, simp] theorem head_fullLeg (S : Finset α) :
    head q S ≫ fullLeg q S = WidePushout.head q := WidePushout.head_desc _ _ _ _

@[reassoc, simp] theorem leg_fullLeg (S : Finset α) (a : S) :
    leg q S a ≫ fullLeg q S = WidePushout.ι q a.val := WidePushout.ι_desc _ _ _ _ _

abbrev fullCocone : Cocone (diagram q) where
  pt := widePushout X Y q
  ι := {
    app := fullLeg q
    naturality S T f := by
      apply WidePushout.hom_ext
      · intro a
        change leg q S a ≫ (map q (leOfHom f) ≫ fullLeg q T) = leg q S a ≫ (fullLeg q S ≫ 𝟙 _)
        simp only [leg_map_assoc, leg_fullLeg, Category.comp_id]
      · change head q S ≫ (map q (leOfHom f) ≫ fullLeg q T) = head q S ≫ (fullLeg q S ≫ 𝟙 _)
        simp only [head_map_assoc, head_fullLeg, Category.comp_id] }

def glueHead (c : Cocone (diagram q)) : X ⟶ c.pt := head q ∅ ≫ c.ι.app ∅

def glueLeg [DecidableEq α] (c : Cocone (diagram q)) (a : α) : Y a ⟶ c.pt :=
  leg q {a} ⟨a, Finset.mem_singleton_self a⟩ ≫ c.ι.app {a}

theorem glue_condition [DecidableEq α] (c : Cocone (diagram q)) (a : α) :
    q a ≫ glueLeg q c a = glueHead q c := by
  have hc := c.w (homOfLE (Finset.empty_subset {a}))
  change map q (Finset.empty_subset {a}) ≫ c.ι.app {a} = c.ι.app ∅ at hc
  unfold glueLeg
  rw [arrow_leg_assoc q {a} ⟨a, Finset.mem_singleton_self a⟩]
  rw [glueHead, ← hc, head_map_assoc]

def fullDesc [DecidableEq α] (c : Cocone (diagram q)) : widePushout X Y q ⟶ c.pt :=
  WidePushout.desc (glueHead q c) (glueLeg q c) (glue_condition q c)

theorem fullDesc_fac [DecidableEq α] (c : Cocone (diagram q)) (S : Finset α) :
    fullLeg q S ≫ fullDesc q c = c.ι.app S := by
  apply WidePushout.hom_ext
  · intro a
    have hsub : ({a.val} : Finset α) ⊆ S := Finset.singleton_subset_iff.mpr a.property
    have hc := c.w (homOfLE hsub)
    change map q hsub ≫ c.ι.app S = c.ι.app {a.val} at hc
    have hh := congrArg (fun f => leg q {a.val} ⟨a.val, Finset.mem_singleton_self _⟩ ≫ f) hc
    change leg q {a.val} ⟨a.val, _⟩ ≫ (map q hsub ≫ c.ι.app S) =
      leg q {a.val} ⟨a.val, _⟩ ≫ c.ι.app {a.val} at hh
    rw [leg_map_assoc] at hh
    change leg q S a ≫ (fullLeg q S ≫ fullDesc q c) = leg q S a ≫ c.ι.app S
    rw [leg_fullLeg_assoc]
    exact (WidePushout.ι_desc q _ _ _ a.val).trans hh.symm
  · have hc := c.w (homOfLE (Finset.empty_subset S))
    change map q (Finset.empty_subset S) ≫ c.ι.app S = c.ι.app ∅ at hc
    have hh := congrArg (fun f => head q ∅ ≫ f) hc
    change head q ∅ ≫ (map q _ ≫ c.ι.app S) = head q ∅ ≫ c.ι.app ∅ at hh
    rw [head_map_assoc] at hh
    change head q S ≫ (fullLeg q S ≫ fullDesc q c) = head q S ≫ c.ι.app S
    rw [head_fullLeg_assoc]
    exact (WidePushout.head_desc q _ _ _).trans hh.symm

def fullIsColimit [DecidableEq α] : IsColimit (fullCocone q) where
  desc := fullDesc q
  fac := fullDesc_fac q
  uniq c m hm := by
    apply WidePushout.hom_ext
    · intro a
      have hh := congrArg
        (fun f => leg q {a} ⟨a, Finset.mem_singleton_self a⟩ ≫ f) (hm {a})
      change leg q {a} ⟨a, _⟩ ≫ (fullLeg q {a} ≫ m) =
        leg q {a} ⟨a, _⟩ ≫ c.ι.app {a} at hh
      rw [leg_fullLeg_assoc] at hh
      exact hh.trans (WidePushout.ι_desc q (glueHead q c) (glueLeg q c) (glue_condition q c) a).symm
    · have hh := congrArg (fun f => head q ∅ ≫ f) (hm ∅)
      change head q ∅ ≫ (fullLeg q ∅ ≫ m) = head q ∅ ≫ c.ι.app ∅ at hh
      rw [head_fullLeg_assoc] at hh
      exact hh.trans (WidePushout.head_desc q _ _ _).symm

/-- A map remains weak after every individual cobase change. -/
abbrev cobaseWeak (W : MorphismProperty C) : MorphismProperty C :=
  W.op.universally.unop

omit [HasColimitsOfSize.{0,0} C] in
theorem cobaseWeak_iff (W : MorphismProperty C) {A B : C} (i : A ⟶ B) :
    cobaseWeak W i ↔ ∀ {Z P : C} (a : A ⟶ Z) (b : B ⟶ P) (j : Z ⟶ P),
      IsPushout i a b j → W j := by
  constructor
  · intro h Z P a b j sq
    exact h b.op a.op j.op sq.op
  · intro h Z P a b j sq
    exact h b.unop a.unop j.unop sq.unop

theorem finite_head_weak (W : MorphismProperty C) [W.IsMultiplicative] [W.RespectsIso]
    (hq : ∀ a, cobaseWeak W (q a)) (S : Finset α) : W (head q S) := by
  classical
  induction S using Finset.induction_on with
  | empty => exact W.of_isIso (emptyIso q).hom
  | @insert i S hi ih =>
    rw [← head_map q (Finset.subset_insert i S)]
    exact W.comp_mem _ _ ih
      ((cobaseWeak_iff W (q i)).mp (hq i) _ _ _ (insert_isPushout q S i hi).flip)

/-- Arbitrary simultaneous cobase-weak maps remain weak. The proof uses
the actual filtered colimit of finite subfamilies. -/
theorem full_head_weak (W : MorphismProperty C) [W.IsMultiplicative] [W.RespectsIso]
    [W.IsStableUnderFilteredColimits.{0,0}]
    (hq : ∀ a, cobaseWeak W (q a)) : W (WidePushout.head q) := by
  classical
  apply MorphismProperty.IsStableUnderColimitsOfShape.condition
    (W := W) ((Functor.const (Finset α)).obj X) (diagram q)
    (Cocone.mk X (𝟙 _)) (fullCocone q)
    (isColimitConstCocone (Finset α) X) (fullIsColimit q) (heads q)
  · exact finite_head_weak q W hq
  · intro S
    change 𝟙 X ≫ WidePushout.head q = head q S ≫ fullLeg q S
    rw [Category.id_comp, head_fullLeg]

end

end Thomason.Construction.FiniteSubsetAttachments

end

section

/-! # From individual attachments to simultaneous attachments

A pushout of a coproduct of maps is the wide pushout of their individual
pushouts over the common attaching object. Together with the finite-subset
colimit this reduces simultaneous weak attachments to individual ones.
-/

namespace Thomason.Construction.SimultaneousAttachments

open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty
open FiniteSubsetAttachments

universe u

variable {C : Type u} [Category.{0} C] [HasColimitsOfSize.{0,0} C]
    {α : Type} {A B : α → C} (i : ∀ a, A a ⟶ B a) {X : C} (a : ∐ A ⟶ X)

noncomputable section

abbrev attachingMap (j : α) : A j ⟶ X := Sigma.ι A j ≫ a

abbrev piece (j : α) : C := pushout (i j) (attachingMap a j)

abbrev pieceMap (j : α) : X ⟶ piece i a j := pushout.inr (i j) (attachingMap a j)

abbrev pieceInclusion (j : α) : B j ⟶ piece i a j :=
  pushout.inl (i j) (attachingMap a j)

abbrev total : C := widePushout X (piece i a) (pieceMap i a)

abbrev totalHead : X ⟶ total i a := WidePushout.head (pieceMap i a)

abbrev totalLeg (j : α) : piece i a j ⟶ total i a :=
  WidePushout.ι (pieceMap i a) j

@[reassoc, simp] theorem pieceMap_totalLeg (j : α) :
    pieceMap i a j ≫ totalLeg i a j = totalHead i a :=
  WidePushout.arrow_ι (pieceMap i a) j

abbrev totalInclusion : ∐ B ⟶ total i a :=
  Sigma.desc (fun j => pieceInclusion i a j ≫ totalLeg i a j)

@[reassoc, simp] theorem sigma_totalInclusion (j : α) :
    Sigma.ι B j ≫ totalInclusion i a = pieceInclusion i a j ≫ totalLeg i a j :=
  Sigma.ι_comp_desc _ j

theorem total_condition : Limits.Sigma.map i ≫ totalInclusion i a = a ≫ totalHead i a := by
  apply Sigma.hom_ext
  intro j
  rw [Sigma.ι_map_assoc, sigma_totalInclusion]
  change i j ≫ (pushout.inl (i j) (attachingMap a j) ≫ totalLeg i a j) = _
  rw [← Category.assoc, pushout.condition, Category.assoc, pieceMap_totalLeg]
  exact Category.assoc _ _ _

variable (s : PushoutCocone (Limits.Sigma.map i) a)

theorem piece_condition (j : α) :
    i j ≫ (Sigma.ι B j ≫ s.inl) = attachingMap a j ≫ s.inr := by
  have hs := congrArg (fun f => Sigma.ι A j ≫ f) s.condition
  simpa only [Category.assoc, Sigma.ι_map_assoc] using hs

abbrev pieceDesc (j : α) : piece i a j ⟶ s.pt :=
  pushout.desc (Sigma.ι B j ≫ s.inl) s.inr (piece_condition i a s j)

@[reassoc, simp] theorem pieceInclusion_desc (j : α) :
    pieceInclusion i a j ≫ pieceDesc i a s j = Sigma.ι B j ≫ s.inl :=
  pushout.inl_desc _ _ _

@[reassoc, simp] theorem pieceMap_desc (j : α) :
    pieceMap i a j ≫ pieceDesc i a s j = s.inr :=
  pushout.inr_desc _ _ _

abbrev totalDesc : total i a ⟶ s.pt :=
  WidePushout.desc s.inr (pieceDesc i a s) (pieceMap_desc i a s)

@[reassoc, simp] theorem totalLeg_desc (j : α) :
    totalLeg i a j ≫ totalDesc i a s = pieceDesc i a s j :=
  WidePushout.ι_desc (pieceMap i a) _ _ _ j

@[reassoc, simp] theorem totalHead_desc : totalHead i a ≫ totalDesc i a s = s.inr :=
  WidePushout.head_desc (pieceMap i a) _ _ _

theorem totalInclusion_desc : totalInclusion i a ≫ totalDesc i a s = s.inl := by
  apply Sigma.hom_ext
  intro j
  rw [sigma_totalInclusion_assoc, totalLeg_desc, pieceInclusion_desc]

omit s in
theorem total_isPushout : IsPushout (Limits.Sigma.map i) a (totalInclusion i a) (totalHead i a) := by
  apply IsPushout.of_isColimit (c := PushoutCocone.mk
    (totalInclusion i a) (totalHead i a) (total_condition i a))
  refine PushoutCocone.IsColimit.mk (total_condition i a) (totalDesc i a)
    (totalInclusion_desc i a) (totalHead_desc i a) ?_
  intro s m hm₁ hm₂
  apply WidePushout.hom_ext
  · intro j
    apply pushout.hom_ext
    · have hm := congrArg (fun f => Sigma.ι B j ≫ f) hm₁
      change Sigma.ι B j ≫ (totalInclusion i a ≫ m) = Sigma.ι B j ≫ s.inl at hm
      rw [sigma_totalInclusion_assoc] at hm
      change pieceInclusion i a j ≫ (totalLeg i a j ≫ m) =
        pieceInclusion i a j ≫ (totalLeg i a j ≫ totalDesc i a s)
      rw [totalLeg_desc, pieceInclusion_desc]
      exact hm
    · change pieceMap i a j ≫ (totalLeg i a j ≫ m) =
        pieceMap i a j ≫ (totalLeg i a j ≫ totalDesc i a s)
      rw [pieceMap_totalLeg_assoc, pieceMap_totalLeg_assoc, totalHead_desc]
      exact hm₂
  · exact hm₂.trans (totalHead_desc i a s).symm

omit s in
theorem pushout_sigma_weak (W : MorphismProperty C) [W.IsMultiplicative] [W.RespectsIso]
    [W.IsStableUnderFilteredColimits.{0,0}]
    (hi : ∀ j, cobaseWeak W (i j)) {P : C} (b : ∐ B ⟶ P) (j : X ⟶ P)
    (sq : IsPushout (Limits.Sigma.map i) a b j) : W j := by
  have hp : ∀ j, cobaseWeak W (pieceMap i a j) := fun j =>
    MorphismProperty.of_isPushout (IsPushout.of_hasPushout (i j) (attachingMap a j)).flip (hi j)
  have hw : W (totalHead i a) := full_head_weak (pieceMap i a) W hp
  let e := (total_isPushout i a).isoIsPushout _ _ sq
  have he : totalHead i a ≫ e.hom = j := IsPushout.inr_isoIsPushout_hom _ _ (total_isPushout i a) sq
  rw [← he, W.cancel_right_of_respectsIso]
  exact hw

omit i a s [HasColimitsOfSize.{0,0} C] in
theorem cobaseWeak_le (W : MorphismProperty C) : cobaseWeak W ≤ W := by
  intro X Y f hf
  exact W.op.universally_le f.op hf

omit i a s in
theorem cobaseWeak_sigmaMap (W : MorphismProperty C) [W.IsMultiplicative] [W.RespectsIso]
    [W.IsStableUnderFilteredColimits.{0,0}]
    {α : Type} {A B : α → C} (i : ∀ j, A j ⟶ B j)
    (hi : ∀ j, cobaseWeak W (i j)) : cobaseWeak W (Limits.Sigma.map i) := by
  rw [cobaseWeak_iff]
  intro X P a b j sq
  exact pushout_sigma_weak i a W hi b j sq

omit i a s in
instance cobaseWeak_stableUnderCoproducts (W : MorphismProperty C)
    [W.IsMultiplicative] [W.RespectsIso] [W.IsStableUnderFilteredColimits.{0,0}] :
    (cobaseWeak W).IsStableUnderCoproducts.{0} where
  isStableUnderCoproductsOfShape _α := IsStableUnderCoproductsOfShape.mk _ _
    (fun _ _ _ _ i hi => cobaseWeak_sigmaMap W i hi)

omit i a s in
/-- Only individual pushouts need to be checked. Simultaneous pushouts
follow from finite composition and filtered-colimit stability. -/
theorem simultaneous_attachments_weak (I W : MorphismProperty C)
    [W.IsMultiplicative] [W.RespectsIso] [W.IsStableUnderFilteredColimits.{0,0}]
    (h : I.pushouts ≤ W) : (coproducts.{0} I).pushouts ≤ W := by
  have hi : I ≤ cobaseWeak W := by
    intro A B i hi
    rw [cobaseWeak_iff]
    intro X P a b j sq
    exact h _ (I.pushouts_mk sq.flip hi)
  have hc : coproducts.{0} I ≤ cobaseWeak W := coproducts_le_iff.mpr hi
  exact (pushouts_le_iff.mpr hc).trans (cobaseWeak_le W)

omit i a s in
theorem smallObject_leftLifting_weak_of_individualAttachments (I W : MorphismProperty C)
    [I.HasSmallObjectArgument.{0}] [W.IsMultiplicative] [W.RespectsIso]
    [W.IsStableUnderFilteredColimits.{0,0}] [W.IsStableUnderRetracts]
    [W.IsStableUnderTransfiniteComposition.{0}]
    (h : I.pushouts ≤ W) : I.rlp.llp ≤ W :=
  smallObject_leftLifting_weak I W (simultaneous_attachments_weak I W h)

end

end Thomason.Construction.SimultaneousAttachments

end

section

/-! # The individual horn-attachment criterion for Thomason transfer

The small-object factorizations and Street weak class reduce
horn-left acyclicity to the pushout of one literal categorified horn at a
time, in omega and every positive finite dimension.
-/

namespace Thomason.Construction

open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty

universe u

namespace NormalizedSimplexIdentities

variable (h : NormalizedSimplexIdentities)

local instance : h.streetWeakEquivalences.IsMultiplicative := by
  change (realizationWeakEquivalences.inverseImage h.streetNerve).IsMultiplicative
  exact { toContainsIdentities := inferInstance, toIsStableUnderComposition := inferInstance }
local instance : h.streetWeakEquivalences.RespectsIso :=
  inferInstanceAs (realizationWeakEquivalences.inverseImage h.streetNerve).RespectsIso
local instance : h.streetWeakEquivalences.IsStableUnderRetracts :=
  inferInstanceAs (realizationWeakEquivalences.inverseImage h.streetNerve).IsStableUnderRetracts
local instance : h.streetWeakEquivalences.HasTwoOutOfThreeProperty :=
  inferInstanceAs (realizationWeakEquivalences.inverseImage h.streetNerve).HasTwoOutOfThreeProperty

theorem horn_left_weak_of_individual_attachments
    (ha : (imageHorns h.thomasonLeft).pushouts ≤ h.streetWeakEquivalences) :
    h.thomasonFibrations.llp ≤ h.streetWeakEquivalences := by
  change (SSet.modelCategoryQuillen.J.rlp.inverseImage h.thomasonRight).llp ≤ _
  rw [← imageHorns_rlp h.thomasonAdjunction]
  let : (imageHorns h.thomasonLeft).HasSmallObjectArgument.{0} := smallFamily_hasSmallObjectArgument
    (fun p : Σ n : ℕ, Fin (n+2) => h.thomasonLeft.map (SSet.horn (p.1+1) p.2).ι)
  exact SimultaneousAttachments.smallObject_leftLifting_weak_of_individualAttachments (imageHorns h.thomasonLeft) h.streetWeakEquivalences ha

theorem weakCofibration_factorization_of_individual_attachments
    (ha : (imageHorns h.thomasonLeft).pushouts ≤ h.streetWeakEquivalences) :
    IsWeakFactorizationSystem
      ((h.thomasonFibrations ⊓ h.streetWeakEquivalences).llp ⊓ h.streetWeakEquivalences)
      h.thomasonFibrations := by
  let := h.thomason_hornFactorization
  exact weakCofibration_factorization_of_leftLifting_weak _ _
    (h.horn_left_weak_of_individual_attachments ha)

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
local instance : (thomasonWeakEquivalences (n := n) h).HasTwoOutOfThreeProperty :=
  inferInstanceAs (realizationWeakEquivalences.inverseImage (h.finiteStreetNerve (n+1))).HasTwoOutOfThreeProperty

include r in
theorem horn_left_weak_of_individual_attachments
    (ha : (imageHorns (thomasonLeft r h)).pushouts ≤
      thomasonWeakEquivalences (n := n) h) :
    (thomasonFibrations (n := n) h).llp ≤ thomasonWeakEquivalences (n := n) h := by
  change (SSet.modelCategoryQuillen.J.rlp.inverseImage
    (h.finiteStreetNerve (n+1) ⋙ SSet.ex ⋙ SSet.ex)).llp ≤ _
  rw [← imageHorns_rlp (r.thomasonAdjunction h)]
  let : (imageHorns (thomasonLeft r h)).HasSmallObjectArgument.{0} := smallFamily_hasSmallObjectArgument
    (fun p : Σ m : ℕ, Fin (m+2) => (thomasonLeft r h).map (SSet.horn (p.1+1) p.2).ι)
  exact SimultaneousAttachments.smallObject_leftLifting_weak_of_individualAttachments (imageHorns (thomasonLeft r h))
    (thomasonWeakEquivalences (n := n) h) ha

include r in
theorem weakCofibration_factorization_of_individual_attachments
    (ha : (imageHorns (thomasonLeft r h)).pushouts ≤
      thomasonWeakEquivalences (n := n) h) :
    IsWeakFactorizationSystem
      (((thomasonFibrations (n := n) h ⊓ thomasonWeakEquivalences (n := n) h).llp) ⊓
        thomasonWeakEquivalences (n := n) h)
      (thomasonFibrations (n := n) h) := by
  let := r.thomason_hornFactorization h
  exact weakCofibration_factorization_of_leftLifting_weak _ _
    (r.horn_left_weak_of_individual_attachments h ha)

end FiniteReflectionInput

end Thomason.Construction

end

section

/-! # The actual Thomason unit is weak from finite-poset units

The double subdivision of a finite poset nerve is again an actual finite
poset nerve. Brown preservation and the finite-carrier reduction then
extend the unit test to every simplicial set.
-/

namespace Thomason.Construction

open CategoryTheory CategoryTheory.Limits
open WeakNaturalTransformationColimits

noncomputable section

/-- Finite-poset units for categorification imply finite-poset units for
the composite double-subdivision adjunction. -/
theorem twiceSubdivision_unit_finite_poset
    {C : Type 1} [Category.{0} C] {L : SSet.{0} ⥤ C} {N : C ⥤ SSet.{0}}
    (adj : L ⊣ N)
    (hu : ∀ (P : Type) [PartialOrder P] [Finite P],
      realizationWeakEquivalences (adj.unit.app (nerve P)))
    (P : Type) [PartialOrder P] [Finite P] :
    realizationWeakEquivalences
      (((SSet.sdExAdjunction.comp SSet.sdExAdjunction).comp adj).unit.app (nerve P)) := by
  let e : (SSet.sd ⋙ SSet.sd).obj (nerve P) ≅
      nerve (iteratedChainPoset (PartOrd.of P) 2) :=
    iteratedSubdivisionNerveIso (PartOrd.of P) 2
  have hs : realizationWeakEquivalences
      (adj.unit.app ((SSet.sd ⋙ SSet.sd).obj (nerve P))) :=
    (app_weak_iff_of_weak_images realizationWeakEquivalences adj.unit e.hom
      (realizationWeakEquivalences.of_isIso _)
      (realizationWeakEquivalences.of_isIso _)).mpr
      (hu (iteratedChainPoset (PartOrd.of P) 2))
  rw [Adjunction.comp_unit_app]
  apply realizationWeakEquivalences.comp_mem _ _
    (subdivision_twice_unit_weak_equivalence realizationWeakEquivalences
      lastVertex_weak canonicalExtension_weak (nerve P))
  exact (ex_twice_map_iff realizationWeakEquivalences canonicalExtension
    canonicalExtension_weak _).mpr hs

/-- Once the actual proper model axioms hold, the Thomason adjunction has
weak unit at every simplicial set if the finite categorification units hold. -/
theorem thomason_unit_weak_of_finite_poset_units
    {C : Type 1} [Category.{0} C] {L : SSet.{0} ⥤ C} {N : C ⥤ SSet.{0}}
    (adj : L ⊣ (N ⋙ SSet.ex ⋙ SSet.ex))
    (kq : KanQuillenPublishedInput.{0})
    (a : ProperCombinatorialAxioms C (realizationWeakEquivalences.inverseImage N)
      (SSet.modelCategoryQuillen.J.rlp.inverseImage (N ⋙ SSet.ex ⋙ SSet.ex)))
    [PreservesFilteredColimitsOfSize.{0,0} (N ⋙ SSet.ex ⋙ SSet.ex)]
    (hu : ∀ (P : Type) [PartialOrder P] [Finite P],
      realizationWeakEquivalences (adj.unit.app (nerve P)))
    (X : SSet.{0}) : realizationWeakEquivalences (adj.unit.app X) := by
  let : PreservesColimitsOfSize.{0,0} L := adj.leftAdjoint_preservesColimits
  apply FinitePosetUnitReduction.all adj.unit ?_ hu X
  intro A B f hf
  exact (ex_twice_map_iff realizationWeakEquivalences canonicalExtension
    canonicalExtension_weak _).mpr
    (ThomasonAdjunction.left_preserves_weakEquivalences adj kq a f hf)

namespace NormalizedSimplexIdentities

variable (h : NormalizedSimplexIdentities) [StrictColimitsInput]

/-- The omega-dimensional unit test, using only the finite-poset units
and the prescribed model axioms. -/
theorem thomason_unit_weak
    (kq : KanQuillenPublishedInput.{0})
    (a : ProperCombinatorialAxioms StrictOmegaCategory.{0} h.streetWeakEquivalences
      h.thomasonFibrations)
    (hu : ∀ (P : Type) [PartialOrder P] [Finite P],
      realizationWeakEquivalences (h.categorificationAdjunction.unit.app (nerve P)))
    (X : SSet.{0}) : realizationWeakEquivalences (h.thomasonAdjunction.unit.app X) :=
  thomason_unit_weak_of_finite_poset_units h.thomasonAdjunction kq a
    (twiceSubdivision_unit_finite_poset h.categorificationAdjunction hu) X

end NormalizedSimplexIdentities

namespace FiniteReflectionInput

variable {n : ℕ} (r : FiniteReflectionInput n)
    (h : NormalizedSimplexIdentities) [StrictColimitsInput]

/-- The same exact unit test in every positive finite dimension. -/
theorem thomason_unit_weak
    (kq : KanQuillenPublishedInput.{0})
    (a : ProperCombinatorialAxioms (StrictOmegaCategory.Truncated.{0} (n+1))
      (thomasonWeakEquivalences (n := n) h) (thomasonFibrations (n := n) h))
    (hu : ∀ (P : Type) [PartialOrder P] [Finite P],
      realizationWeakEquivalences ((r.categorificationAdjunction h).unit.app (nerve P)))
    (X : SSet.{0}) : realizationWeakEquivalences ((r.thomasonAdjunction h).unit.app X) :=
  thomason_unit_weak_of_finite_poset_units (r.thomasonAdjunction h) kq a
    (twiceSubdivision_unit_finite_poset (r.categorificationAdjunction h) hu) X

end FiniteReflectionInput

end

end Thomason.Construction

end

section

/-! # Thomason localization from the constructed model and finite units

This obtains the actual derived equivalence from unit and counit maps,
without invoking the published Street-localization equivalence.
-/

namespace Thomason.Construction

open CategoryTheory

noncomputable section

section General

variable {C : Type 1} [Category.{0} C]
    {L : SSet.{0} ⥤ C} {N : C ⥤ SSet.{0}}
    (adj : L ⊣ (N ⋙ SSet.ex ⋙ SSet.ex))
    (kq : KanQuillenPublishedInput.{0})
    (a : ProperCombinatorialAxioms C (realizationWeakEquivalences.inverseImage N)
      (SSet.modelCategoryQuillen.J.rlp.inverseImage (N ⋙ SSet.ex ⋙ SSet.ex)))

/-- Brown preservation makes the actual left adjoint a morphism of localizers. -/
def thomasonLeftLocalizer : LocalizerMorphism realizationWeakEquivalences
    (realizationWeakEquivalences.inverseImage N) where
  functor := L
  map _ _ f hf := ThomasonAdjunction.left_preserves_weakEquivalences adj kq a f hf

/-- The original counit is a Street weak equivalence, detected using the
triangle identity and the exact twice-extension weak criterion. -/
theorem thomason_counit_weak
    (hu : ∀ X, realizationWeakEquivalences (adj.unit.app X)) (Y : C) :
    (realizationWeakEquivalences.inverseImage N) (adj.counit.app Y) := by
  apply (realization_ex_twice_iff canonicalExtension_weak _).mp
  exact right_counit_weak_of_unit adj realizationWeakEquivalences hu Y

include a in
/-- The actual `Ex² N` functor induces an equivalence of localized categories. -/
theorem thomasonRightLocalizer_equivalence_of_weak_unit
    (hu : ∀ X, realizationWeakEquivalences (adj.unit.app X)) :
    (thomasonRightLocalizer N kq canonicalExtension_weak).IsLocalizedEquivalence :=
  localizer_equivalence_of_weak_unit_counit
    (thomasonRightLocalizer N kq canonicalExtension_weak)
    (thomasonLeftLocalizer adj kq a) adj hu (thomason_counit_weak adj hu)

end General

namespace NormalizedSimplexIdentities

variable (h : NormalizedSimplexIdentities) [StrictColimitsInput]

/-- Omega-dimensional localization follows from the prescribed model
axioms and the finite-poset unit comparison. -/
theorem thomason_localized_equivalence
    (kq : KanQuillenPublishedInput.{0})
    (a : ProperCombinatorialAxioms StrictOmegaCategory.{0} h.streetWeakEquivalences
      h.thomasonFibrations)
    (hu : ∀ (P : Type) [PartialOrder P] [Finite P],
      realizationWeakEquivalences (h.categorificationAdjunction.unit.app (nerve P))) :
    (thomasonRightLocalizer h.streetNerve kq canonicalExtension_weak).IsLocalizedEquivalence :=
  thomasonRightLocalizer_equivalence_of_weak_unit h.thomasonAdjunction kq a
    (h.thomason_unit_weak kq a hu)

end NormalizedSimplexIdentities

namespace FiniteReflectionInput

variable {n : ℕ} (r : FiniteReflectionInput n)
    (h : NormalizedSimplexIdentities) [StrictColimitsInput]

/-- The same localization equivalence in each positive finite dimension. -/
theorem thomason_localized_equivalence
    (kq : KanQuillenPublishedInput.{0})
    (a : ProperCombinatorialAxioms (StrictOmegaCategory.Truncated.{0} (n+1))
      (thomasonWeakEquivalences (n := n) h) (thomasonFibrations (n := n) h))
    (hu : ∀ (P : Type) [PartialOrder P] [Finite P],
      realizationWeakEquivalences ((r.categorificationAdjunction h).unit.app (nerve P))) :
    (thomasonRightLocalizer (h.finiteStreetNerve (n+1)) kq
      canonicalExtension_weak).IsLocalizedEquivalence :=
  thomasonRightLocalizer_equivalence_of_weak_unit (r.thomasonAdjunction h) kq a
    (r.thomason_unit_weak h kq a hu)

end FiniteReflectionInput

end

end Thomason.Construction

end

section

/-! # The original Street-localization input follows from the constructed models

Cancelling the known extension equivalences from `Ex² N` gives the actual
Street nerve itself. This recovers exactly the former published input,
including every positive finite dimension.
-/

namespace Thomason.Construction

open CategoryTheory CategoryTheory.Functor

universe u₁ u₂ u₃ v₁ v₂ v₃

section Cancellation

variable {C₁ : Type u₁} {C₂ : Type u₂} {C₃ : Type u₃}
    [Category.{v₁} C₁] [Category.{v₂} C₂] [Category.{v₃} C₃]
    {W₁ : MorphismProperty C₁} {W₂ : MorphismProperty C₂} {W₃ : MorphismProperty C₃}

/-- Cancellation on the right holds for equivalences of the actual localized categories. -/
theorem localizedEquivalence_cancel_right
    (Φ : LocalizerMorphism W₁ W₂) (Ψ : LocalizerMorphism W₂ W₃)
    [Ψ.IsLocalizedEquivalence] [(Φ.comp Ψ).IsLocalizedEquivalence] :
    Φ.IsLocalizedEquivalence := by
  let F := Φ.localizedFunctor W₁.Q W₂.Q
  let G := Ψ.localizedFunctor W₂.Q W₃.Q
  let : CatCommSq (Φ.comp Ψ).functor W₁.Q W₃.Q (F ⋙ G) :=
    CatCommSq.hComp Φ.functor Ψ.functor W₁.Q W₂.Q W₃.Q F G
  have : (F ⋙ G).IsEquivalence :=
    (Φ.comp Ψ).isEquivalence W₁.Q W₃.Q (F ⋙ G)
  have : F.IsEquivalence := Functor.isEquivalence_of_comp_right F G
  exact LocalizerMorphism.IsLocalizedEquivalence.mk' Φ W₁.Q W₂.Q F

end Cancellation

/-- Twice extension can be cancelled from the localized nerve comparison. -/
theorem nerveLocalizer_equivalence_of_thomasonRight
    {C : Type*} [Category* C] (N : C ⥤ SSet.{0})
    (kq : KanQuillenPublishedInput.{0})
    (hR : (thomasonRightLocalizer N kq canonicalExtension_weak).IsLocalizedEquivalence) :
    (nerveLocalizer N).IsLocalizedEquivalence := by
  let E := extensionLocalizer kq canonicalExtension_weak
  have : E.IsLocalizedEquivalence :=
    extensionLocalizer_isLocalizedEquivalence kq canonicalExtension_weak
  have : (((nerveLocalizer N).comp E).comp E).IsLocalizedEquivalence := hR
  have : ((nerveLocalizer N).comp E).IsLocalizedEquivalence :=
    localizedEquivalence_cancel_right ((nerveLocalizer N).comp E) E
  exact localizedEquivalence_cancel_right (nerveLocalizer N) E

namespace NormalizedSimplexIdentities

variable (h : NormalizedSimplexIdentities) [StrictColimitsInput]

/-- The omega Street nerve is an equivalence after localization. -/
theorem street_localized_equivalence
    (kq : KanQuillenPublishedInput.{0})
    (a : ProperCombinatorialAxioms StrictOmegaCategory.{0} h.streetWeakEquivalences
      h.thomasonFibrations)
    (hu : ∀ (P : Type) [PartialOrder P] [Finite P],
      realizationWeakEquivalences (h.categorificationAdjunction.unit.app (nerve P))) :
    (nerveLocalizer h.streetNerve).IsLocalizedEquivalence :=
  nerveLocalizer_equivalence_of_thomasonRight h.streetNerve kq
    (h.thomason_localized_equivalence kq a hu)

end NormalizedSimplexIdentities

namespace FiniteReflectionInput

variable {n : ℕ} (r : FiniteReflectionInput n)
    (h : NormalizedSimplexIdentities) [StrictColimitsInput]

/-- The positive finite-dimensional Street nerve is an equivalence after localization. -/
theorem street_localized_equivalence
    (kq : KanQuillenPublishedInput.{0})
    (a : ProperCombinatorialAxioms (StrictOmegaCategory.Truncated.{0} (n+1))
      (thomasonWeakEquivalences (n := n) h) (thomasonFibrations (n := n) h))
    (hu : ∀ (P : Type) [PartialOrder P] [Finite P],
      realizationWeakEquivalences ((r.categorificationAdjunction h).unit.app (nerve P))) :
    (nerveLocalizer (h.finiteStreetNerve (n+1))).IsLocalizedEquivalence :=
  nerveLocalizer_equivalence_of_thomasonRight (h.finiteStreetNerve (n+1)) kq
    (r.thomason_localized_equivalence h kq a hu)

end FiniteReflectionInput

/-- The literal former published localization input is supplied by the
actual model axioms and finite-poset units. -/
theorem streetLocalizationInput_of_models
    (h : NormalizedSimplexIdentities) [StrictColimitsInput]
    (kq : KanQuillenPublishedInput.{0}) (r : ∀ n, FiniteReflectionInput n)
    (aω : ProperCombinatorialAxioms StrictOmegaCategory.{0} h.streetWeakEquivalences
      h.thomasonFibrations)
    (af : ∀ n, ProperCombinatorialAxioms (StrictOmegaCategory.Truncated.{0} (n+1))
      (FiniteReflectionInput.thomasonWeakEquivalences (n := n) h)
      (FiniteReflectionInput.thomasonFibrations (n := n) h))
    (units : PublishedFinitePosetUnitInput h) : PublishedStreetLocalizationInput h where
  omega := h.street_localized_equivalence kq aω units.omega
  finite n := (r n).street_localized_equivalence h kq (af n) (units.finite n (r n))

end Thomason.Construction

end

end OAI
