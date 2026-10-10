import Mathlib
import OAI.CategoryTheory.Thomason.GreatestAttachments

namespace OAI

/-! Couniversality. -/

noncomputable section
universe u v w z


namespace Thomason.Couniversality
open CategoryTheory Limits OmegaCategory

lemma greatest_or_two_maximal {P : Type u} [PartialOrder P] [Finite P]
    (S : Set P) (hne : S.Nonempty) :
    (∃ x, IsGreatest S x) ∨
      ∃ x y, Maximal (· ∈ S) x ∧ Maximal (· ∈ S) y ∧ x ≠ y := by
  classical
  by_cases hg : ∃ x, IsGreatest S x
  · exact Or.inl hg
  right
  obtain ⟨x,hx⟩ := S.toFinite.exists_maximal hne
  have hn : ¬ ∀ z ∈ S, z ≤ x := fun h => hg ⟨x,hx.1,h⟩
  push Not at hn
  obtain ⟨z,hz,hzx⟩ := hn
  obtain ⟨y,hzy,hy⟩ := S.toFinite.exists_le_maximal hz
  exact ⟨x,y,hx,hy,fun hxy => hzx (hxy ▸ hzy)⟩

lemma maximal_new_isMax {P : Type u} [PartialOrder P]
    {A : Set P} (hA : IsLowerSet A) {x : P} (hx : Maximal (· ∈ Aᶜ) x) : IsMax x := by
  intro y hxy
  exact hx.2 (fun hy => hx.1 (hA hxy hy)) hxy

lemma delete_max_lower {P : Type u} [PartialOrder P] {x : P} (hx : IsMax x) :
    IsLowerSet ({x}ᶜ : Set P) := by
  intro a b hab hb
  change b ≠ x
  intro he
  subst b
  exact hb (le_antisymm (hx hab) hab)

def nestedOldIso {D : Type v} [Category.{w} D] (F : SSet.{u} ⥤ D)
    {P : Type u} [PartialOrder P] (A S : Set P) (hAS : A ⊆ S) :
    F.obj (nerve {s : S | s.val ∈ A}) ≅ F.obj (nerve A) where
  hom := F.map (nerveMap (show {s : S | s.val ∈ A} →o A from
    ⟨fun a => ⟨a.val.val,a.property⟩,fun _ _ h => h⟩).toFunctor)
  inv := F.map (nerveMap (show A →o {s : S | s.val ∈ A} from
    ⟨fun a => ⟨⟨a.val,hAS a.property⟩,a.property⟩,fun _ _ h => h⟩).toFunctor)
  hom_inv_id := by
    rw [← F.map_comp]
    exact F.map_id _
  inv_hom_id := by
    rw [← F.map_comp]
    exact F.map_id _

lemma nestedOldIso_inc {D : Type v} [Category.{w} D] (F : SSet.{u} ⥤ D)
    {P : Type u} [PartialOrder P] (A S : Set P) (hAS : A ⊆ S) :
    (nestedOldIso F A S hAS).hom ≫
      F.map (nerveMap (Attachments.subposetMap A S hAS).toFunctor) =
      F.map (nerveMap (OrderEmbedding.subtype {s : S | s.val ∈ A}).toOrderHom.toFunctor) := by
  rw [nestedOldIso, ← F.map_comp]
  rfl

lemma restricted_lower {P : Type u} [PartialOrder P] {A : Set P}
    (hA : IsLowerSet A) (S : Set P) : IsLowerSet {s : S | s.val ∈ A} :=
  fun _ _ h ha => hA h ha

def restrictedRetract {P : Type u} [PartialOrder P] (A S : Set P)
    (hAS : A ⊆ S) (r : P →o A) : S →o {s : S | s.val ∈ A} :=
  ⟨fun e => ⟨⟨(r e.val).val,hAS (r e.val).property⟩,(r e.val).property⟩,
    fun _ _ h => r.monotone h⟩

lemma restricted_adjoint {P : Type u} [PartialOrder P] (A S : Set P)
    (hAS : A ⊆ S) (r : P →o A)
    (hadj : ∀ (a : A) (e : P), a.val ≤ e ↔ a ≤ r e) :
    ∀ (a : {s : S | s.val ∈ A}) (e : S),
      a.val ≤ e ↔ a ≤ restrictedRetract A S hAS r e := by
  intro a e
  exact hadj ⟨a.val.val,a.property⟩ e.val

lemma weak_of_full_sieve_cover {C : OmegaCategory.{u}} {S T : Set C.Objects}
    (hS : C.IsObjectSieve S) (hT : C.IsObjectSieve T)
    (hc : S ∪ T = Set.univ) {X : SSet.{u}} (j : X ⟶ streetNerve C)
    (jS : X ⟶ streetNerve (C.fullOn S).category)
    (jT : X ⟶ streetNerve (C.fullOn T).category)
    (jI : X ⟶ streetNerve (C.fullOn (S ∩ T)).category)
    (heS : jS ≫ streetNerveMap (C.fullOn S).inclusion = j)
    (heT : jT ≫ streetNerveMap (C.fullOn T).inclusion = j)
    (heI : jI ≫ streetNerveMap (C.fullOn (S ∩ T)).inclusion = j)
    (hwS : simplicialWeakEquivalences jS)
    (hwT : simplicialWeakEquivalences jT)
    (hwI : simplicialWeakEquivalences jI) : simplicialWeakEquivalences j := by
  let pS := streetNerveMap (fullOnMap (Set.inter_subset_left (s := S) (t := T)))
  let pT := streetNerveMap (fullOnMap (Set.inter_subset_right (s := S) (t := T)))
  have he : jI ≫ pS = jS := by
    apply (cancel_mono (streetNerveMap (C.fullOn S).inclusion)).mp
    rw [Category.assoc, heS]
    exact heI
  have hw : simplicialWeakEquivalences pS :=
    simplicialWeakEquivalences.of_precomp jI pS hwI (he ▸ hwS)
  have sq := sieve_cover_nerve_isPushout hS hT (fun a => by
    have ha : a ∈ S ∪ T := by rw [hc]; trivial
    exact ha)
  have hwT' : simplicialWeakEquivalences (streetNerveMap (C.fullOn T).inclusion) :=
    GeometricRecognition.left_proper _ _ _ _ sq.flip (by infer_instance) hw
  rw [← heT]
  exact simplicialWeakEquivalences.comp_mem _ _ hwT hwT'

end Thomason.Couniversality

end

noncomputable section
universe u v w z


namespace Thomason.Couniversality
open CategoryTheory Limits OmegaCategory Attachments AttachmentComparison

lemma isIso_subtype_all {D : Type v} [Category.{w} D] (F : SSet.{u} ⥤ D)
    {E : Type u} [PartialOrder E] (A : Set E) (ha : ∀ e, e ∈ A) :
    IsIso (F.map (nerveMap (OrderEmbedding.subtype (fun element : E => element ∈ A)).toOrderHom.toFunctor)) := by
  let r : E →o A := ⟨fun e => ⟨e, ha e⟩,fun _ _ h => h⟩
  refine ⟨⟨F.map (nerveMap r.toFunctor), ?_, ?_⟩⟩ <;>
    rw [← F.map_comp] <;> exact F.map_id _

theorem finite_poset_couniversal
    (T : RightIntervalExtension.{u})
    (R : OmegaCategory.{u} ⥤ OmegaCategory.{u}) (adj : T.tensor ⊣ R)
    (n : ℕ) (hn : 1 ≤ n) {E : Type u} [PartialOrder E] [Finite E]
    (A : Set E) (hA : IsLowerSet A) (r : E →o A)
    (hadj : ∀ (a : A) (e : E), a.val ≤ e ↔ a ≤ r e)
    {X Y : NCategory.{u} n} {a : posetObj n A ⟶ X}
    {j : X ⟶ Y} {v : posetObj n E ⟶ Y} (sq : IsPushout a (inc n A) j v) :
    simplicialWeakEquivalences ((streetNerveFinite n).map j) := by
  classical
  suffices H : ∀ m : ℕ, ∀ (E : Type u) [PartialOrder E] [Finite E], Nat.card E = m →
      ∀ (A : Set E), IsLowerSet A → ∀ (r : E →o A),
      (∀ (a : A) (e : E), a.val ≤ e ↔ a ≤ r e) →
      ∀ {X Y : NCategory.{u} n} (a : posetObj n A ⟶ X) (j : X ⟶ Y)
        (v : posetObj n E ⟶ Y), IsPushout a (inc n A) j v →
        simplicialWeakEquivalences ((streetNerveFinite n).map j) from
    H (Nat.card E) E rfl A hA r hadj a j v sq
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro E _ _ hm A hA r hadj X Y a j v sq
    by_cases he : Aᶜ.Nonempty
    · rcases greatest_or_two_maximal Aᶜ he with ⟨x,hx⟩ | ⟨x,y,hx,hy,hxy⟩
      · exact GreatestNew.finite_pushout_nerve_weak T R adj A hA r hadj x hx n sq.flip
      · let S₁ : Set E := {x}ᶜ
        let S₂ : Set E := {y}ᶜ
        have h₁ : IsLowerSet S₁ := delete_max_lower (maximal_new_isMax hA hx)
        have h₂ : IsLowerSet S₂ := delete_max_lower (maximal_new_isMax hA hy)
        have hA₁ : A ⊆ S₁ := by
          intro z hz heq
          change z = x at heq
          exact hx.1 (heq ▸ hz)
        have hA₂ : A ⊆ S₂ := by
          intro z hz heq
          change z = y at heq
          exact hy.1 (heq ▸ hz)
        have hc : S₁ ∪ S₂ = Set.univ := by
          apply Set.eq_univ_of_forall
          intro z
          change z ≠ x ∨ z ≠ y
          by_cases hz : z = x
          · exact Or.inr (fun heq => hxy (hz.symm.trans heq))
          · exact Or.inl hz
        obtain ⟨T₁,T₂,hT₁,hT₂,hTc,hp₁,hp₂,hp₃⟩ :=
          sieve_finite_attachment_covers n hn A S₁ S₂ h₁ h₂ hA₁ hA₂ hc a j v sq
        have hpiece (S : Set E) (hAS : A ⊆ S) (e : E) (he : e ∉ S)
            (Z : Set Y.val.Objects) (hp : IsPosetFiniteAttachmentPiece n A S hAS a j v Z) :
            ∃ (jS : X ⟶ fullFinite n Y Z), jS ≫ fullFiniteInclusion n Y Z = j ∧
              simplicialWeakEquivalences ((streetNerveFinite n).map jS) := by
          obtain ⟨jS,vS,hjS,hvS,sqS⟩ := hp
          refine ⟨jS,hjS,?_⟩
          let eS := nestedOldIso (categorificationFinite n) A S hAS
          have sqS' : IsPushout (eS.hom ≫ a) (inc n {s : S | s.val ∈ A}) jS vS := by
            apply sqS.of_iso' eS (Iso.refl _) (Iso.refl _) (Iso.refl _)
            · simp
            · simp only [Iso.refl_hom, Category.comp_id]
              exact nestedOldIso_inc (categorificationFinite n) A S hAS
            · simp
            · simp
          exact ih (Nat.card S) (hm ▸ Finite.card_subtype_lt he) S rfl
            {s : S | s.val ∈ A} (restricted_lower hA S)
            (restrictedRetract A S hAS r) (restricted_adjoint A S hAS r hadj)
            (eS.hom ≫ a) jS vS sqS'
        obtain ⟨j₁,hj₁,hw₁⟩ := hpiece S₁ hA₁ x (by simp [S₁]) T₁ hp₁
        obtain ⟨j₂,hj₂,hw₂⟩ := hpiece S₂ hA₂ y (by simp [S₂]) T₂ hp₂
        obtain ⟨j₃,hj₃,hw₃⟩ := hpiece (S₁ ∩ S₂) (fun _ ha => ⟨hA₁ ha,hA₂ ha⟩)
          x (by simp [S₁]) (T₁ ∩ T₂) hp₃
        apply weak_of_full_sieve_cover hT₁ hT₂ hTc ((streetNerveFinite n).map j)
          ((streetNerveFinite n).map j₁) ((streetNerveFinite n).map j₂)
          ((streetNerveFinite n).map j₃) _ _ _ hw₁ hw₂ hw₃
        · exact (Functor.map_comp (streetNerveFinite n) _ _).symm.trans
            (congrArg (fun f : X ⟶ Y => (streetNerveFinite n).map f) hj₁)
        · exact (Functor.map_comp (streetNerveFinite n) _ _).symm.trans
            (congrArg (fun f : X ⟶ Y => (streetNerveFinite n).map f) hj₂)
        · exact (Functor.map_comp (streetNerveFinite n) _ _).symm.trans
            (congrArg (fun f : X ⟶ Y => (streetNerveFinite n).map f) hj₃)
    · have ha : ∀ e, e ∈ A := by
        intro e
        by_contra h
        exact he ⟨e,h⟩
      have : IsIso (inc n A) := isIso_subtype_all (categorificationFinite n) A ha
      have : IsIso j := sq.isIso_inl_of_isIso
      exact simplicialWeakEquivalences.of_isIso _

end Thomason.Couniversality

end

noncomputable section
universe u v w z


namespace Thomason.Couniversality
open CategoryTheory Limits OmegaCategory Attachments AttachmentComparison GreatestNew

theorem omega_finite_poset_couniversal
    (T : RightIntervalExtension.{u})
    {E : Type u} [PartialOrder E] [Finite E]
    (A : Set E) (hA : IsLowerSet A) (r : E →o A)
    (hadj : ∀ (a : A) (e : E), a.val ≤ e ↔ a ≤ r e)
    {X Y : OmegaCategory.{u}} {a : omegaPosetObj A ⟶ X}
    {j : X ⟶ Y} {v : omegaPosetObj E ⟶ Y} (sq : IsPushout a (omegaInc A) j v) :
    simplicialWeakEquivalences (streetNerveFunctor.map j) := by
  classical
  suffices H : ∀ m : ℕ, ∀ (E : Type u) [PartialOrder E] [Finite E], Nat.card E = m →
      ∀ (A : Set E), IsLowerSet A → ∀ (r : E →o A),
      (∀ (a : A) (e : E), a.val ≤ e ↔ a ≤ r e) →
      ∀ {X Y : OmegaCategory.{u}} (a : omegaPosetObj A ⟶ X) (j : X ⟶ Y)
        (v : omegaPosetObj E ⟶ Y), IsPushout a (omegaInc A) j v →
        simplicialWeakEquivalences (streetNerveFunctor.map j) from
    H (Nat.card E) E rfl A hA r hadj a j v sq
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro E _ _ hm A hA r hadj X Y a j v sq
    by_cases he : Aᶜ.Nonempty
    · rcases greatest_or_two_maximal Aᶜ he with ⟨x,hx⟩ | ⟨x,y,hx,hy,hxy⟩
      · exact GreatestNew.omega_pushout_nerve_weak T A hA r hadj x hx sq.flip
      · let S₁ : Set E := {x}ᶜ
        let S₂ : Set E := {y}ᶜ
        have h₁ : IsLowerSet S₁ := delete_max_lower (maximal_new_isMax hA hx)
        have h₂ : IsLowerSet S₂ := delete_max_lower (maximal_new_isMax hA hy)
        have hA₁ : A ⊆ S₁ := by
          intro z hz heq
          change z = x at heq
          exact hx.1 (heq ▸ hz)
        have hA₂ : A ⊆ S₂ := by
          intro z hz heq
          change z = y at heq
          exact hy.1 (heq ▸ hz)
        have hc : S₁ ∪ S₂ = Set.univ := by
          apply Set.eq_univ_of_forall
          intro z
          change z ≠ x ∨ z ≠ y
          by_cases hz : z = x
          · exact Or.inr (fun heq => hxy (hz.symm.trans heq))
          · exact Or.inl hz
        obtain ⟨T₁,T₂,hT₁,hT₂,hTc,hp₁,hp₂,hp₃⟩ :=
          sieve_attachment_covers A S₁ S₂ h₁ h₂ hA₁ hA₂ hc a j v sq
        have hpiece (S : Set E) (hAS : A ⊆ S) (e : E) (he : e ∉ S)
            (Z : Set Y.Objects) (hp : IsPosetAttachmentPiece A S hAS a j v Z) :
            ∃ (jS : X ⟶ (Y.fullOn Z).category), jS ≫ (Y.fullOn Z).inclusion = j ∧
              simplicialWeakEquivalences (streetNerveFunctor.map jS) := by
          obtain ⟨jS,vS,hjS,hvS,sqS⟩ := hp
          refine ⟨jS,hjS,?_⟩
          let eS := nestedOldIso categorification A S hAS
          have sqS' : IsPushout (eS.hom ≫ a) (omegaInc {s : S | s.val ∈ A}) jS vS := by
            apply sqS.of_iso' eS (Iso.refl _) (Iso.refl _) (Iso.refl _)
            · simp
            · simp only [Iso.refl_hom, Category.comp_id]
              exact nestedOldIso_inc categorification A S hAS
            · simp
            · simp
          exact ih (Nat.card S) (hm ▸ Finite.card_subtype_lt he) S rfl
            {s : S | s.val ∈ A} (restricted_lower hA S)
            (restrictedRetract A S hAS r) (restricted_adjoint A S hAS r hadj)
            (eS.hom ≫ a) jS vS sqS'
        obtain ⟨j₁,hj₁,hw₁⟩ := hpiece S₁ hA₁ x (by simp [S₁]) T₁ hp₁
        obtain ⟨j₂,hj₂,hw₂⟩ := hpiece S₂ hA₂ y (by simp [S₂]) T₂ hp₂
        obtain ⟨j₃,hj₃,hw₃⟩ := hpiece (S₁ ∩ S₂) (fun _ ha => ⟨hA₁ ha,hA₂ ha⟩)
          x (by simp [S₁]) (T₁ ∩ T₂) hp₃
        apply weak_of_full_sieve_cover hT₁ hT₂ hTc (streetNerveFunctor.map j)
          (streetNerveFunctor.map j₁) (streetNerveFunctor.map j₂)
          (streetNerveFunctor.map j₃) _ _ _ hw₁ hw₂ hw₃
        · exact (Functor.map_comp streetNerveFunctor _ _).symm.trans
            (congrArg (fun f : X ⟶ Y => streetNerveFunctor.map f) hj₁)
        · exact (Functor.map_comp streetNerveFunctor _ _).symm.trans
            (congrArg (fun f : X ⟶ Y => streetNerveFunctor.map f) hj₂)
        · exact (Functor.map_comp streetNerveFunctor _ _).symm.trans
            (congrArg (fun f : X ⟶ Y => streetNerveFunctor.map f) hj₃)
    · have ha : ∀ e, e ∈ A := by
        intro e
        by_contra h
        exact he ⟨e,h⟩
      have : IsIso (omegaInc A) := isIso_subtype_all categorification A ha
      have : IsIso j := sq.isIso_inl_of_isIso
      exact simplicialWeakEquivalences.of_isIso _

end Thomason.Couniversality

end

noncomputable section
universe u v w z


namespace Thomason.AttachmentComparison
open CategoryTheory Limits OmegaCategory Attachments Couniversality

lemma finite_nerve_attachment_mono (n : ℕ) (hn : 1 ≤ n)
    {B : Type u} [PartialOrder B] (A : Set B) (hA : IsLowerSet A)
    {X Y : NCategory.{u} n} (a : posetObj n A ⟶ X)
    (j : X ⟶ Y) (v : posetObj n B ⟶ Y) (sc : IsPushout a (inc n A) j v) :
    Mono ((streetNerveFinite n).map j) := by
  obtain ⟨S,hS,e,he⟩ := poset_finite_sieve_attachment n hn A hA a j v sc
  have hinc := OmegaCategory.Subcategory.inclusion_mono (Y.val.fullOn S)
  have hj : Mono ((nCategoryInclusion n).map j) := by
    change @Mono OmegaCategory inferInstance X.val Y.val j
    rw [← he]
    infer_instance
  have : Mono j := (nCategoryInclusion n).mono_of_mono_map hj
  let : PreservesLimits (streetNerveFinite n) :=
    (categorificationFiniteAdjunction n).rightAdjoint_preservesLimits
  infer_instance

lemma finite_nerve_upper_mono (n : ℕ) (hn : 1 ≤ n)
    {P : Type u} [PartialOrder P] (S : Set P) (hS : IsUpperSet S) :
    Mono ((streetNerveFinite n).map (inc n S)) := by
  let l := NormalizedChains.PosetTables.upperSegmentLabel S hS
  have hS' : S = {p | l p = 1} := by
    ext p
    exact (NormalizedChains.PosetTables.upperSegmentLabel_one S hS p).symm
  let e := posetPieceFiniteFiberIso n hn S l 1 hS'
  have he := posetPieceFiniteFiberIso_inclusion n hn S l 1 hS'
  have := fiberFiniteInclusion_mono n hn 1
    (Over.mk (posetCategorificationFiniteLabel n hn l))
  have : Mono (inc n S) := by
    change Mono ((categorificationFinite n).map
      (nerveMap (OrderEmbedding.subtype (fun element : P => element ∈ S)).toOrderHom.monotone.functor))
    rw [← he]
    infer_instance
  let : PreservesLimits (streetNerveFinite n) :=
    (categorificationFiniteAdjunction n).rightAdjoint_preservesLimits
  infer_instance

lemma finite_nerve_inter_upper_mono (n : ℕ) (hn : 1 ≤ n)
    {P : Type u} [PartialOrder P] (Z C : Set P) (hZ : IsUpperSet Z) :
    Mono ((streetNerveFinite n).map (sb n (Z ∩ C) C Set.inter_subset_right)) := by
  let e := nestedOldIso (categorificationFinite n) (Z ∩ C) C Set.inter_subset_right
  have : Mono ((streetNerveFinite n).map (inc n {c : C | c.val ∈ Z ∩ C})) :=
    finite_nerve_upper_mono n hn _ (by
      intro x y hxy hx
      exact ⟨hZ hxy hx.1,y.property⟩)
  have he : sb n (Z ∩ C) C Set.inter_subset_right =
      e.inv ≫ inc n {c : C | c.val ∈ Z ∩ C} := by
    calc
      _ = e.inv ≫ (e.hom ≫ sb n (Z ∩ C) C Set.inter_subset_right) := by simp
      _ = _ := congrArg (e.inv ≫ ·) (nestedOldIso_inc
        (categorificationFinite n) (Z ∩ C) C Set.inter_subset_right)
  rw [he, CategoryTheory.Functor.map_comp]
  infer_instance

lemma finite_piece_couniversal (T : RightIntervalExtension.{u})
    (R : OmegaCategory.{u} ⥤ OmegaCategory.{u}) (adj : T.tensor ⊣ R)
    (n : ℕ) (hn : 1 ≤ n) {B : Type u} [PartialOrder B]
    (A S : Set B) [Finite S] (hA : IsLowerSet A) (hAS : A ⊆ S)
    (r : S →o A) (hadj : ∀ (a : A) (s : S), a.val ≤ s.val ↔ a ≤ r s)
    {X Y : NCategory.{u} n} (a : posetObj n A ⟶ X)
    (j : X ⟶ Y) (v : posetObj n S ⟶ Y)
    (sq : IsPushout a (sb n A S hAS) j v) :
    simplicialWeakEquivalences ((streetNerveFinite n).map j) := by
  let e := nestedOldIso (categorificationFinite n) A S hAS
  let r' : S →o {s : S | s.val ∈ A} :=
    ⟨fun s => ⟨⟨(r s).val,hAS (r s).property⟩,(r s).property⟩,
      fun _ _ h => r.monotone h⟩
  have sq' : IsPushout (e.hom ≫ a) (inc n {s : S | s.val ∈ A}) j v := by
    apply sq.of_iso' e (Iso.refl _) (Iso.refl _) (Iso.refl _)
    · simp
    · simp only [Iso.refl_hom,Category.comp_id]
      exact nestedOldIso_inc (categorificationFinite n) A S hAS
    · simp
    · simp
  exact finite_poset_couniversal T R adj n hn {s : S | s.val ∈ A}
    (restricted_lower hA S) r' (fun a s => hadj ⟨a.val.val,a.property⟩ s) sq'

lemma comparison_local_finite_poset (T : RightIntervalExtension.{u})
    (R : OmegaCategory.{u} ⥤ OmegaCategory.{u}) (adj : T.tensor ⊣ R)
    (n : ℕ) (hn : 1 ≤ n) {B : Type u} [PartialOrder B] [Finite B]
    (A : Set B) (hA : IsLowerSet A)
    (r : upward A →o A)
    (hadj : ∀ (a : A) (z : upward A), a.val ≤ z.val ↔ a ≤ r z)
    {X Y : NCategory.{u} n} (a : posetObj n A ⟶ X)
    (j : X ⟶ Y) (v : posetObj n B ⟶ Y) (sc : IsPushout a (inc n A) j v)
    {P : SSet.{u}} {lX : (streetNerveFinite n).obj X ⟶ P}
    {lB : (streetNerveFinite n).obj (posetObj n B) ⟶ P}
    (ss : IsPushout ((streetNerveFinite n).map a) ((streetNerveFinite n).map (inc n A)) lX lB)
    (F : P ⟶ (streetNerveFinite n).obj Y)
    (hFX : lX ≫ F = (streetNerveFinite n).map j)
    (hFB : lB ≫ F = (streetNerveFinite n).map v) : simplicialWeakEquivalences F := by
  let Z := upward A
  let C := Aᶜ
  have hAZ : A ⊆ Z := fun x hx => ⟨x,hx,le_rfl⟩
  have hZ : IsUpperSet Z := by
    intro x y hxy hx
    obtain ⟨a,ha,hax⟩ := hx
    exact ⟨a,ha,hax.trans hxy⟩
  have hC : IsUpperSet C := isUpperSet_compl.mpr hA
  have hcov : Z ∪ C = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    by_cases hx : x ∈ A
    · exact Or.inl (hAZ hx)
    · exact Or.inr hx
  obtain ⟨YZ,jZ,vZ,uZ,scZ,hj,hv,sq⟩ :=
    attachment_nerve_cover n hn A Z C hZ hC hAZ disjoint_compl_right hcov a j v sc
  let N := streetNerveFinite n
  let e := N.map (sb n A Z hAZ)
  let b := N.map a
  let PZ := pushout b e
  let xZ := pushout.inl b e
  let zZ := pushout.inr b e
  let sZ := IsPushout.of_hasPushout b e
  let FZ : PZ ⟶ N.obj YZ := sZ.desc (N.map jZ) (N.map vZ) (by
    rw [← N.map_comp, ← N.map_comp, scZ.w])
  have hFZX : xZ ≫ FZ = N.map jZ := sZ.inl_desc _ _ _
  have hFZZ : zZ ≫ FZ = N.map vZ := sZ.inr_desc _ _ _
  have hwj : simplicialWeakEquivalences (N.map jZ) :=
    finite_piece_couniversal T R adj n hn A Z hA hAZ r hadj a jZ vZ scZ
  have hwe : simplicialWeakEquivalences e :=
    finite_piece_couniversal T R adj n hn A Z hA hAZ r hadj
      (𝟙 _) (sb n A Z hAZ) (𝟙 _) IsPushout.of_id_fst
  have hcE : Mono e := by
    let e' := nestedOldIso (categorificationFinite n) A Z hAZ
    have he' : sb n A Z hAZ = e'.inv ≫ inc n {z : Z | z.val ∈ A} := by
      calc
        _ = e'.inv ≫ (e'.hom ≫ sb n A Z hAZ) := by simp
        _ = _ := congrArg (e'.inv ≫ ·) (nestedOldIso_inc (categorificationFinite n) A Z hAZ)
    have : Mono (N.map (inc n {z : Z | z.val ∈ A})) :=
      finite_nerve_attachment_mono n hn _ (restricted_lower hA Z)
        (𝟙 _) _ (𝟙 _) IsPushout.of_id_fst
    dsimp [e]
    rw [he',CategoryTheory.Functor.map_comp]
    infer_instance
  have hwx : simplicialWeakEquivalences xZ := by
    have he : SSet.anodyneExtensions e := KanQuillen.anodyne_class.symm ▸ ⟨hcE,hwe⟩
    exact KanQuillen.anodyne_weak _ (SSet.anodyneExtensions.of_isPushout sZ he)
  have hwFZ : simplicialWeakEquivalences FZ :=
    simplicialWeakEquivalences.of_precomp xZ FZ hwx (hFZX ▸ hwj)
  let pZ : PZ ⟶ P := sZ.desc lX (N.map (inc n Z) ≫ lB) (by
    rw [← Category.assoc, ← N.map_comp, sb_inc]
    exact ss.w)
  have hpZX : xZ ≫ pZ = lX := sZ.inl_desc _ _ _
  have hpZZ : zZ ≫ pZ = N.map (inc n Z) ≫ lB := sZ.inr_desc _ _ _
  have ss' : IsPushout b (e ≫ N.map (inc n Z)) (xZ ≫ pZ) lB := by
    rw [hpZX, ← N.map_comp, sb_inc]
    exact ss
  have sr : IsPushout zZ (N.map (inc n Z)) pZ lB := ss'.of_top hpZZ sZ
  have sp := (poset_nerve_cover n hn Z C hZ hC hcov).paste_horiz sr
  let k := N.map (sb n (Z ∩ C) Z Set.inter_subset_left) ≫ zZ
  let c := N.map (sb n (Z ∩ C) C Set.inter_subset_right)
  have hc : Mono c := finite_nerve_inter_upper_mono n hn Z C hZ
  have hk : k ≫ FZ = N.map (sb n (Z ∩ C) Z Set.inter_subset_left ≫ vZ) := by
    rw [show k = N.map (sb n (Z ∩ C) Z Set.inter_subset_left) ≫ zZ from rfl,
      Category.assoc, hFZZ, ← N.map_comp]
  have sq' : IsPushout (k ≫ FZ) c (N.map uZ) (N.map (inc n C ≫ v)) := by
    rw [hk]
    exact sq
  have hFpZ : pZ ≫ F = FZ ≫ N.map uZ := by
    apply sZ.hom_ext
    · rw [← Category.assoc, hpZX, ← Category.assoc xZ, hFZX, ← N.map_comp, hj]
      exact hFX
    · rw [← Category.assoc, hpZZ, Category.assoc, hFB,
        ← Category.assoc zZ, hFZZ, ← N.map_comp, ← N.map_comp, hv]
  have hFC : (N.map (inc n C) ≫ lB) ≫ F = N.map (inc n C ≫ v) := by
    rw [Category.assoc, hFB, ← N.map_comp]
  exact KanLocal.local_weak F (KanLocal.local_pushout_map k c FZ
    (GeometricRecognition.weak_local FZ hwFZ) sp sq' F hFpZ hFC)

end Thomason.AttachmentComparison

end

noncomputable section
universe u v w z


namespace Thomason.FilteredWeak
open CategoryTheory Limits Opposite Simplicial MonoidalCategory CartesianMonoidalCategory MonoidalClosed
open KanPath LastVertexProof KanHomotopy HornSubdivision SSet.modelCategoryQuillen

lemma colimit_lifting {J : Type u} [Category.{u} J] [IsFiltered J]
    {A B : SSet.{u}} [A.Finite] [B.Finite]
    (i : A ⟶ B) {X Y : J ⥤ SSet.{u}} (p : X ⟶ Y)
    (hp : ∀ j, HasLiftingProperty i (p.app j)) :
    HasLiftingProperty i (colim.map p) := by
  constructor
  intro a b sq
  obtain ⟨n,an,han⟩ := exists_hom_of_preservesColimit_coyoneda (colimit.isColimit X) a
  obtain ⟨m,bm,hbm⟩ := exists_hom_of_preservesColimit_coyoneda (colimit.isColimit Y) b
  change an ≫ colimit.ι X n = a at han
  change bm ≫ colimit.ι Y m = b at hbm
  have he : (an ≫ p.app n) ≫ colimit.ι Y n = (i ≫ bm) ≫ colimit.ι Y m := by
    rw [Category.assoc,← ι_colimMap,← Category.assoc,han,Category.assoc,hbm]
    exact sq.w
  obtain ⟨k,s,t,hst⟩ := exists_eq_of_preservesColimit_coyoneda (colimit.isColimit Y)
    (an ≫ p.app n) (i ≫ bm) he
  let := hp k
  let q : CommSq (an ≫ X.map s) i (p.app k) (bm ≫ Y.map t) :=
    ⟨by rw [Category.assoc,p.naturality,← Category.assoc]; exact hst⟩
  refine ⟨⟨{l := q.lift ≫ colimit.ι X k,fac_left := ?_,fac_right := ?_}⟩⟩
  · rw [← Category.assoc,q.fac_left,Category.assoc,colimit.w,han]
  · change (q.lift ≫ colimit.ι X k) ≫ colimMap p = b
    rw [Category.assoc,ι_colimMap,← Category.assoc,q.fac_right,Category.assoc,colimit.w,hbm]

lemma boundary_rlp_colimit {J : Type u} [Category.{u} J] [IsFiltered J]
    {X Y : J ⥤ SSet.{u}} (p : X ⟶ Y) (hp : ∀ j, I.rlp (p.app j)) :
    I.rlp (colim.map p) := by
  rintro _ _ _ ⟨n⟩
  exact colimit_lifting (SSet.boundary n).ι p (fun j => hp j _ ⟨n⟩)

lemma eval₀_rlp (B : SSet.{u}) [SSet.KanComplex B] :
    (MorphismProperty.monomorphisms SSet).rlp (eval₀ B) := by
  intro D E i hi
  let : Mono i := hi
  constructor
  intro x y sq
  have hp : simplicialFibrations (terminal.from B) := by
    change J.rlp _
    rw [← fibrations_eq, ← HomotopicalAlgebra.fibration_iff]
    infer_instance
  obtain ⟨Q,hQ,h₀,_⟩ := cylinder_lift i (terminal.from B) hp 1 y
    (uncurryR x) (terminal.from _)
    (by rw [endpoint_zero, ← comp_eval₀]; exact sq.w)
    (by subsingleton) (by subsingleton)
  refine ⟨⟨{l := curryR Q, fac_left := ?_, fac_right := ?_}⟩⟩
  · apply uncurryR_injective
    rw [uncurryR_pre, uncurryR_curryR, hQ]
  · rw [comp_eval₀, uncurryR_curryR]
    simpa only [endpoint_zero] using h₀

lemma path_projection_rlp {A B : SSet.{u}} [SSet.KanComplex B] (f : A ⟶ B) :
    I.rlp (pullback.fst f (eval₀ B)) := by
  rw [← SSet.rlp_monomorphisms]
  exact MorphismProperty.of_isPullback (IsPullback.of_hasPullback f (eval₀ B)).flip (eval₀_rlp B)

@[simp] lemma path_map_id {A B : SSet.{u}} (f : A ⟶ B)
    (h : (𝟙 A) ≫ f = f ≫ (𝟙 B)) :
    KanPath.map (𝟙 A) (𝟙 B) h = 𝟙 (MappingPath f) := by
  apply pullback.hom_ext <;> simp

lemma const_natural {A B : SSet.{u}} (f : A ⟶ B) :
    const A ≫ (ihom Δ[1]).map f = f ≫ const B := by
  apply uncurryR_injective
  rw [uncurryR_post, uncurryR_pre]
  simp only [const, uncurryR_curryR, whiskerRight_fst]

@[reassoc] lemma path_map_left {A₁ A₀ B₁ B₀ : SSet.{u}}
    {f₁ : A₁ ⟶ B₁} {f₀ : A₀ ⟶ B₀}
    (a : A₁ ⟶ A₀) (b : B₁ ⟶ B₀) (h : a ≫ f₀ = f₁ ≫ b) :
    left f₁ ≫ KanPath.map a b h = a ≫ left f₀ := by
  apply pullback.hom_ext
  · simp only [Category.assoc, map_fst, left, pullback.lift_fst_assoc,
      pullback.lift_fst, Category.id_comp, Category.comp_id]
  · simp only [Category.assoc, map_snd, left, pullback.lift_snd_assoc, pullback.lift_snd]
    rw [const_natural, ← Category.assoc, ← h, Category.assoc]

def pathDiagram {J : Type u} [Category.{u} J]
    {X Y : J ⥤ SSet.{u}} (p : X ⟶ Y) : J ⥤ SSet.{u} where
  obj j := MappingPath (p.app j)
  map f := KanPath.map (X.map f) (Y.map f) (p.naturality f)
  map_id j := by
    apply pullback.hom_ext <;> simp
  map_comp f g := by
    apply pullback.hom_ext
    · simp
    · simp [CategoryTheory.Functor.map_comp]

def pathProjection {J : Type u} [Category.{u} J]
    {X Y : J ⥤ SSet.{u}} (p : X ⟶ Y) : pathDiagram p ⟶ X where
  app j := pullback.fst (p.app j) (eval₀ (Y.obj j))
  naturality _ _ f := map_fst _ _ (p.naturality f)

def pathLeft {J : Type u} [Category.{u} J]
    {X Y : J ⥤ SSet.{u}} (p : X ⟶ Y) : X ⟶ pathDiagram p where
  app j := left (p.app j)
  naturality _ _ f := (path_map_left _ _ (p.naturality f)).symm

def pathRight {J : Type u} [Category.{u} J]
    {X Y : J ⥤ SSet.{u}} (p : X ⟶ Y) : pathDiagram p ⟶ Y where
  app j := right (p.app j)
  naturality _ _ f := map_right _ _ (p.naturality f)

@[simp] lemma path_left_projection {J : Type u} [Category.{u} J]
    {X Y : J ⥤ SSet.{u}} (p : X ⟶ Y) :
    pathLeft p ≫ pathProjection p = 𝟙 X := by
  apply NatTrans.ext
  funext j
  exact pullback.lift_fst _ _ _

@[simp] lemma path_fac {J : Type u} [Category.{u} J]
    {X Y : J ⥤ SSet.{u}} (p : X ⟶ Y) : pathLeft p ≫ pathRight p = p := by
  apply NatTrans.ext
  funext j
  exact fac _

theorem kan_colimit_weak {J : Type u} [Category.{u} J] [IsFiltered J]
    {X Y : J ⥤ SSet.{u}} (p : X ⟶ Y)
    (hX : ∀ j, SSet.KanComplex (X.obj j)) (hY : ∀ j, SSet.KanComplex (Y.obj j))
    (hp : ∀ j, simplicialWeakEquivalences (p.app j)) :
    simplicialWeakEquivalences (colim.map p) := by
  have hproj : simplicialWeakEquivalences (colim.map (pathProjection p)) := by
    apply KanQuillen.boundary_right_weak
    apply boundary_rlp_colimit
    intro j
    let := hY j
    exact path_projection_rlp (p.app j)
  have hr : simplicialWeakEquivalences (colim.map (pathRight p)) := by
    apply KanQuillen.boundary_right_weak
    apply boundary_rlp_colimit
    intro j
    let := hX j
    let := hY j
    rw [← SSet.rlp_monomorphisms]
    exact right_rlp (p.app j) (GeometricRecognition.weak_kan_heq _ (hp j))
  have hl : simplicialWeakEquivalences (colim.map (pathLeft p)) := by
    apply simplicialWeakEquivalences.of_postcomp _ _ hproj
    rw [← CategoryTheory.Functor.map_comp,path_left_projection,CategoryTheory.Functor.map_id]
    exact simplicialWeakEquivalences.id_mem _
  simpa only [← CategoryTheory.Functor.map_comp,path_fac] using simplicialWeakEquivalences.comp_mem _ _ hl hr

theorem colimit_weak {J : Type u} [Category.{u} J] [IsFiltered J]
    {X Y : J ⥤ SSet.{u}} (p : X ⟶ Y)
    (hp : ∀ j, simplicialWeakEquivalences (p.app j)) :
    simplicialWeakEquivalences (colim.map p) := by
  let R := Subdivision.exInfinityFunctor.{u}
  have hr : simplicialWeakEquivalences (colim.map (CategoryTheory.Functor.whiskerRight p R)) :=
    kan_colimit_weak (CategoryTheory.Functor.whiskerRight p R)
      (fun j => Subdivision.exInfinity_kan (X.obj j))
      (fun j => Subdivision.exInfinity_kan (Y.obj j))
      (fun j => (Subdivision.exInfinity_map_weak_iff (p.app j)).mpr (hp j))
  apply (Subdivision.exInfinity_map_weak_iff (colim.map p)).mp
  apply simplicialWeakEquivalences.of_postcomp _ (preservesColimitIso R Y).hom
    (simplicialWeakEquivalences.of_isIso _)
  have hw : R.map (colim.map p) ≫ (preservesColimitIso R Y).hom =
      (preservesColimitIso R X).hom ≫ colim.map (CategoryTheory.Functor.whiskerRight p R) :=
    (preservesColimitNatIso R).hom.naturality p
  rw [hw]
  exact simplicialWeakEquivalences.comp_mem _ _ (simplicialWeakEquivalences.of_isIso _) hr

lemma weak_of_colimit {J : Type u} [Category.{u} J] [IsFiltered J]
    {X Y : J ⥤ SSet.{u}} (p : X ⟶ Y) (c : Cocone X) (d : Cocone Y)
    (hc : IsColimit c) (hd : IsColimit d) (f : c.pt ⟶ d.pt)
    (fac : ∀ j, c.ι.app j ≫ f = p.app j ≫ d.ι.app j)
    (hp : ∀ j, simplicialWeakEquivalences (p.app j)) :
    simplicialWeakEquivalences f := by
  let e₁ := hc.coconePointUniqueUpToIso (colimit.isColimit X)
  let e₂ := (colimit.isColimit Y).coconePointUniqueUpToIso hd
  have h₁ (j : J) : c.ι.app j ≫ e₁.hom = colimit.ι X j :=
    hc.comp_coconePointUniqueUpToIso_hom (colimit.isColimit X) j
  have h₂ (j : J) : colimit.ι Y j ≫ e₂.hom = d.ι.app j :=
    (colimit.isColimit Y).comp_coconePointUniqueUpToIso_hom hd j
  have he : f = e₁.hom ≫ colim.map p ≫ e₂.hom := by
    apply hc.hom_ext
    intro j
    rw [← Category.assoc,← Category.assoc,h₁,colimit.ι_map,Category.assoc,h₂]
    exact fac j
  rw [he]
  exact simplicialWeakEquivalences.comp_mem _ _ (simplicialWeakEquivalences.of_isIso _)
    (simplicialWeakEquivalences.comp_mem _ _ (colimit_weak p hp)
      (simplicialWeakEquivalences.of_isIso _))

end Thomason.FilteredWeak

end

end OAI
