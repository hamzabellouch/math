import Mathlib
import OAI.CategoryTheory.Thomason.SieveAttachments

namespace OAI

/-! Finite Attachments. -/

noncomputable section
universe u v w z
open CategoryTheory Limits Opposite Simplicial MonoidalCategory

namespace Thomason.Attachments
open CategoryTheory Limits OmegaCategory NormalizedChains.PosetTables

theorem cosieve_attachment_covers {P : Type u} [PartialOrder P]
    (A S₁ S₂ : Set P) (h₁ : IsUpperSet S₁) (h₂ : IsUpperSet S₂)
    (hA₁ : A ⊆ S₁) (hA₂ : Disjoint A S₂) (hcover : S₁ ∪ S₂ = Set.univ)
    {X Y : OmegaCategory.{u}} (a : categorification.obj (nerve A) ⟶ X)
    (h : X ⟶ Y) (i : categorification.obj (nerve P) ⟶ Y)
    (H : IsPushout a
      (categorification.map (nerveMap (OrderEmbedding.subtype A).toOrderHom.monotone.functor)) h i) :
    ∃ T₁ T₂ : Set Y.Objects,
      Y.IsObjectCosieve T₁ ∧ Y.IsObjectCosieve T₂ ∧ T₁ ∪ T₂ = Set.univ ∧
      IsPosetAttachmentPiece A S₁ hA₁ a h i T₁ ∧
      IsPosetNewPiece S₂ i T₂ ∧ IsPosetNewPiece (S₁ ∩ S₂) i (T₁ ∩ T₂) :=
by
  classical
  let l₁ := upperSegmentLabel S₁ h₁
  let l₂ := upperSegmentLabel S₂ h₂
  let l₃ : P →o Fin 2 := ⟨fun p => min (l₁ p) (l₂ p),
    fun _ _ he => min_le_min (l₁.monotone he) (l₂.monotone he)⟩
  have hl₁ : ∀ p : A, l₁ p.val = 1 := fun p => (upperSegmentLabel_one S₁ h₁ _).mpr (hA₁ p.property)
  have hl₂ : ∀ p : A, l₂ p.val = 0 := by
    intro p
    have hp : p.val ∉ S₂ := fun hp => Set.disjoint_left.mp hA₂ p.property hp
    change (if p.val ∈ S₂ then (1 : Fin 2) else 0) = 0
    simp [hp]
  have hl₃ : ∀ p : A, l₃ p.val = 0 := by intro p; change min (l₁ p.val) (l₂ p.val) = 0; rw [hl₁,hl₂]; rfl
  have hS₁ : S₁ = {p | l₁ p = 1} := by ext p; exact (upperSegmentLabel_one S₁ h₁ p).symm
  have hS₂ : S₂ = {p | l₂ p = 1} := by ext p; exact (upperSegmentLabel_one S₂ h₂ p).symm
  have hS₃ : S₁ ∩ S₂ = {p | l₃ p = 1} := by
    ext p
    change (p ∈ S₁ ∧ p ∈ S₂) ↔
      min (if p ∈ S₁ then (1 : Fin 2) else 0) (if p ∈ S₂ then 1 else 0) = 1
    by_cases hp₁ : p ∈ S₁ <;> by_cases hp₂ : p ∈ S₂ <;>
      simp [hp₁,hp₂]
  let η₁ := constantAttachmentLabel A l₁ 1 hl₁ a h i H
  let η₂ := constantAttachmentLabel A l₂ 0 hl₂ a h i H
  let η₃ := constantAttachmentLabel A l₃ 0 hl₃ a h i H
  have hη₃ : η₃ = minLabel η₁ η₂ := by
    apply H.hom_ext
    · change h ≫ constantAttachmentLabel A l₃ 0 hl₃ a h i H = _
      rw [constantAttachmentLabel_old,comp_minLabel,
        constantAttachmentLabel_old,constantAttachmentLabel_old]
      rfl
    · change i ≫ constantAttachmentLabel A l₃ 0 hl₃ a h i H = _
      rw [constantAttachmentLabel_new,comp_minLabel,
        constantAttachmentLabel_new,constantAttachmentLabel_new]
      rfl
  have hp₃ := constant_attachment_new_piece A l₃ 0 hl₃ a h i H
    (S₁ ∩ S₂) 1 (by decide) hS₃
  change IsPosetNewPiece (S₁ ∩ S₂) i (intervalFiberObjects η₃ 1) at hp₃
  rw [hη₃,minLabel_objects_fiber] at hp₃
  refine ⟨intervalFiberObjects η₁ 1,intervalFiberObjects η₂ 1,
    one_fiber_isObjectCosieve η₁,one_fiber_isObjectCosieve η₂,?_,
    constant_attachment_old_piece A l₁ 1 hl₁ a h i H S₁ hA₁ hS₁,
    constant_attachment_new_piece A l₂ 0 hl₂ a h i H S₂ 1 (by decide) hS₂,hp₃⟩
  refine labelled_objects_cover H η₁ η₂ l₁ l₂ 1
    (Or.inl (constantAttachmentLabel_old A l₁ 1 hl₁ a h i H))
    (constantAttachmentLabel_new A l₁ 1 hl₁ a h i H)
    (constantAttachmentLabel_new A l₂ 0 hl₂ a h i H) ?_
  intro p
  have hp : p ∈ S₁ ∪ S₂ := by rw [hcover]; trivial
  exact hp.imp ((upperSegmentLabel_one S₁ h₁ p).mpr) ((upperSegmentLabel_one S₂ h₂ p).mpr)

end Thomason.Attachments

end

noncomputable section
universe u v w z
open CategoryTheory Limits Opposite Simplicial MonoidalCategory

namespace Thomason.Attachments
open CategoryTheory Limits OmegaCategory

def fullFinite (n : ℕ) (C : NCategory.{u} n) (T : Set C.val.Objects) : NCategory.{u} n :=
  ⟨(C.val.fullOn T).category, fun x => Subtype.ext (C.property x.val)⟩

def fullFiniteInclusion (n : ℕ) (C : NCategory.{u} n) (T : Set C.val.Objects) :
    fullFinite n C T ⟶ C := (C.val.fullOn T).inclusion

def IsPosetFiniteAttachmentPiece (n : ℕ) {P : Type u} [PartialOrder P]
    (A S : Set P) (hAS : A ⊆ S) {X Y : NCategory.{u} n}
    (a : (categorificationFinite n).obj (nerve A) ⟶ X) (h : X ⟶ Y)
    (i : (categorificationFinite n).obj (nerve P) ⟶ Y) (T : Set Y.val.Objects) : Prop :=
  ∃ (j : X ⟶ fullFinite n Y T)
    (k : (categorificationFinite n).obj (nerve S) ⟶ fullFinite n Y T),
    j ≫ fullFiniteInclusion n Y T = h ∧
    k ≫ fullFiniteInclusion n Y T = (categorificationFinite n).map
      (nerveMap (OrderEmbedding.subtype S).toOrderHom.monotone.functor) ≫ i ∧
    IsPushout a ((categorificationFinite n).map (nerveMap (subposetMap A S hAS).monotone.functor)) j k

def IsPosetFiniteNewPiece (n : ℕ) {P : Type u} [PartialOrder P]
    (S : Set P) {Y : NCategory.{u} n}
    (i : (categorificationFinite n).obj (nerve P) ⟶ Y) (T : Set Y.val.Objects) : Prop :=
  ∃ e : (categorificationFinite n).obj (nerve S) ≅ fullFinite n Y T,
    e.hom ≫ fullFiniteInclusion n Y T = (categorificationFinite n).map
      (nerveMap (OrderEmbedding.subtype S).toOrderHom.monotone.functor) ≫ i

end Thomason.Attachments

end

noncomputable section
universe u v w z
open CategoryTheory Limits Opposite Simplicial MonoidalCategory

namespace Thomason.Attachments
open CategoryTheory Limits OmegaCategory NormalizedChains.PosetTables

lemma posetFiniteLabel_constant (n : ℕ) (hn : 1 ≤ n)
    {P : Type u} [PartialOrder P] (l : P →o Fin 2)
    (e : Fin 2) (hl : ∀ p, l p = e) :
    posetCategorificationFiniteLabel n hn l =
      constantLabel ((categorificationFinite n).obj (nerve P)).val e := by
  apply truncation_functor_ext
  exact posetLabel_constant l e hl

lemma posetFiniteLabel_natural (n : ℕ) (hn : 1 ≤ n)
    {P Q : Type u} [PartialOrder P] [PartialOrder Q] (g : Q →o P) (l : P →o Fin 2) :
    (categorificationFinite n).map (nerveMap g.monotone.functor) ≫
      posetCategorificationFiniteLabel n hn l = posetCategorificationFiniteLabel n hn (l.comp g) := by
  apply truncation_functor_ext
  exact posetCategorificationLabel_natural g l

lemma posetFiniteLabel_max (n : ℕ) (hn : 1 ≤ n)
    {P : Type u} [PartialOrder P] (l₁ l₂ : P →o Fin 2) :
    posetCategorificationFiniteLabel n hn
      (⟨fun p => max (l₁ p) (l₂ p),fun _ _ he => max_le_max (l₁.monotone he) (l₂.monotone he)⟩ : P →o Fin 2) =
      maxLabel (posetCategorificationFiniteLabel n hn l₁) (posetCategorificationFiniteLabel n hn l₂) := by
  apply truncation_functor_ext
  rfl

lemma posetFiniteLabel_min (n : ℕ) (hn : 1 ≤ n)
    {P : Type u} [PartialOrder P] (l₁ l₂ : P →o Fin 2) :
    posetCategorificationFiniteLabel n hn
      (⟨fun p => min (l₁ p) (l₂ p),fun _ _ he => min_le_min (l₁.monotone he) (l₂.monotone he)⟩ : P →o Fin 2) =
      minLabel (posetCategorificationFiniteLabel n hn l₁) (posetCategorificationFiniteLabel n hn l₂) := by
  apply truncation_functor_ext
  rfl

def constantFiniteLabel (n : ℕ) (hn : 1 ≤ n) (C : NCategory.{u} n) (e : Fin 2) :
    C ⟶ finiteInterval n hn := constantLabel C.val e

lemma comp_constantFiniteLabel (n : ℕ) (hn : 1 ≤ n) {C D : NCategory.{u} n}
    (f : C ⟶ D) (e : Fin 2) :
    f ≫ constantFiniteLabel n hn D e = constantFiniteLabel n hn C e := by
  exact comp_constantLabel f e

variable (n : ℕ) (hn : 1 ≤ n) {P : Type u} [PartialOrder P] (A : Set P)
    (l : P →o Fin 2) (b : Fin 2) (hlA : ∀ p : A, l p.val = b)
    {X Y : NCategory.{u} n} (a : (categorificationFinite n).obj (nerve A) ⟶ X)
    (h : X ⟶ Y) (i : (categorificationFinite n).obj (nerve P) ⟶ Y)
    (H : IsPushout a
      ((categorificationFinite n).map (nerveMap (OrderEmbedding.subtype A).toOrderHom.monotone.functor)) h i)

def constantFiniteAttachmentLabel : Y ⟶ finiteInterval n hn :=
  H.desc (constantFiniteLabel n hn X b) (posetCategorificationFiniteLabel n hn l) (by
    rw [comp_constantFiniteLabel]
    exact ((posetFiniteLabel_natural n hn _ l).trans (posetFiniteLabel_constant n hn _ b hlA)).symm)

lemma constantFiniteAttachmentLabel_old :
    h ≫ constantFiniteAttachmentLabel n hn A l b hlA a h i H = constantFiniteLabel n hn X b := H.inl_desc _ _ _
lemma constantFiniteAttachmentLabel_new :
    i ≫ constantFiniteAttachmentLabel n hn A l b hlA a h i H = posetCategorificationFiniteLabel n hn l := H.inr_desc _ _ _

lemma subposetFiniteMap_comp (S : Set P) (hAS : A ⊆ S) :
    (categorificationFinite n).map (nerveMap (subposetMap A S hAS).monotone.functor) ≫
      (categorificationFinite n).map (nerveMap (OrderEmbedding.subtype S).toOrderHom.monotone.functor) =
    (categorificationFinite n).map (nerveMap (OrderEmbedding.subtype A).toOrderHom.monotone.functor) := by
  rw [← (categorificationFinite n).map_comp]
  rfl

lemma fiberFiniteInclusion_mono (e : Fin 2) (Q : Over (finiteInterval.{u} n hn)) :
    Mono (fiberFiniteInclusion n hn e Q) := by
  constructor
  intro Z f g he
  apply OmegaCategory.Functor.ext
  funext x
  apply Subtype.ext
  exact congrArg (fun F => F.map x) he

def intervalFiberFullFiniteIso {C : NCategory.{u} n} (η : C ⟶ finiteInterval n hn) (e : Fin 2) :
    (fiberFiniteFunctor n hn e).obj (Over.mk η) ≅ fullFinite n C (intervalFiberObjects η e) where
  hom := (intervalFiberFullIso η e).hom
  inv := (intervalFiberFullIso η e).inv
  hom_inv_id := (intervalFiberFullIso η e).hom_inv_id
  inv_hom_id := (intervalFiberFullIso η e).inv_hom_id

lemma constant_finite_attachment_old_piece (S : Set P) (hAS : A ⊆ S)
    (hS : S = {p | l p = b}) :
    IsPosetFiniteAttachmentPiece n A S hAS a h i
      (intervalFiberObjects (constantFiniteAttachmentLabel n hn A l b hlA a h i H) b) := by
  let η := constantFiniteAttachmentLabel n hn A l b hlA a h i H
  let q := posetCategorificationFiniteLabel n hn l
  let C := (categorificationFinite n).obj (nerve A)
  let g : C ⟶ (categorificationFinite n).obj (nerve P) :=
    (categorificationFinite n).map (nerveMap (OrderEmbedding.subtype A).toOrderHom.monotone.functor)
  let src : Over (finiteInterval n hn) := Over.mk (constantFiniteLabel n hn C b)
  let old : Over (finiteInterval n hn) := Over.mk (constantFiniteLabel n hn X b)
  let af : src ⟶ old := Over.homMk a (comp_constantLabel a b)
  let gf : src ⟶ Over.mk q := Over.homMk g (by
    exact (posetFiniteLabel_natural n hn _ l).trans (posetFiniteLabel_constant n hn _ b hlA))
  let hf : old ⟶ Over.mk η := Over.homMk h (constantFiniteAttachmentLabel_old n hn A l b hlA a h i H)
  let if' : Over.mk q ⟶ Over.mk η := Over.homMk i (constantFiniteAttachmentLabel_new n hn A l b hlA a h i H)
  let F := fiberFiniteFunctor n hn b
  let E := posetPieceFiniteFiberIso n hn S l b hS
  let j := (constantFiniteFiberIso n hn X b).hom ≫ F.map hf
  let k := E.hom ≫ F.map if'
  have := fiberFiniteInclusion_mono n hn b (Over.mk q)
  have hE := posetPieceFiniteFiberIso_inclusion n hn S l b hS
  have hp : IsPushout a
      ((categorificationFinite n).map (nerveMap (subposetMap A S hAS).monotone.functor)) j k := by
    refine (labelled_pushout_finite_fibers n hn af gf hf if' H b).of_iso'
      (constantFiniteFiberIso n hn C b) (constantFiniteFiberIso n hn X b) E (Iso.refl _) ?_ ?_ ?_ ?_
    · rfl
    · apply (cancel_mono (C := NCategory.{u} n) (fiberFiniteInclusion n hn b (Over.mk q))).mp
      change g = (categorificationFinite n).map (nerveMap (subposetMap A S hAS).monotone.functor) ≫
        (E.hom ≫ fiberFiniteInclusion n hn b (Over.mk q))
      rw [hE]
      exact (subposetFiniteMap_comp n A S hAS).symm
    · simp only [Iso.refl_hom, Category.comp_id]; rfl
    · simp only [Iso.refl_hom, Category.comp_id]; rfl
  let Efull := intervalFiberFullFiniteIso n hn η b
  refine ⟨j ≫ Efull.hom,k ≫ Efull.hom,?_,?_,?_⟩
  · rfl
  · change k ≫ fiberFiniteInclusion n hn b (Over.mk η) = _
    change E.hom ≫ (F.map if' ≫ fiberFiniteInclusion n hn b (Over.mk η)) = _
    change E.hom ≫ (fiberFiniteInclusion n hn b (Over.mk q) ≫ i) = _
    rw [← Category.assoc, hE]
  · exact hp.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) Efull
      (by simp) (by simp) (by simp) (by simp)

lemma constant_finite_attachment_new_piece (S : Set P) (e : Fin 2) (hbe : b ≠ e)
    (hS : S = {p | l p = e}) :
    IsPosetFiniteNewPiece n S i (intervalFiberObjects (constantFiniteAttachmentLabel n hn A l b hlA a h i H) e) := by
  let η := constantFiniteAttachmentLabel n hn A l b hlA a h i H
  let q := posetCategorificationFiniteLabel n hn l
  let C := (categorificationFinite n).obj (nerve A)
  let g : C ⟶ (categorificationFinite n).obj (nerve P) :=
    (categorificationFinite n).map (nerveMap (OrderEmbedding.subtype A).toOrderHom.monotone.functor)
  let src : Over (finiteInterval n hn) := Over.mk (constantFiniteLabel n hn C b)
  let old : Over (finiteInterval n hn) := Over.mk (constantFiniteLabel n hn X b)
  let af : src ⟶ old := Over.homMk a (comp_constantLabel a b)
  let gf : src ⟶ Over.mk q := Over.homMk g (by
    exact (posetFiniteLabel_natural n hn _ l).trans (posetFiniteLabel_constant n hn _ b hlA))
  let hf : old ⟶ Over.mk η := Over.homMk h (constantFiniteAttachmentLabel_old n hn A l b hlA a h i H)
  let if' : Over.mk q ⟶ Over.mk η := Over.homMk i (constantFiniteAttachmentLabel_new n hn A l b hlA a h i H)
  let F := fiberFiniteFunctor n hn e
  have : IsEmpty (F.obj src).val.Cell := ⟨fun x =>
    hbe (congrArg (fun c => c.left.down) x.property)⟩
  have : IsEmpty (F.obj old).val.Cell := ⟨fun x =>
    hbe (congrArg (fun c => c.left.down) x.property)⟩
  let J := isoOfBijective ((nCategoryInclusion n).map (F.map af)) (by
    constructor
    · intro x; change (F.obj src).val.Cell at x; exact isEmptyElim x
    · intro x; change (F.obj old).val.Cell at x; exact isEmptyElim x)
  let Jf : F.obj src ≅ F.obj old := {
    hom := J.hom, inv := J.inv, hom_inv_id := J.hom_inv_id, inv_hom_id := J.inv_hom_id }
  have : IsIso (F.map af) := Jf.isIso_hom
  have hp := labelled_pushout_finite_fibers n hn af gf hf if' H e
  have : IsIso (F.map if') := hp.isIso_inr_of_isIso
  let E := posetPieceFiniteFiberIso n hn S l e hS
  let fiberIso := asIso (F.map if')
  refine ⟨E ≪≫ fiberIso ≪≫ intervalFiberFullFiniteIso n hn η e, ?_⟩
  change E.hom ≫ (F.map if' ≫ fiberFiniteInclusion n hn e (Over.mk η)) = _
  change E.hom ≫ (fiberFiniteInclusion n hn e (Over.mk q) ≫ i) = _
  rw [← Category.assoc, posetPieceFiniteFiberIso_inclusion n hn]

end Thomason.Attachments

end

noncomputable section
universe u v w z
open CategoryTheory Limits Opposite Simplicial MonoidalCategory

namespace Thomason.Attachments
open CategoryTheory Limits OmegaCategory NormalizedChains.PosetTables

def finitePosetObject (n : ℕ) {P : Type u} [PartialOrder P]
    (x : ((categorificationFinite n).obj (nerve P)).val.Objects) : P :=
  NormalizedChains.tableObjectsEquiv ((posetCategorificationTableMap P).objects
    (truncationCellLift (categorification.obj (nerve P)) n 0 x))

lemma posetFiniteLabel_objects (n : ℕ) (hn : 1 ≤ n)
    {P : Type u} [PartialOrder P] (l : P →o Fin 2)
    (x : ((categorificationFinite n).obj (nerve P)).val.Objects) :
    (posetCategorificationFiniteLabel n hn l).objects x = intervalVertex (l (finitePosetObject n x)) := by
  conv_lhs => rw [← truncationCellLift_unit (categorification.obj (nerve P)) n 0 x]
  exact posetLabel_objects l (truncationCellLift (categorification.obj (nerve P)) n 0 x)

lemma labelled_finite_objects_cover (n : ℕ) (hn : 1 ≤ n)
    {P : Type u} [PartialOrder P] {A : Set P}
    {X Y : NCategory.{u} n} {a : (categorificationFinite n).obj (nerve A) ⟶ X}
    {h : X ⟶ Y} {i : (categorificationFinite n).obj (nerve P) ⟶ Y}
    (H : IsPushout a
      ((categorificationFinite n).map (nerveMap (OrderEmbedding.subtype A).toOrderHom.monotone.functor)) h i)
    (η₁ η₂ : Y ⟶ finiteInterval n hn) (l₁ l₂ : P →o Fin 2) (e : Fin 2)
    (hh : h ≫ η₁ = constantFiniteLabel n hn X e ∨ h ≫ η₂ = constantFiniteLabel n hn X e)
    (hi₁ : i ≫ η₁ = posetCategorificationFiniteLabel n hn l₁)
    (hi₂ : i ≫ η₂ = posetCategorificationFiniteLabel n hn l₂)
    (hl : ∀ p, l₁ p = e ∨ l₂ p = e) :
    intervalFiberObjects η₁ e ∪ intervalFiberObjects η₂ e = Set.univ := by
  apply Set.eq_univ_of_forall
  intro y
  rcases Types.eq_or_eq_of_isPushout (pushout_finite_objects n hn _ _ _ _ H) y with ⟨x,rfl⟩ | ⟨x,rfl⟩
  · rcases hh with hh | hh
    · exact Or.inl (interval_vertex_mem_old h η₁ e hh x)
    · exact Or.inr (interval_vertex_mem_old h η₂ e hh x)
  · rcases hl (finitePosetObject n x) with hx | hx
    · apply Or.inl
      change η₁.objects (i.objects x) = intervalVertex e
      exact (congrArg (fun f : (categorificationFinite n).obj (nerve P) ⟶ finiteInterval n hn => f.objects x) hi₁).trans
        ((posetFiniteLabel_objects n hn l₁ x).trans (congrArg intervalVertex hx))
    · apply Or.inr
      change η₂.objects (i.objects x) = intervalVertex e
      exact (congrArg (fun f : (categorificationFinite n).obj (nerve P) ⟶ finiteInterval n hn => f.objects x) hi₂).trans
        ((posetFiniteLabel_objects n hn l₂ x).trans (congrArg intervalVertex hx))

end Thomason.Attachments

end

noncomputable section
universe u v w z
open CategoryTheory Limits Opposite Simplicial MonoidalCategory

namespace Thomason.Attachments
open CategoryTheory Limits OmegaCategory NormalizedChains.PosetTables
def maxFiniteLabel (n : ℕ) (hn : 1 ≤ n) {C : NCategory.{u} n}
    (p q : C ⟶ finiteInterval n hn) : C ⟶ finiteInterval n hn := maxLabel p q

def minFiniteLabel (n : ℕ) (hn : 1 ≤ n) {C : NCategory.{u} n}
    (p q : C ⟶ finiteInterval n hn) : C ⟶ finiteInterval n hn := minLabel p q

lemma comp_maxFiniteLabel (n : ℕ) (hn : 1 ≤ n) {C D : NCategory.{u} n}
    (f : C ⟶ D) (p q : D ⟶ finiteInterval n hn) :
    f ≫ maxFiniteLabel n hn p q = maxFiniteLabel n hn (f ≫ p) (f ≫ q) := rfl

lemma comp_minFiniteLabel (n : ℕ) (hn : 1 ≤ n) {C D : NCategory.{u} n}
    (f : C ⟶ D) (p q : D ⟶ finiteInterval n hn) :
    f ≫ minFiniteLabel n hn p q = minFiniteLabel n hn (f ≫ p) (f ≫ q) := rfl

lemma maxFiniteLabel_objects_fiber (n : ℕ) (hn : 1 ≤ n) {C : NCategory.{u} n}
    (p q : C ⟶ finiteInterval n hn) :
    intervalFiberObjects (maxFiniteLabel n hn p q) 0 = intervalFiberObjects p 0 ∩ intervalFiberObjects q 0 :=
  maxLabel_objects_fiber p q

lemma minFiniteLabel_objects_fiber (n : ℕ) (hn : 1 ≤ n) {C : NCategory.{u} n}
    (p q : C ⟶ finiteInterval n hn) :
    intervalFiberObjects (minFiniteLabel n hn p q) 1 = intervalFiberObjects p 1 ∩ intervalFiberObjects q 1 :=
  minLabel_objects_fiber p q

theorem sieve_finite_attachment_covers (n : ℕ) (hn : 1 ≤ n) {P : Type u} [PartialOrder P]
    (A S₁ S₂ : Set P) (h₁ : IsLowerSet S₁) (h₂ : IsLowerSet S₂)
    (hA₁ : A ⊆ S₁) (hA₂ : A ⊆ S₂) (hcover : S₁ ∪ S₂ = Set.univ)
    {X Y : NCategory.{u} n} (a : (categorificationFinite n).obj (nerve A) ⟶ X)
    (h : X ⟶ Y) (i : (categorificationFinite n).obj (nerve P) ⟶ Y)
    (H : IsPushout a
      ((categorificationFinite n).map (nerveMap (OrderEmbedding.subtype A).toOrderHom.monotone.functor)) h i) :
    ∃ T₁ T₂ : Set Y.val.Objects,
      Y.val.IsObjectSieve T₁ ∧ Y.val.IsObjectSieve T₂ ∧ T₁ ∪ T₂ = Set.univ ∧
      IsPosetFiniteAttachmentPiece n A S₁ hA₁ a h i T₁ ∧
      IsPosetFiniteAttachmentPiece n A S₂ hA₂ a h i T₂ ∧
      IsPosetFiniteAttachmentPiece n A (S₁ ∩ S₂) (fun _ hx => ⟨hA₁ hx,hA₂ hx⟩)
        a h i (T₁ ∩ T₂) :=
by
  classical
  let l₁ := lowerSegmentLabel S₁ h₁
  let l₂ := lowerSegmentLabel S₂ h₂
  let l₃ : P →o Fin 2 := ⟨fun p => max (l₁ p) (l₂ p),
    fun _ _ he => max_le_max (l₁.monotone he) (l₂.monotone he)⟩
  have hl₁ : ∀ p : A, l₁ p.val = 0 := fun p => (lowerSegmentLabel_zero S₁ h₁ _).mpr (hA₁ p.property)
  have hl₂ : ∀ p : A, l₂ p.val = 0 := fun p => (lowerSegmentLabel_zero S₂ h₂ _).mpr (hA₂ p.property)
  have hl₃ : ∀ p : A, l₃ p.val = 0 := by intro p; change max (l₁ p.val) (l₂ p.val) = 0; rw [hl₁,hl₂]; rfl
  have hS₁ : S₁ = {p | l₁ p = 0} := by ext p; exact (lowerSegmentLabel_zero S₁ h₁ p).symm
  have hS₂ : S₂ = {p | l₂ p = 0} := by ext p; exact (lowerSegmentLabel_zero S₂ h₂ p).symm
  have hS₃ : S₁ ∩ S₂ = {p | l₃ p = 0} := by
    ext p
    change (p ∈ S₁ ∧ p ∈ S₂) ↔
      max (if p ∈ S₁ then (0 : Fin 2) else 1) (if p ∈ S₂ then 0 else 1) = 0
    by_cases hp₁ : p ∈ S₁ <;> by_cases hp₂ : p ∈ S₂ <;>
      simp [hp₁,hp₂]
  let η₁ := constantFiniteAttachmentLabel n hn A l₁ 0 hl₁ a h i H
  let η₂ := constantFiniteAttachmentLabel n hn A l₂ 0 hl₂ a h i H
  let η₃ := constantFiniteAttachmentLabel n hn A l₃ 0 hl₃ a h i H
  have hη₃ : η₃ = maxFiniteLabel n hn η₁ η₂ := by
    apply H.hom_ext
    · change h ≫ constantFiniteAttachmentLabel n hn A l₃ 0 hl₃ a h i H = _
      rw [constantFiniteAttachmentLabel_old n hn,comp_maxFiniteLabel,
        constantFiniteAttachmentLabel_old n hn,constantFiniteAttachmentLabel_old n hn]
      rfl
    · change i ≫ constantFiniteAttachmentLabel n hn A l₃ 0 hl₃ a h i H = _
      rw [constantFiniteAttachmentLabel_new n hn,comp_maxFiniteLabel,
        constantFiniteAttachmentLabel_new n hn,constantFiniteAttachmentLabel_new n hn]
      exact posetFiniteLabel_max n hn l₁ l₂
  have hp₃ := constant_finite_attachment_old_piece n hn A l₃ 0 hl₃ a h i H
    (S₁ ∩ S₂) (fun _ hx => ⟨hA₁ hx,hA₂ hx⟩) hS₃
  change IsPosetFiniteAttachmentPiece n A (S₁ ∩ S₂) _ a h i (intervalFiberObjects η₃ 0) at hp₃
  rw [hη₃,maxFiniteLabel_objects_fiber] at hp₃
  refine ⟨intervalFiberObjects η₁ 0,intervalFiberObjects η₂ 0,
    zero_fiber_isObjectSieve η₁,zero_fiber_isObjectSieve η₂,?_,
    constant_finite_attachment_old_piece n hn A l₁ 0 hl₁ a h i H S₁ hA₁ hS₁,
    constant_finite_attachment_old_piece n hn A l₂ 0 hl₂ a h i H S₂ hA₂ hS₂,hp₃⟩
  refine labelled_finite_objects_cover n hn H η₁ η₂ l₁ l₂ 0
    (Or.inl (constantFiniteAttachmentLabel_old n hn A l₁ 0 hl₁ a h i H))
    (constantFiniteAttachmentLabel_new n hn A l₁ 0 hl₁ a h i H)
    (constantFiniteAttachmentLabel_new n hn A l₂ 0 hl₂ a h i H) ?_
  intro p
  have hp : p ∈ S₁ ∪ S₂ := by rw [hcover]; trivial
  exact hp.imp ((lowerSegmentLabel_zero S₁ h₁ p).mpr) ((lowerSegmentLabel_zero S₂ h₂ p).mpr)

end Thomason.Attachments

end

noncomputable section
universe u v w z
open CategoryTheory Limits Opposite Simplicial MonoidalCategory

namespace Thomason.Attachments
open CategoryTheory Limits OmegaCategory NormalizedChains.PosetTables

theorem cosieve_finite_attachment_covers (n : ℕ) (hn : 1 ≤ n) {P : Type u} [PartialOrder P]
    (A S₁ S₂ : Set P) (h₁ : IsUpperSet S₁) (h₂ : IsUpperSet S₂)
    (hA₁ : A ⊆ S₁) (hA₂ : Disjoint A S₂) (hcover : S₁ ∪ S₂ = Set.univ)
    {X Y : NCategory.{u} n} (a : (categorificationFinite n).obj (nerve A) ⟶ X)
    (h : X ⟶ Y) (i : (categorificationFinite n).obj (nerve P) ⟶ Y)
    (H : IsPushout a
      ((categorificationFinite n).map (nerveMap (OrderEmbedding.subtype A).toOrderHom.monotone.functor)) h i) :
    ∃ T₁ T₂ : Set Y.val.Objects,
      Y.val.IsObjectCosieve T₁ ∧ Y.val.IsObjectCosieve T₂ ∧ T₁ ∪ T₂ = Set.univ ∧
      IsPosetFiniteAttachmentPiece n A S₁ hA₁ a h i T₁ ∧
      IsPosetFiniteNewPiece n S₂ i T₂ ∧ IsPosetFiniteNewPiece n (S₁ ∩ S₂) i (T₁ ∩ T₂) :=
by
  classical
  let l₁ := upperSegmentLabel S₁ h₁
  let l₂ := upperSegmentLabel S₂ h₂
  let l₃ : P →o Fin 2 := ⟨fun p => min (l₁ p) (l₂ p),
    fun _ _ he => min_le_min (l₁.monotone he) (l₂.monotone he)⟩
  have hl₁ : ∀ p : A, l₁ p.val = 1 := fun p => (upperSegmentLabel_one S₁ h₁ _).mpr (hA₁ p.property)
  have hl₂ : ∀ p : A, l₂ p.val = 0 := by
    intro p
    have hp : p.val ∉ S₂ := fun hp => Set.disjoint_left.mp hA₂ p.property hp
    change (if p.val ∈ S₂ then (1 : Fin 2) else 0) = 0
    simp [hp]
  have hl₃ : ∀ p : A, l₃ p.val = 0 := by intro p; change min (l₁ p.val) (l₂ p.val) = 0; rw [hl₁,hl₂]; rfl
  have hS₁ : S₁ = {p | l₁ p = 1} := by ext p; exact (upperSegmentLabel_one S₁ h₁ p).symm
  have hS₂ : S₂ = {p | l₂ p = 1} := by ext p; exact (upperSegmentLabel_one S₂ h₂ p).symm
  have hS₃ : S₁ ∩ S₂ = {p | l₃ p = 1} := by
    ext p
    change (p ∈ S₁ ∧ p ∈ S₂) ↔
      min (if p ∈ S₁ then (1 : Fin 2) else 0) (if p ∈ S₂ then 1 else 0) = 1
    by_cases hp₁ : p ∈ S₁ <;> by_cases hp₂ : p ∈ S₂ <;>
      simp [hp₁,hp₂]
  let η₁ := constantFiniteAttachmentLabel n hn A l₁ 1 hl₁ a h i H
  let η₂ := constantFiniteAttachmentLabel n hn A l₂ 0 hl₂ a h i H
  let η₃ := constantFiniteAttachmentLabel n hn A l₃ 0 hl₃ a h i H
  have hη₃ : η₃ = minFiniteLabel n hn η₁ η₂ := by
    apply H.hom_ext
    · change h ≫ constantFiniteAttachmentLabel n hn A l₃ 0 hl₃ a h i H = _
      rw [constantFiniteAttachmentLabel_old n hn,comp_minFiniteLabel,
        constantFiniteAttachmentLabel_old n hn,constantFiniteAttachmentLabel_old n hn]
      rfl
    · change i ≫ constantFiniteAttachmentLabel n hn A l₃ 0 hl₃ a h i H = _
      rw [constantFiniteAttachmentLabel_new n hn,comp_minFiniteLabel,
        constantFiniteAttachmentLabel_new n hn,constantFiniteAttachmentLabel_new n hn]
      exact posetFiniteLabel_min n hn l₁ l₂
  have hp₃ := constant_finite_attachment_new_piece n hn A l₃ 0 hl₃ a h i H
    (S₁ ∩ S₂) 1 (by decide) hS₃
  change IsPosetFiniteNewPiece n (S₁ ∩ S₂) i (intervalFiberObjects η₃ 1) at hp₃
  rw [hη₃,minFiniteLabel_objects_fiber] at hp₃
  refine ⟨intervalFiberObjects η₁ 1,intervalFiberObjects η₂ 1,
    one_fiber_isObjectCosieve η₁,one_fiber_isObjectCosieve η₂,?_,
    constant_finite_attachment_old_piece n hn A l₁ 1 hl₁ a h i H S₁ hA₁ hS₁,
    constant_finite_attachment_new_piece n hn A l₂ 0 hl₂ a h i H S₂ 1 (by decide) hS₂,hp₃⟩
  refine labelled_finite_objects_cover n hn H η₁ η₂ l₁ l₂ 1
    (Or.inl (constantFiniteAttachmentLabel_old n hn A l₁ 1 hl₁ a h i H))
    (constantFiniteAttachmentLabel_new n hn A l₁ 1 hl₁ a h i H)
    (constantFiniteAttachmentLabel_new n hn A l₂ 0 hl₂ a h i H) ?_
  intro p
  have hp : p ∈ S₁ ∪ S₂ := by rw [hcover]; trivial
  exact hp.imp ((upperSegmentLabel_one S₁ h₁ p).mpr) ((upperSegmentLabel_one S₂ h₂ p).mpr)

end Thomason.Attachments

end

end OAI
