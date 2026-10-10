import Mathlib
import OAI.CategoryTheory.Thomason.Couniversality

namespace OAI

/-! Attachment Comparison. -/

noncomputable section
universe u v w z


namespace Thomason.FilteredPosets
open CategoryTheory Limits Opposite

def nerveIsColimit {J : Type u} [Category.{u} J] [IsFiltered J]
    {D : J ⥤ PartOrd.{u}} (c : Cocone D)
    (hrel : ∀ j (x y : D.obj j), c.ι.app j x ≤ c.ι.app j y → x ≤ y)
    (hcover : ∀ t : Finset c.pt, ∃ j, ∀ x ∈ t, ∃ y : D.obj j, c.ι.app j y = x) :
    IsColimit (PartOrd.nerveFunctor.mapCocone c) := by
  classical
  apply evaluationJointlyReflectsColimits
  intro m
  apply Types.FilteredColimit.isColimitOf'
  · intro x
    change (nerve c.pt).obj m at x
    let t : Finset c.pt := Finset.univ.image x.obj
    obtain ⟨j,hj⟩ := hcover t
    have hx (i : Fin (m.unop.len+1)) : ∃ y : D.obj j, c.ι.app j y = x.obj i :=
      hj _ (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)
    let y : Fin (m.unop.len+1) →o D.obj j := {
      toFun i := (hx i).choose
      monotone' := by
        intro a b hab
        apply hrel j
        rw [(hx a).choose_spec,(hx b).choose_spec]
        exact leOfHom (x.map (homOfLE hab)) }
    refine ⟨j,y.toFunctor,?_⟩
    apply nerve.ext_of_isThin
    funext i
    exact (hx i).choose_spec.symm
  · intro j x y h
    refine ⟨j,𝟙 j,?_⟩
    rw [CategoryTheory.Functor.map_id]
    change x = y
    apply nerve.ext_of_isThin
    funext i
    have he := congrArg (fun z : (nerve c.pt).obj m => z.obj i) h
    exact le_antisymm (hrel j _ _ he.le) (hrel j _ _ he.ge)

def diagram {J E : Type u} [Preorder J] [PartialOrder E]
    (S : J →o Set E) : J ⥤ PartOrd.{u} where
  obj j := PartOrd.of (S j)
  map f := PartOrd.ofHom ⟨fun x => ⟨x.val,S.monotone (leOfHom f) x.property⟩,
    fun _ _ h => h⟩
  map_id _ := rfl
  map_comp _ _ := rfl

def cocone {J E : Type u} [Preorder J] [PartialOrder E]
    (S : J →o Set E) : Cocone (diagram S) where
  pt := PartOrd.of E
  ι := {
    app j := PartOrd.ofHom (OrderEmbedding.subtype (S j)).toOrderHom
    naturality _ _ _ := rfl }

def unionIsColimit {J E : Type u} [Preorder J] [IsFiltered J] [PartialOrder E]
    (S : J →o Set E) (hcover : ∀ t : Finset E, ∃ j, (↑t : Set E) ⊆ S j) :
    IsColimit (PartOrd.nerveFunctor.mapCocone (cocone S)) := by
  apply nerveIsColimit
  · intro j x y h
    exact h
  · intro t
    obtain ⟨j,hj⟩ := hcover t
    exact ⟨j,fun x hx => ⟨⟨x,hj hx⟩,rfl⟩⟩

def oldDiagram {J E : Type u} [Preorder J] [PartialOrder E]
    (S : J →o Set E) (A : Set E) : J ⥤ PartOrd.{u} where
  obj j := PartOrd.of {s : S j | s.val ∈ A}
  map f := PartOrd.ofHom ⟨fun x =>
      ⟨⟨x.val.val,S.monotone (leOfHom f) x.val.property⟩,x.property⟩,
    fun _ _ h => h⟩
  map_id _ := rfl
  map_comp _ _ := rfl

def oldCocone {J E : Type u} [Preorder J] [PartialOrder E]
    (S : J →o Set E) (A : Set E) : Cocone (oldDiagram S A) where
  pt := PartOrd.of A
  ι := {
    app _ := PartOrd.ofHom ⟨fun x => ⟨x.val.val,x.property⟩,fun _ _ h => h⟩
    naturality _ _ _ := rfl }

def inclusion {J E : Type u} [Preorder J] [PartialOrder E]
    (S : J →o Set E) (A : Set E) : oldDiagram S A ⟶ diagram S where
  app j := PartOrd.ofHom (OrderEmbedding.subtype {s : S j | s.val ∈ A}).toOrderHom
  naturality _ _ _ := rfl

def oldUnionIsColimit {J E : Type u} [Preorder J] [IsFiltered J] [PartialOrder E]
    (S : J →o Set E) (hcover : ∀ t : Finset E, ∃ j, (↑t : Set E) ⊆ S j)
    (A : Set E) : IsColimit (PartOrd.nerveFunctor.mapCocone (oldCocone S A)) := by
  classical
  apply nerveIsColimit
  · intro j x y h
    exact h
  · intro t
    obtain ⟨j,hj⟩ := hcover (t.image Subtype.val)
    refine ⟨j,fun x hx => ?_⟩
    exact ⟨⟨⟨x.val,hj (Finset.mem_image.mpr ⟨x,hx,rfl⟩)⟩,x.property⟩,rfl⟩

def close {E : Type u} (q : E → E) (s : Finset E) : Finset E := by
  classical
  exact s ∪ s.image q

lemma mem_close {E : Type u} (q : E → E) (s : Finset E) (x : E) :
    x ∈ close q s ↔ x ∈ s ∨ ∃ y ∈ s, q y = x := by
  classical
  simp [close]

lemma close_contains {E : Type u} (q : E → E) (s : Finset E) : s ⊆ close q s := by
  intro x hx
  exact (mem_close q s x).mpr (Or.inl hx)

lemma close_stable {E : Type u} (q : E → E) (hq : ∀ x, q (q x) = q x)
    (s : Finset E) {x : E} (hx : x ∈ close q s) : q x ∈ close q s := by
  apply (mem_close q s (q x)).mpr
  right
  rcases (mem_close q s x).mp hx with hx | ⟨y,hy,h⟩
  · exact ⟨x,hx,rfl⟩
  · exact ⟨y,hy,by rw [← h,hq y]⟩

def closedFamily {E : Type u} (q : E → E) : Finset E →o Set E where
  toFun s := ↑(close q s)
  monotone' := by
    intro s t h x hx
    apply (mem_close q t x).mpr
    rcases (mem_close q s x).mp hx with hx | ⟨y,hy,he⟩
    · exact Or.inl (h hx)
    · exact Or.inr ⟨y,h hy,he⟩

instance closedFamily_finite {E : Type u} (q : E → E) (s : Finset E) :
    Finite (closedFamily q s) := (close q s).finite_toSet.to_subtype

lemma closedFamily_cover {E : Type u} (q : E → E) :
    ∀ t : Finset E, ∃ s, (↑t : Set E) ⊆ closedFamily q s :=
  fun t => ⟨t,close_contains q t⟩

end Thomason.FilteredPosets

end

noncomputable section
universe u v w z


namespace Thomason.FilteredPushouts
open CategoryTheory Limits

def isColimitOfPushout {J : Type u} [Category.{u} J]
    {C : Type v} [Category.{w} C]
    {A X B Y : J ⥤ C} (a : A ⟶ X) (b : A ⟶ B) (j : X ⟶ Y) (v : B ⟶ Y)
    (sq : ∀ k, IsPushout (a.app k) (b.app k) (j.app k) (v.app k))
    (cA : Cocone A) (cX : Cocone X) (cB : Cocone B) (cY : Cocone Y)
    (hA : IsColimit cA) (hX : IsColimit cX) (hB : IsColimit cB)
    (a₀ : cA.pt ⟶ cX.pt) (b₀ : cA.pt ⟶ cB.pt)
    (j₀ : cX.pt ⟶ cY.pt) (v₀ : cB.pt ⟶ cY.pt)
    (sq₀ : IsPushout a₀ b₀ j₀ v₀)
    (ha : ∀ k, (a.app k) ≫ cX.ι.app k = cA.ι.app k ≫ a₀)
    (hb : ∀ k, (b.app k) ≫ cB.ι.app k = cA.ι.app k ≫ b₀)
    (hj : ∀ k, (j.app k) ≫ cY.ι.app k = cX.ι.app k ≫ j₀)
    (hv : ∀ k, (v.app k) ≫ cY.ι.app k = cB.ι.app k ≫ v₀) :
    IsColimit cY := by
  let cx (s : Cocone Y) : Cocone X := ⟨s.pt,j ≫ s.ι⟩
  let cb (s : Cocone Y) : Cocone B := ⟨s.pt,v ≫ s.ι⟩
  have compat (s : Cocone Y) : a₀ ≫ hX.desc (cx s) = b₀ ≫ hB.desc (cb s) := by
    apply hA.hom_ext
    intro k
    rw [← Category.assoc,← ha,Category.assoc,hX.fac,
      ← Category.assoc _ b₀,← hb,Category.assoc,hB.fac]
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ s.ι.app k) (sq k).w).trans (Category.assoc _ _ _))
  refine {
    desc := fun s => sq₀.desc (hX.desc (cx s)) (hB.desc (cb s)) (compat s)
    fac := ?_
    uniq := ?_ }
  · intro s k
    apply (sq k).hom_ext
    · rw [← Category.assoc,hj,Category.assoc,sq₀.inl_desc,hX.fac]
      rfl
    · rw [← Category.assoc,hv,Category.assoc,sq₀.inr_desc,hB.fac]
      rfl
  · intro s m hm
    apply sq₀.hom_ext
    · rw [sq₀.inl_desc]
      apply hX.hom_ext
      intro k
      rw [← Category.assoc,← hj,Category.assoc,hm,hX.fac]
      rfl
    · rw [sq₀.inr_desc]
      apply hB.hom_ext
      intro k
      rw [← Category.assoc,← hv,Category.assoc,hm,hB.fac]
      rfl

section Attachment
variable {J : Type u} [Category.{u} J] [IsConnected J]
    {C : Type v} [Category.{w} C] [HasPushouts C]
    {A B : J ⥤ C} (cA : Cocone A) (cB : Cocone B)
    (hA : IsColimit cA) (hB : IsColimit cB)
    {X Y : C} (a : cA.pt ⟶ X) (b : A ⟶ B) (b₀ : cA.pt ⟶ cB.pt)
    (hb : b ≫ cB.ι = cA.ι ≫ (CategoryTheory.Functor.const J).map b₀)
    (j : X ⟶ Y) (v : cB.pt ⟶ Y) (sq : IsPushout a b₀ j v)

abbrev attachingMap : A ⟶ (CategoryTheory.Functor.const J).obj X :=
  cA.ι ≫ (CategoryTheory.Functor.const J).map a

abbrev attachmentDiagram : J ⥤ C := pushout (attachingMap cA a) b

def attachmentCocone : Cocone (attachmentDiagram cA a b) where
  pt := Y
  ι := pushout.desc ((CategoryTheory.Functor.const J).map j)
    (cB.ι ≫ (CategoryTheory.Functor.const J).map v) (by
      change (cA.ι ≫ (CategoryTheory.Functor.const J).map a) ≫
        (CategoryTheory.Functor.const J).map j = _
      rw [Category.assoc,← CategoryTheory.Functor.map_comp,sq.w,
        CategoryTheory.Functor.map_comp,← Category.assoc,← hb,Category.assoc])

omit [IsConnected J] in
lemma attachmentCocone_inl (k : J) :
    (pushout.inl (attachingMap cA a) b).app k ≫
      (attachmentCocone cA cB a b b₀ hb j v sq).ι.app k = j := by
  change ((pushout.inl (attachingMap cA a) b) ≫
    (attachmentCocone cA cB a b b₀ hb j v sq).ι).app k = j
  simp only [attachmentCocone,pushout.inl_desc]
  rfl

omit [IsConnected J] in
lemma attachmentCocone_inr (k : J) :
    (pushout.inr (attachingMap cA a) b).app k ≫
      (attachmentCocone cA cB a b b₀ hb j v sq).ι.app k = cB.ι.app k ≫ v := by
  change ((pushout.inr (attachingMap cA a) b) ≫
    (attachmentCocone cA cB a b b₀ hb j v sq).ι).app k = _
  simp only [attachmentCocone,pushout.inr_desc]
  rfl

def attachmentIsColimit : IsColimit (attachmentCocone cA cB a b b₀ hb j v sq) := by
  apply isColimitOfPushout (attachingMap cA a) b
    (pushout.inl (attachingMap cA a) b) (pushout.inr (attachingMap cA a) b)
    (fun k => (IsPushout.of_hasPushout (attachingMap cA a) b).map ((evaluation J C).obj k))
    cA (constCocone J X) cB (attachmentCocone cA cB a b b₀ hb j v sq)
      hA (isColimitConstCocone J X) hB a b₀ j v sq
  · intro k
    change (cA.ι.app k ≫ a) ≫ 𝟙 X = cA.ι.app k ≫ a
    exact Category.comp_id _
  · intro k
    exact congrArg (fun t => t.app k) hb
  · intro k
    change _ = 𝟙 X ≫ j
    rw [Category.id_comp]
    exact attachmentCocone_inl cA cB a b b₀ hb j v sq k
  · exact attachmentCocone_inr cA cB a b b₀ hb j v sq
end Attachment

end Thomason.FilteredPushouts

end

noncomputable section
universe u v w z


namespace Thomason.Couniversality
open CategoryTheory Limits FilteredPosets FilteredPushouts

theorem couniversal_of_finite {D : Type v} [Category.{w} D] [HasPushouts D]
    (L : SSet.{u} ⥤ D) (N : D ⥤ SSet.{u}) [PreservesColimitsOfSize.{u,u} L]
    (hfin : ∀ (P : Type u) [PartialOrder P] [Finite P] (A : Set P),
      IsLowerSet A → ∀ (r : P →o A), (∀ (a : A) (x : P), a.val ≤ x ↔ a ≤ r x) →
      ∀ {X Y : D} (a : L.obj (nerve A) ⟶ X) (j : X ⟶ Y) (v : L.obj (nerve P) ⟶ Y),
        IsPushout a (L.map (nerveMap (OrderEmbedding.subtype A).toOrderHom.toFunctor)) j v →
          simplicialWeakEquivalences (N.map j))
    {E : Type u} [PartialOrder E] [PreservesColimitsOfShape (Finset E) N]
    (A : Set E) (hA : IsLowerSet A) (r : E →o A)
    (hadj : ∀ (a : A) (e : E), a.val ≤ e ↔ a ≤ r e)
    {X Y : D} (a : L.obj (nerve A) ⟶ X) (j : X ⟶ Y) (v : L.obj (nerve E) ⟶ Y)
    (sq : IsPushout a (L.map (nerveMap (OrderEmbedding.subtype A).toOrderHom.toFunctor)) j v) :
    simplicialWeakEquivalences (N.map j) := by
  classical
  let q : E → E := fun e => (r e).val
  have hr (x : A) : r x.val = x :=
    le_antisymm ((hadj (r x.val) x.val).mpr le_rfl) ((hadj x x.val).mp le_rfl)
  have hq (x : E) : q (q x) = q x := congrArg Subtype.val (hr (r x))
  let S := closedFamily q
  let cA := L.mapCocone (PartOrd.nerveFunctor.mapCocone (oldCocone S A))
  let cB := L.mapCocone (PartOrd.nerveFunctor.mapCocone (cocone S))
  have hcA : IsColimit cA := isColimitOfPreserves L
    (oldUnionIsColimit S (closedFamily_cover q) A)
  have hcB : IsColimit cB := isColimitOfPreserves L
    (unionIsColimit S (closedFamily_cover q))
  let b := CategoryTheory.Functor.whiskerRight
    (CategoryTheory.Functor.whiskerRight (inclusion S A) PartOrd.nerveFunctor) L
  let b₀ := L.map (nerveMap (OrderEmbedding.subtype (fun element : E => element ∈ A)).toOrderHom.toFunctor)
  have hb : b ≫ cB.ι = cA.ι ≫ (CategoryTheory.Functor.const (Finset E)).map b₀ := by
    apply NatTrans.ext
    funext s
    change L.map _ ≫ L.map _ = L.map _ ≫ L.map _
    erw [← L.map_comp,← L.map_comp]
    rfl
  let cY := attachmentCocone cA cB a b b₀ hb j v sq
  have hcY : IsColimit cY := attachmentIsColimit cA cB hcA hcB a b b₀ hb j v sq
  let p := pushout.inl (attachingMap cA a) b
  let cp := constCocone (Finset E) X
  have hp (s : Finset E) : simplicialWeakEquivalences (N.map (p.app s)) := by
    let r' : S s →o {x : S s | x.val ∈ A} :=
      ⟨fun x => ⟨⟨(r x.val).val, close_stable q hq s x.property⟩,(r x.val).property⟩,
        fun _ _ h => r.monotone h⟩
    apply hfin (S s) {x : S s | x.val ∈ A} (restricted_lower hA (S s)) r'
      (fun x y => hadj ⟨x.val.val,x.property⟩ y.val) ((attachingMap cA a).app s)
      (p.app s) ((pushout.inr (attachingMap cA a) b).app s)
    exact (IsPushout.of_hasPushout (attachingMap cA a) b).map
      ((evaluation (Finset E) D).obj s)
  apply FilteredWeak.weak_of_colimit (CategoryTheory.Functor.whiskerRight p N)
    (N.mapCocone cp) (N.mapCocone cY)
    (isColimitOfPreserves N (isColimitConstCocone (Finset E) X))
    (isColimitOfPreserves N hcY) (N.map j) _ hp
  intro s
  change N.map (𝟙 X) ≫ N.map j = N.map (p.app s) ≫ N.map (cY.ι.app s)
  rw [N.map_id,Category.id_comp,← N.map_comp]
  exact congrArg (fun f : X ⟶ Y => N.map f)
    (attachmentCocone_inl cA cB a b b₀ hb j v sq s).symm

theorem poset_couniversal
    (T : RightIntervalExtension.{u})
    (R : OmegaCategory.{u} ⥤ OmegaCategory.{u}) (adj : T.tensor ⊣ R)
    (n : ℕ) (hn : 1 ≤ n) {E : Type u} [PartialOrder E]
    (A : Set E) (hA : IsLowerSet A) (r : E →o A)
    (hadj : ∀ (a : A) (e : E), a.val ≤ e ↔ a ≤ r e)
    {X Y : OmegaCategory.NCategory.{u} n} {a : AttachmentComparison.posetObj n A ⟶ X}
    {j : X ⟶ Y} {v : AttachmentComparison.posetObj n E ⟶ Y}
    (sq : IsPushout a (AttachmentComparison.inc n A) j v) :
    simplicialWeakEquivalences ((streetNerveFinite n).map j) := by
  let := (categorificationFiniteAdjunction n).leftAdjoint_preservesColimits
  exact couniversal_of_finite (categorificationFinite n) (streetNerveFinite n)
    (fun P _ _ A hA r hr _ _ a j v sq =>
      finite_poset_couniversal T R adj n hn A hA r hr sq) A hA r hadj a j v sq

theorem omega_poset_couniversal
    (T : RightIntervalExtension.{u})
    {E : Type u} [PartialOrder E] (A : Set E) (hA : IsLowerSet A) (r : E →o A)
    (hadj : ∀ (a : A) (e : E), a.val ≤ e ↔ a ≤ r e)
    {X Y : OmegaCategory.{u}} {a : categorification.obj (nerve A) ⟶ X}
    {j : X ⟶ Y} {v : categorification.obj (nerve E) ⟶ Y}
    (sq : IsPushout a (categorification.map
      (nerveMap (OrderEmbedding.subtype A).toOrderHom.toFunctor)) j v) :
    simplicialWeakEquivalences (streetNerveFunctor.map j) := by
  let := categorificationAdjunction.leftAdjoint_preservesColimits
  exact couniversal_of_finite categorification streetNerveFunctor
    (fun P _ _ A hA r hr _ _ a j v sq =>
      omega_finite_poset_couniversal T A hA r hr sq) A hA r hadj a j v sq

end Thomason.Couniversality

end

noncomputable section
universe u v w z


namespace Thomason.AttachmentComparison
open CategoryTheory Limits OmegaCategory Attachments Couniversality

lemma gray_piece_couniversal (T : RightIntervalExtension.{u})
    (R : OmegaCategory.{u} ⥤ OmegaCategory.{u}) (adj : T.tensor ⊣ R)
    (n : ℕ) (hn : 1 ≤ n) {B : Type u} [PartialOrder B]
    (A S : Set B) (hA : IsLowerSet A) (hAS : A ⊆ S)
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
  exact poset_couniversal T R adj n hn {s : S | s.val ∈ A}
    (restricted_lower hA S) r' (fun a s => hadj ⟨a.val.val,a.property⟩ s) sq'

lemma gray_comparison_local (T : RightIntervalExtension.{u})
    (R : OmegaCategory.{u} ⥤ OmegaCategory.{u}) (adj : T.tensor ⊣ R)
    (n : ℕ) (hn : 1 ≤ n) {B : Type u} [PartialOrder B]
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
    gray_piece_couniversal T R adj n hn A Z hA hAZ r hadj a jZ vZ scZ
  have hwe : simplicialWeakEquivalences e :=
    gray_piece_couniversal T R adj n hn A Z hA hAZ r hadj
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


namespace Thomason.OmegaAttachmentComparison
open CategoryTheory Limits OmegaCategory Attachments Couniversality
open AttachmentComparison (upward)

abbrev posetObj (P : Type u) [PartialOrder P] := categorification.obj (nerve P)
abbrev sb {P : Type u} [PartialOrder P] (A B : Set P) (h : A ⊆ B) :=
  categorification.map (nerveMap (subposetMap A B h).toFunctor)
abbrev inc {P : Type u} [PartialOrder P] (A : Set P) :=
  categorification.map (nerveMap (OrderEmbedding.subtype (fun element : P => element ∈ A)).toOrderHom.toFunctor)

@[reassoc] lemma sb_inc {P : Type u} [PartialOrder P]
    (A B : Set P) (h : A ⊆ B) : sb A B h ≫ inc B = inc A := by
  rw [← categorification.map_comp]
  rfl

lemma attachment_nerve_cover {P : Type u} [PartialOrder P]
    (A Z C : Set P) (hZ : IsUpperSet Z) (hC : IsUpperSet C)
    (hAZ : A ⊆ Z) (hAC : Disjoint A C) (hcover : Z ∪ C = Set.univ)
    {X Y : OmegaCategory.{u}} (a : posetObj A ⟶ X) (j : X ⟶ Y)
    (v : posetObj P ⟶ Y) (sc : IsPushout a (inc A) j v) :
    ∃ (YZ : OmegaCategory.{u}) (jZ : X ⟶ YZ) (vZ : posetObj Z ⟶ YZ) (uZ : YZ ⟶ Y),
      IsPushout a (sb A Z hAZ) jZ vZ ∧ jZ ≫ uZ = j ∧ vZ ≫ uZ = inc Z ≫ v ∧
      IsPushout (streetNerveFunctor.map (sb (Z ∩ C) Z Set.inter_subset_left ≫ vZ))
        (streetNerveFunctor.map (sb (Z ∩ C) C Set.inter_subset_right))
        (streetNerveFunctor.map uZ) (streetNerveFunctor.map (inc C ≫ v)) := by
  obtain ⟨T₁,T₂,hT₁,hT₂,hTc,⟨jZ,vZ,hj,hv,sz⟩,⟨e₂,he₂⟩,⟨e₃,he₃⟩⟩ :=
    cosieve_attachment_covers A Z C hZ hC hAZ hAC hcover a j v sc
  let N := streetNerveFunctor
  let u₁ := (Y.fullOn T₁).inclusion
  let u₂ := (Y.fullOn T₂).inclusion
  let u₃ := (Y.fullOn (T₁ ∩ T₂)).inclusion
  let p₁ : (Y.fullOn (T₁ ∩ T₂)).category ⟶ (Y.fullOn T₁).category :=
    fullOnMap Set.inter_subset_left
  let p₂ : (Y.fullOn (T₁ ∩ T₂)).category ⟶ (Y.fullOn T₂).category :=
    fullOnMap Set.inter_subset_right
  change vZ ≫ u₁ = inc Z ≫ v at hv
  change e₂.hom ≫ u₂ = inc C ≫ v at he₂
  change e₃.hom ≫ u₃ = inc (Z ∩ C) ≫ v at he₃
  have hu₁ : p₁ ≫ u₁ = u₃ := rfl
  have hu₂ : p₂ ≫ u₂ = u₃ := rfl
  have : Mono (N.map u₁) := fullInclusion_nerve_mono Y T₁
  have : Mono (N.map u₂) := fullInclusion_nerve_mono Y T₂
  have sq : IsPushout (N.map p₁) (N.map p₂) (N.map u₁) (N.map u₂) :=
    cosieve_cover_nerve_isPushout hT₁ hT₂ (fun x => by
      have hx : x ∈ T₁ ∪ T₂ := by rw [hTc]; trivial
      exact hx)
  refine ⟨(Y.fullOn T₁).category, jZ, vZ, u₁, sz, hj, hv, ?_⟩
  apply sq.of_iso' (N.mapIso e₃) (Iso.refl _) (N.mapIso e₂) (Iso.refl _)
  · simp only [CategoryTheory.Functor.mapIso_hom, Iso.refl_hom, Category.comp_id]
    change N.map e₃.hom ≫ N.map p₁ = N.map (sb (Z ∩ C) Z Set.inter_subset_left ≫ vZ)
    apply (cancel_mono (N.map u₁)).mp
    simp only [← N.map_comp, Category.assoc, hu₁, he₃, hv]
    rw [sb_inc_assoc]
  · simp only [CategoryTheory.Functor.mapIso_hom]
    change N.map e₃.hom ≫ N.map p₂ = N.map (sb (Z ∩ C) C Set.inter_subset_right) ≫ N.map e₂.hom
    apply (cancel_mono (N.map u₂)).mp
    simp only [← N.map_comp, Category.assoc, hu₂, he₃, he₂]
    rw [sb_inc_assoc]
  · simp [N]
  · simp only [CategoryTheory.Functor.mapIso_hom, Iso.refl_hom, Category.comp_id]
    change N.map e₂.hom ≫ N.map u₂ = N.map (inc C ≫ v)
    rw [← N.map_comp, he₂]

lemma poset_nerve_cover {P : Type u} [PartialOrder P]
    (Z C : Set P) (hZ : IsUpperSet Z) (hC : IsUpperSet C)
    (hcover : Z ∪ C = Set.univ) :
    IsPushout (streetNerveFunctor.map (sb (Z ∩ C) Z Set.inter_subset_left))
      (streetNerveFunctor.map (sb (Z ∩ C) C Set.inter_subset_right))
      (streetNerveFunctor.map (inc Z)) (streetNerveFunctor.map (inc C)) := by
  obtain ⟨YZ,jZ,vZ,uZ,sz,hj,hv,sq⟩ := attachment_nerve_cover (∅ : Set P) Z C
    hZ hC (Set.empty_subset Z) (by simp) hcover
    (𝟙 (posetObj (∅ : Set P))) (inc (∅ : Set P)) (𝟙 (posetObj P))
    (IsPushout.of_id_fst)
  have : IsIso vZ := sz.isIso_inr_of_isIso
  let N := streetNerveFunctor
  apply sq.of_iso' (Iso.refl _) (N.mapIso (asIso vZ)) (Iso.refl _) (Iso.refl _)
  · simp [N]
  · simp
  · simp only [CategoryTheory.Functor.mapIso_hom, asIso_hom, Iso.refl_hom, Category.comp_id]
    change N.map vZ ≫ N.map uZ = N.map (inc Z)
    rw [← N.map_comp, hv, Category.comp_id]
  · simp

lemma nerve_attachment_mono     {B : Type u} [PartialOrder B] (A : Set B) (hA : IsLowerSet A)
    {X Y : OmegaCategory.{u}} (a : posetObj A ⟶ X)
    (j : X ⟶ Y) (v : posetObj B ⟶ Y) (sc : IsPushout a (inc A) j v) :
    Mono (streetNerveFunctor.map j) := by
  obtain ⟨S,hS,e,he⟩ := poset_sieve_attachment A hA a j v sc
  have hinc := OmegaCategory.Subcategory.inclusion_mono (Y.fullOn S)
  have : Mono j := by
    rw [← he]
    infer_instance
  let : PreservesLimits streetNerveFunctor :=
    categorificationAdjunction.rightAdjoint_preservesLimits
  infer_instance

lemma nerve_upper_mono     {P : Type u} [PartialOrder P] (S : Set P) (hS : IsUpperSet S) :
    Mono (streetNerveFunctor.map (inc S)) := by
  let l := NormalizedChains.PosetTables.upperSegmentLabel S hS
  have hS' : S = {p | l p = 1} := by
    ext p
    exact (NormalizedChains.PosetTables.upperSegmentLabel_one S hS p).symm
  let e := posetPieceFiberIso S l 1 hS'
  have he := posetPieceFiberIso_inclusion S l 1 hS'
  have := OmegaCategory.Subcategory.inclusion_mono
    ((posetCategorificationLabel l).fiber (intervalVertex 1))
  have : Mono (inc S) := by
    change Mono (categorification.map
      (nerveMap (OrderEmbedding.subtype (fun element : P => element ∈ S)).toOrderHom.monotone.functor))
    rw [← he]
    infer_instance
  let : PreservesLimits streetNerveFunctor :=
    categorificationAdjunction.rightAdjoint_preservesLimits
  infer_instance

lemma nerve_inter_upper_mono     {P : Type u} [PartialOrder P] (Z C : Set P) (hZ : IsUpperSet Z) :
    Mono (streetNerveFunctor.map (sb (Z ∩ C) C Set.inter_subset_right)) := by
  let e := nestedOldIso categorification (Z ∩ C) C Set.inter_subset_right
  have : Mono (streetNerveFunctor.map (inc {c : C | c.val ∈ Z ∩ C})) :=
    nerve_upper_mono _ (by
      intro x y hxy hx
      exact ⟨hZ hxy hx.1,y.property⟩)
  have he : sb (Z ∩ C) C Set.inter_subset_right =
      e.inv ≫ inc {c : C | c.val ∈ Z ∩ C} := by
    calc
      _ = e.inv ≫ (e.hom ≫ sb (Z ∩ C) C Set.inter_subset_right) := by simp
      _ = _ := congrArg (e.inv ≫ ·) (nestedOldIso_inc
        categorification (Z ∩ C) C Set.inter_subset_right)
  rw [he, CategoryTheory.Functor.map_comp]
  infer_instance

lemma gray_piece_couniversal (T : RightIntervalExtension.{u})
    {B : Type u} [PartialOrder B]
    (A S : Set B) (hA : IsLowerSet A) (hAS : A ⊆ S)
    (r : S →o A) (hadj : ∀ (a : A) (s : S), a.val ≤ s.val ↔ a ≤ r s)
    {X Y : OmegaCategory.{u}} (a : posetObj A ⟶ X)
    (j : X ⟶ Y) (v : posetObj S ⟶ Y)
    (sq : IsPushout a (sb A S hAS) j v) :
    simplicialWeakEquivalences (streetNerveFunctor.map j) := by
  let e := nestedOldIso categorification A S hAS
  let r' : S →o {s : S | s.val ∈ A} :=
    ⟨fun s => ⟨⟨(r s).val,hAS (r s).property⟩,(r s).property⟩,
      fun _ _ h => r.monotone h⟩
  have sq' : IsPushout (e.hom ≫ a) (inc {s : S | s.val ∈ A}) j v := by
    apply sq.of_iso' e (Iso.refl _) (Iso.refl _) (Iso.refl _)
    · simp
    · simp only [Iso.refl_hom,Category.comp_id]
      exact nestedOldIso_inc categorification A S hAS
    · simp
    · simp
  exact omega_poset_couniversal T {s : S | s.val ∈ A}
    (restricted_lower hA S) r' (fun a s => hadj ⟨a.val.val,a.property⟩ s) sq'

lemma gray_comparison_local (T : RightIntervalExtension.{u})
    {B : Type u} [PartialOrder B]
    (A : Set B) (hA : IsLowerSet A)
    (r : upward A →o A)
    (hadj : ∀ (a : A) (z : upward A), a.val ≤ z.val ↔ a ≤ r z)
    {X Y : OmegaCategory.{u}} (a : posetObj A ⟶ X)
    (j : X ⟶ Y) (v : posetObj B ⟶ Y) (sc : IsPushout a (inc A) j v)
    {P : SSet.{u}} {lX : streetNerveFunctor.obj X ⟶ P}
    {lB : streetNerveFunctor.obj (posetObj B) ⟶ P}
    (ss : IsPushout (streetNerveFunctor.map a) (streetNerveFunctor.map (inc A)) lX lB)
    (F : P ⟶ streetNerveFunctor.obj Y)
    (hFX : lX ≫ F = streetNerveFunctor.map j)
    (hFB : lB ≫ F = streetNerveFunctor.map v) : simplicialWeakEquivalences F := by
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
    attachment_nerve_cover A Z C hZ hC hAZ disjoint_compl_right hcov a j v sc
  let N := streetNerveFunctor
  let e := N.map (sb A Z hAZ)
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
    gray_piece_couniversal T A Z hA hAZ r hadj a jZ vZ scZ
  have hwe : simplicialWeakEquivalences e :=
    gray_piece_couniversal T A Z hA hAZ r hadj
      (𝟙 _) (sb A Z hAZ) (𝟙 _) IsPushout.of_id_fst
  have hcE : Mono e := by
    let e' := nestedOldIso categorification A Z hAZ
    have he' : sb A Z hAZ = e'.inv ≫ inc {z : Z | z.val ∈ A} := by
      calc
        _ = e'.inv ≫ (e'.hom ≫ sb A Z hAZ) := by simp
        _ = _ := congrArg (e'.inv ≫ ·) (nestedOldIso_inc categorification A Z hAZ)
    have : Mono (N.map (inc {z : Z | z.val ∈ A})) :=
      nerve_attachment_mono _ (restricted_lower hA Z)
        (𝟙 _) _ (𝟙 _) IsPushout.of_id_fst
    dsimp [e]
    rw [he',CategoryTheory.Functor.map_comp]
    infer_instance
  have hwx : simplicialWeakEquivalences xZ := by
    have he : SSet.anodyneExtensions e := KanQuillen.anodyne_class.symm ▸ ⟨hcE,hwe⟩
    exact KanQuillen.anodyne_weak _ (SSet.anodyneExtensions.of_isPushout sZ he)
  have hwFZ : simplicialWeakEquivalences FZ :=
    simplicialWeakEquivalences.of_precomp xZ FZ hwx (hFZX ▸ hwj)
  let pZ : PZ ⟶ P := sZ.desc lX (N.map (inc Z) ≫ lB) (by
    rw [← Category.assoc, ← N.map_comp, sb_inc]
    exact ss.w)
  have hpZX : xZ ≫ pZ = lX := sZ.inl_desc _ _ _
  have hpZZ : zZ ≫ pZ = N.map (inc Z) ≫ lB := sZ.inr_desc _ _ _
  have ss' : IsPushout b (e ≫ N.map (inc Z)) (xZ ≫ pZ) lB := by
    rw [hpZX, ← N.map_comp, sb_inc]
    exact ss
  have sr : IsPushout zZ (N.map (inc Z)) pZ lB := ss'.of_top hpZZ sZ
  have sp := (poset_nerve_cover Z C hZ hC hcov).paste_horiz sr
  let k := N.map (sb (Z ∩ C) Z Set.inter_subset_left) ≫ zZ
  let c := N.map (sb (Z ∩ C) C Set.inter_subset_right)
  have hc : Mono c := nerve_inter_upper_mono Z C hZ
  have hk : k ≫ FZ = N.map (sb (Z ∩ C) Z Set.inter_subset_left ≫ vZ) := by
    rw [show k = N.map (sb (Z ∩ C) Z Set.inter_subset_left) ≫ zZ from rfl,
      Category.assoc, hFZZ, ← N.map_comp]
  have sq' : IsPushout (k ≫ FZ) c (N.map uZ) (N.map (inc C ≫ v)) := by
    rw [hk]
    exact sq
  have hFpZ : pZ ≫ F = FZ ≫ N.map uZ := by
    apply sZ.hom_ext
    · rw [← Category.assoc, hpZX, ← Category.assoc xZ, hFZX, ← N.map_comp, hj]
      exact hFX
    · rw [← Category.assoc, hpZZ, Category.assoc, hFB,
        ← Category.assoc zZ, hFZZ, ← N.map_comp, ← N.map_comp, hv]
  have hFC : (N.map (inc C) ≫ lB) ≫ F = N.map (inc C ≫ v) := by
    rw [Category.assoc, hFB, ← N.map_comp]
  exact KanLocal.local_weak F (KanLocal.local_pushout_map k c FZ
    (GeometricRecognition.weak_local FZ hwFZ) sp sq' F hFpZ hFC)

end Thomason.OmegaAttachmentComparison

end

end OAI
