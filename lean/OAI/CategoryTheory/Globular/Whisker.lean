import OAI.CategoryTheory.Globular.RelativeLifting

namespace OAI

universe u v w

namespace Grothendieck.GlobularTheory
open CategoryTheory CategoryTheory.Limits Opposite

structure RepresentedHom {C : GlobularTheory.{v}} {K : Type u} [Category.{v} K]
    (F : C.Obj ⥤ K) (R : Shape ⥤ K)
    (e₀ e₁ : C.toTheoryData.arity ⋙ F ⟶ R) (S T : Shape) where
  original : C.Hom S T
  cylinder : R.obj S ⟶ R.obj T
  endpoint₀ : e₀.app S ≫ cylinder = F.map (show C.toTheoryData.arity.obj S ⟶ C.toTheoryData.arity.obj T from original) ≫ e₀.app T
  endpoint₁ : e₁.app S ≫ cylinder = F.map (show C.toTheoryData.arity.obj S ⟶ C.toTheoryData.arity.obj T from original) ≫ e₁.app T

@[ext] theorem RepresentedHom.ext {C : GlobularTheory.{v}} {K : Type u} [Category.{v} K]
    {F : C.Obj ⥤ K} {R : Shape ⥤ K} {e₀ e₁ : C.toTheoryData.arity ⋙ F ⟶ R}
    {S T : Shape} {a b : RepresentedHom F R e₀ e₁ S T}
    (h : a.original = b.original) (k : a.cylinder = b.cylinder) : a = b := by
  cases a
  cases b
  cases h
  cases k
  rfl

noncomputable def representedData {C : GlobularTheory.{v}} {K : Type u} [Category.{v} K]
    (F : C.Obj ⥤ K) (R : Shape ⥤ K)
    (e₀ e₁ : C.toTheoryData.arity ⋙ F ⟶ R) : TheoryData.{v} where
  Hom := RepresentedHom F R e₀ e₁
  id S := ⟨C.id S, 𝟙 _, by
    change e₀.app S ≫ 𝟙 _ = F.map (𝟙 _) ≫ e₀.app S
    simp, by
    change e₁.app S ≫ 𝟙 _ = F.map (𝟙 _) ≫ e₁.app S
    simp⟩
  comp a b :=
    { original := C.comp a.original b.original
      cylinder := a.cylinder ≫ b.cylinder
      endpoint₀ := by
        rw [← Category.assoc, a.endpoint₀, Category.assoc, b.endpoint₀, ← Category.assoc]
        exact congrArg (· ≫ e₀.app _) (F.map_comp a.original b.original).symm
      endpoint₁ := by
        rw [← Category.assoc, a.endpoint₁, Category.assoc, b.endpoint₁, ← Category.assoc]
        exact congrArg (· ≫ e₁.app _) (F.map_comp a.original b.original).symm }
  id_comp a := RepresentedHom.ext (C.id_comp _) (Category.id_comp _)
  comp_id a := RepresentedHom.ext (C.comp_id _) (Category.comp_id _)
  assoc a b c := RepresentedHom.ext (C.assoc _ _ _) (Category.assoc _ _ _)
  base f := ⟨C.base f, R.map f, (e₀.naturality f).symm, (e₁.naturality f).symm⟩
  base_id S := RepresentedHom.ext (C.base_id S) (R.map_id S)
  base_comp a b := RepresentedHom.ext (C.base_comp a b) (R.map_comp a b)

noncomputable def representedTheory {C : GlobularTheory.{v}} {K : Type u} [Category.{v} K]
    (F : C.Obj ⥤ K) (R : Shape ⥤ K)
    (e₀ e₁ : C.toTheoryData.arity ⋙ F ⟶ R)
    (hR : ∀ (S : Shape) b h hl hr, IsPushout
      (R.map (S.seam hl)) (R.map (Shape.face hr false))
      (R.map (S.inl b h hl hr)) (R.map (S.inr b h hl hr)))
    (hF : ∀ (S : Shape) b h hl hr, IsPushout
      (F.map (C.base (S.seam hl))) (F.map (C.base (Shape.face hr false)))
      (F.map (C.base (S.inl b h hl hr))) (F.map (C.base (S.inr b h hl hr)))) :
    GlobularTheory.{v} where
  toTheoryData := representedData F R e₀ e₁
  sums S b h hl hr := by
    apply IsPushout.mk'
    · exact RepresentedHom.ext (C.sums S b h hl hr).w (hR S b h hl hr).w
    · intro T a a' ha hb
      apply RepresentedHom.ext
      · exact (C.sums S b h hl hr).hom_ext (W := C.toTheoryData.arity.obj T.shape)
          (congrArg RepresentedHom.original ha) (congrArg RepresentedHom.original hb)
      · exact (hR S b h hl hr).hom_ext
          (congrArg RepresentedHom.cylinder ha) (congrArg RepresentedHom.cylinder hb)
    · intro T a b' hab
      change RepresentedHom F R e₀ e₁ S T.shape at a
      change RepresentedHom F R e₀ e₁ (Shape.globe h) T.shape at b'
      let d : C.Hom (S.attach b h hl hr) T.shape :=
        (C.sums S b h hl hr).desc (W := C.toTheoryData.arity.obj T.shape) a.original b'.original
          (congrArg RepresentedHom.original hab)
      let l : R.obj (S.attach b h hl hr) ⟶ R.obj T.shape :=
        (hR S b h hl hr).desc a.cylinder b'.cylinder
          (congrArg RepresentedHom.cylinder hab)
      have hd₀ : C.comp (C.base (S.inl b h hl hr)) d = a.original :=
        (C.sums S b h hl hr).inl_desc _ _ _
      have hd₁ : C.comp (C.base (S.inr b h hl hr)) d = b'.original :=
        (C.sums S b h hl hr).inr_desc _ _ _
      have hl₀ : R.map (S.inl b h hl hr) ≫ l = a.cylinder :=
        (hR S b h hl hr).inl_desc _ _ _
      have hl₁ : R.map (S.inr b h hl hr) ≫ l = b'.cylinder :=
        (hR S b h hl hr).inr_desc _ _ _
      have he (e : C.toTheoryData.arity ⋙ F ⟶ R)
          (ha : e.app S ≫ a.cylinder = F.map a.original ≫ e.app T.shape)
          (hb : e.app (Shape.globe h) ≫ b'.cylinder = F.map b'.original ≫ e.app T.shape) :
          e.app (S.attach b h hl hr) ≫ l = F.map d ≫ e.app T.shape := by
        apply (hF S b h hl hr).hom_ext
        · change (C.toTheoryData.arity ⋙ F).map (S.inl b h hl hr) ≫
            e.app (S.attach b h hl hr) ≫ l =
            F.map (C.base (S.inl b h hl hr)) ≫ F.map d ≫ e.app T.shape
          rw [← Category.assoc, e.naturality, Category.assoc, hl₀, ha]
          simpa only [Category.assoc, Functor.comp_obj, TheoryData.arity, Shape.globe] using congrArg (· ≫ e.app T.shape)
            ((F.map_comp (C.base (S.inl b h hl hr)) d).symm.trans
              (congrArg F.map hd₀)).symm
        · change (C.toTheoryData.arity ⋙ F).map (S.inr b h hl hr) ≫
            e.app (S.attach b h hl hr) ≫ l =
            F.map (C.base (S.inr b h hl hr)) ≫ F.map d ≫ e.app T.shape
          rw [← Category.assoc, e.naturality, Category.assoc, hl₁, hb]
          simpa only [Category.assoc, Functor.comp_obj, TheoryData.arity, Shape.globe] using congrArg (· ≫ e.app T.shape)
            ((F.map_comp (C.base (S.inr b h hl hr)) d).symm.trans
              (congrArg F.map hd₁)).symm
      let w : RepresentedHom F R e₀ e₁ (S.attach b h hl hr) T.shape :=
        ⟨d, l, he e₀ a.endpoint₀ b'.endpoint₀, he e₁ a.endpoint₁ b'.endpoint₁⟩
      exact ⟨w, RepresentedHom.ext hd₀ ((hR S b h hl hr).inl_desc _ _ _),
        RepresentedHom.ext hd₁ ((hR S b h hl hr).inr_desc _ _ _)⟩

noncomputable def representedProjection {C : GlobularTheory.{v}} {K : Type u} [Category.{v} K]
    (F : C.Obj ⥤ K) (R : Shape ⥤ K)
    (e₀ e₁ : C.toTheoryData.arity ⋙ F ⟶ R) (hR hF) :
    Morphism (representedTheory F R e₀ e₁ hR hF) C where
  map f := f.original
  map_id _ := rfl
  map_comp _ _ := rfl
  map_base _ := rfl

end Grothendieck.GlobularTheory

namespace Grothendieck.GlobularSet

inductive WhiskerCell (X : GlobularSet.{u}) (n : ℕ) : ℕ → Type u
  | base (k : ℕ) : X.Cell k → WhiskerCell X n k
  | tip : X.Cell n → WhiskerCell X n n
  | edge : X.Cell n → WhiskerCell X n (n+1)

namespace WhiskerCell

def source {X : GlobularSet.{u}} (n : ℕ) (ε : Bool) (k : ℕ)
    (x : WhiskerCell X n (k+1)) : WhiskerCell X n k := by
  cases x with
  | base _ x => exact .base _ (X.source k x)
  | tip x => exact .base _ (X.source k x)
  | edge x => exact if ε then .tip x else .base _ x

def target {X : GlobularSet.{u}} (n : ℕ) (ε : Bool) (k : ℕ)
    (x : WhiskerCell X n (k+1)) : WhiskerCell X n k := by
  cases x with
  | base _ x => exact .base _ (X.target k x)
  | tip x => exact .base _ (X.target k x)
  | edge x => exact if ε then .base _ x else .tip x

@[simp] theorem source_base {X : GlobularSet.{u}} (n : ℕ) (ε : Bool)
    (k : ℕ) (x : X.Cell (k+1)) :
    source n ε k (.base _ x) = .base _ (X.source k x) := rfl

@[simp] theorem target_base {X : GlobularSet.{u}} (n : ℕ) (ε : Bool)
    (k : ℕ) (x : X.Cell (k+1)) :
    target n ε k (.base _ x) = .base _ (X.target k x) := rfl

@[simp] theorem source_tip {X : GlobularSet.{u}} (ε : Bool)
    (k : ℕ) (x : X.Cell (k+1)) :
    source (k+1) ε k (.tip x) = .base _ (X.source k x) := rfl

@[simp] theorem target_tip {X : GlobularSet.{u}} (ε : Bool)
    (k : ℕ) (x : X.Cell (k+1)) :
    target (k+1) ε k (.tip x) = .base _ (X.target k x) := rfl

@[simp] theorem source_edge {X : GlobularSet.{u}} (n : ℕ) (ε : Bool)
    (x : X.Cell n) : source n ε n (.edge x) = if ε then .tip x else .base _ x := rfl

@[simp] theorem target_edge {X : GlobularSet.{u}} (n : ℕ) (ε : Bool)
    (x : X.Cell n) : target n ε n (.edge x) = if ε then .base _ x else .tip x := rfl

end WhiskerCell

def whisker (X : GlobularSet.{u}) (n : ℕ) (ε : Bool) : GlobularSet.{u} where
  Cell := WhiskerCell X n
  source := WhiskerCell.source n ε
  target := WhiskerCell.target n ε
  source_source k x := by
    cases x with
    | base _ x => simp only [WhiskerCell.source_base, WhiskerCell.target_base,
        X.source_source]
    | tip x => simp only [WhiskerCell.source_tip, WhiskerCell.target_tip,
        WhiskerCell.source_base, X.source_source]
    | edge x => cases ε <;> rfl
  target_source k x := by
    cases x with
    | base _ x => simp only [WhiskerCell.source_base, WhiskerCell.target_base,
        X.target_source]
    | tip x => simp only [WhiskerCell.source_tip, WhiskerCell.target_tip,
        WhiskerCell.target_base, X.target_source]
    | edge x => cases ε <;> rfl

def whiskerInclusion (X : GlobularSet.{u}) (n : ℕ) (ε : Bool) : Hom X (X.whisker n ε) where
  app := WhiskerCell.base
  source_app _ _ := rfl
  target_app _ _ := rfl

def whiskerMap {X Y : GlobularSet.{u}} (f : Hom X Y) (n : ℕ) (ε : Bool) :
    Hom (X.whisker n ε) (Y.whisker n ε) where
  app _ x := match x with
    | .base k x => .base k (f.app k x)
    | .tip x => .tip (f.app n x)
    | .edge x => .edge (f.app n x)
  source_app k x := by
    cases x with
    | base _ x => exact congrArg (WhiskerCell.base k) (f.source_app k x)
    | tip x => exact congrArg (WhiskerCell.base k) (f.source_app k x)
    | edge x => cases ε <;> rfl
  target_app k x := by
    cases x with
    | base _ x => exact congrArg (WhiskerCell.base k) (f.target_app k x)
    | tip x => exact congrArg (WhiskerCell.base k) (f.target_app k x)
    | edge x => cases ε <;> rfl

theorem whisker_bounded (X : GlobularSet.{u}) (n : ℕ) (ε : Bool)
    (hX : ∀ k, n+1 < k → IsEmpty (X.Cell k)) (k : ℕ) (hk : n+1 < k) :
    IsEmpty ((X.whisker n ε).Cell k) := by
  constructor
  intro x
  cases x with
  | base k x => exact (hX k hk).false x
  | tip x => omega
  | edge x => omega

theorem whiskerMap_injective {X Y : GlobularSet.{u}} (f : Hom X Y)
    (hf : ∀ k, Function.Injective (f.app k)) (n : ℕ) (ε : Bool) (k : ℕ) :
    Function.Injective ((whiskerMap f n ε).app k) := by
  intro x y h
  cases x <;> cases y <;>
    simp only [whiskerMap, reduceCtorEq] at h
  all_goals congr 1; apply hf; injection h


def toPresheafUnderlying (X : GlobularSet.{u}) : Hom X X.presheaf.underlying where
  app _ := _root_.id
  source_app n x := (X.presheafUnderlyingMap.source_app n x).symm
  target_app n x := (X.presheafUnderlyingMap.target_app n x).symm

def whiskerDesc {X Y : GlobularSet.{u}} (n : ℕ) (f : Hom X Y)
    (e : X.Cell n → Y.Cell (n+1)) (he : ∀ x, Y.source n (e x) = f.app n x) :
    Hom (X.whisker n false) Y where
  app _ x := match x with
    | .base k x => f.app k x
    | .tip x => Y.target n (e x)
    | .edge x => e x
  source_app k x := by
    cases x with
    | base _ x => exact f.source_app k x
    | tip x =>
      change f.app k (X.source k x) = Y.source k (Y.target (k+1) (e x))
      rw [f.source_app, ← he, Y.source_source]
    | edge x => exact (he x).symm
  target_app k x := by
    cases x with
    | base _ x => exact f.target_app k x
    | tip x =>
      change f.app k (X.target k x) = Y.target k (Y.target (k+1) (e x))
      rw [f.target_app, ← he, Y.target_source]
    | edge x => rfl

theorem whisker_hom_ext {X Y : GlobularSet.{u}} (n : ℕ) (ε : Bool)
    (f g : Hom (X.whisker n ε) Y)
    (hbase : ∀ k x, f.app k (.base k x) = g.app k (.base k x))
    (hedge : ∀ x, f.app (n+1) (.edge x) = g.app (n+1) (.edge x)) : f = g := by
  ext k x
  cases x with
  | base k x => exact hbase k x
  | edge x => exact hedge x
  | tip x =>
    cases ε with
    | false =>
      have hf := f.target_app n (.edge x)
      have hg := g.target_app n (.edge x)
      exact hf.trans ((congrArg (Y.target n) (hedge x)).trans hg.symm)
    | true =>
      have hf := f.source_app n (.edge x)
      have hg := g.source_app n (.edge x)
      exact hf.trans ((congrArg (Y.source n) (hedge x)).trans hg.symm)

end Grothendieck.GlobularSet

namespace Grothendieck.GlobularPresheaf
open CategoryTheory CategoryTheory.Limits Opposite

def whiskering (n : ℕ) (ε : Bool) : GlobularPresheaf.{u} ⥤ GlobularPresheaf.{u} where
  obj X := (X.underlying.whisker n ε).presheaf
  map f := (GlobularSet.whiskerMap (underlyingMap f) n ε).presheafMap
  map_id X := by
    ext ⟨⟨k⟩⟩ x
    cases x <;> rfl
  map_comp f g := by
    ext ⟨⟨k⟩⟩ x
    cases x <;> rfl

def whiskeringInclusion (n : ℕ) (ε : Bool) : 𝟭 GlobularPresheaf.{u} ⟶ whiskering n ε where
  app X := X.underlyingPresheafIso.inv ≫ (X.underlying.whiskerInclusion n ε).presheafMap
  naturality {X Y} f := by ext; rfl

def whiskeringDesc {X Y : GlobularPresheaf.{u}} (n : ℕ) (f : X ⟶ Y)
    (e : X.underlying.Cell n → Y.underlying.Cell (n+1))
    (he : ∀ x, Y.underlying.source n (e x) = (underlyingMap f).app n x) :
    (whiskering n false).obj X ⟶ Y :=
  (GlobularSet.whiskerDesc n (underlyingMap f) e he).presheafMap ≫ Y.underlyingPresheafIso.hom

theorem whiskering_hom_ext {X Y : GlobularPresheaf.{u}} (n : ℕ) (ε : Bool)
    (f g : (whiskering n ε).obj X ⟶ Y)
    (hbase : ∀ k x, f.app (op (Globe.mk k)) (.base k x) =
      g.app (op (Globe.mk k)) (.base k x))
    (hedge : ∀ x, f.app (op (Globe.mk (n+1))) (.edge x) =
      g.app (op (Globe.mk (n+1))) (.edge x)) : f = g := by
  apply underlyingMap_injective
  have h := GlobularSet.whisker_hom_ext n ε
    ((X.underlying.whisker n ε).toPresheafUnderlying.comp (underlyingMap f))
    ((X.underlying.whisker n ε).toPresheafUnderlying.comp (underlyingMap g)) hbase hedge
  ext k x
  exact congrFun (congrArg (fun z => z.app k) h) x

theorem whiskering_pushout {A B D E : GlobularPresheaf.{u}}
    {f : A ⟶ B} {g : A ⟶ D} {i : B ⟶ E} {j : D ⟶ E}
    (h : IsPushout f g i j) (n : ℕ) : IsPushout
      ((whiskering n false).map f) ((whiskering n false).map g)
      ((whiskering n false).map i) ((whiskering n false).map j) := by
  let W := whiskering n false
  let η := whiskeringInclusion n false
  let N := (evaluation Globeᵒᵖ (Type u)).obj (op (Globe.mk n))
  have hn := h.map N
  have ηi : i ≫ η.app E = η.app B ≫ W.map i := η.naturality i
  have ηj : j ≫ η.app E = η.app D ≫ W.map j := η.naturality j
  have ηf : f ≫ η.app B = η.app A ≫ W.map f := η.naturality f
  have ηg : g ≫ η.app D = η.app A ≫ W.map g := η.naturality g
  apply IsPushout.mk'
  · rw [← W.map_comp, ← W.map_comp, h.w]
  · intro T a b ha hb
    apply whiskering_hom_ext n false a b
    · have he : η.app E ≫ a = η.app E ≫ b := h.hom_ext
        (by rw [← Category.assoc, ηi, Category.assoc, ha,
          ← Category.assoc, ← ηi, Category.assoc])
        (by rw [← Category.assoc, ηj, Category.assoc, hb,
          ← Category.assoc, ← ηj, Category.assoc])
      intro k x
      exact congrFun (congrArg (fun z => z.app (op (Globe.mk k))) he) x
    · have he := hn.hom_ext (W := T.obj (op (Globe.mk (n+1))))
        (k := TypeCat.ofHom (fun x => a.app (op (Globe.mk (n+1))) (.edge x)))
        (l := TypeCat.ofHom (fun x => b.app (op (Globe.mk (n+1))) (.edge x)))
        (by ext x; exact congrFun (congrArg (fun z => z.app (op (Globe.mk (n+1)))) ha) (.edge x))
        (by ext x; exact congrFun (congrArg (fun z => z.app (op (Globe.mk (n+1)))) hb) (.edge x))
      exact fun x => ConcreteCategory.congr_hom he x
  · intro T a b hab
    have hf : f ≫ η.app B ≫ a = g ≫ η.app D ≫ b := by
      rw [← Category.assoc, ηf, Category.assoc, hab,
        ← Category.assoc, ← ηg, Category.assoc]
    let d : E ⟶ T := h.desc (η.app B ≫ a) (η.app D ≫ b) hf
    have hw : N.map f ≫ TypeCat.ofHom (fun x => a.app (op (Globe.mk (n+1))) (.edge x)) =
        N.map g ≫ TypeCat.ofHom (fun x => b.app (op (Globe.mk (n+1))) (.edge x)) := by
      ext x
      exact congrFun (congrArg (fun z => z.app (op (Globe.mk (n+1)))) hab) (.edge x)
    let t : E.obj (op (Globe.mk n)) ⟶ T.obj (op (Globe.mk (n+1))) :=
      hn.desc (TypeCat.ofHom (fun x => a.app (op (Globe.mk (n+1))) (.edge x)))
        (TypeCat.ofHom (fun x => b.app (op (Globe.mk (n+1))) (.edge x))) hw
    have ht : ∀ x, T.underlying.source n (t x) = (underlyingMap d).app n x := by
      have he : t ≫ T.map (Globe.source n).op = d.app (op (Globe.mk n)) := by
        apply hn.hom_ext
        · rw [← Category.assoc, hn.inl_desc]
          have hd := congrArg (fun z => z.app (op (Globe.mk n))) (h.inl_desc _ _ hf)
          change _ = (i ≫ d).app (op (Globe.mk n))
          rw [hd]
          ext x
          exact (((B.underlying.whisker n false).toPresheafUnderlying.comp
            (underlyingMap a)).source_app n (.edge x)).symm
        · rw [← Category.assoc, hn.inr_desc]
          have hd := congrArg (fun z => z.app (op (Globe.mk n))) (h.inr_desc _ _ hf)
          change _ = (j ≫ d).app (op (Globe.mk n))
          rw [hd]
          ext x
          exact (((D.underlying.whisker n false).toPresheafUnderlying.comp
            (underlyingMap b)).source_app n (.edge x)).symm
      exact fun x => ConcreteCategory.congr_hom he x
    let l := whiskeringDesc n d t ht
    refine ⟨l, ?_, ?_⟩
    · apply whiskering_hom_ext n false
      · intro k x
        exact congrFun (congrArg (fun z => z.app (op (Globe.mk k)))
          (h.inl_desc _ _ hf)) x
      · intro x
        exact ConcreteCategory.congr_hom (hn.inl_desc _ _ hw) x
    · apply whiskering_hom_ext n false
      · intro k x
        exact congrFun (congrArg (fun z => z.app (op (Globe.mk k)))
          (h.inr_desc _ _ hf)) x
      · intro x
        exact ConcreteCategory.congr_hom (hn.inr_desc _ _ hw) x

end Grothendieck.GlobularPresheaf

end OAI
