import OAI.CategoryTheory.Globular.Factorization

namespace OAI

universe u v w

namespace Grothendieck

open CategoryTheory CategoryTheory.Limits Opposite

namespace GlobularTheory.Model

def OperationCompatible {C : GlobularTheory.{v}} {R Y : C.Model}
    (g : R.tuples.presheaf ⟶ Y.tuples.presheaf) {S T : Shape} (u : C.Hom S T) : Prop :=
  ∀ x, g.app (op S) (R.eval u x) = Y.eval u (g.app (op T) x)

noncomputable def compatibleData {C : GlobularTheory.{v}} {R Y : C.Model}
    (g : R.tuples.presheaf ⟶ Y.tuples.presheaf) : TheoryData.{v} where
  Hom S T := {u : C.Hom S T // OperationCompatible g u}
  id S := ⟨C.id S, fun x => (congrArg (g.app (op S)) (R.eval_id x)).trans
      (Y.eval_id _).symm⟩
  comp {S _T U} a b := ⟨C.comp a.1 b.1, fun x =>
    (congrArg (g.app (op S)) (R.eval_comp a.1 b.1 x)).trans
      ((a.2 (R.eval b.1 x)).trans
        ((congrArg (Y.eval a.1) (b.2 x)).trans
          (Y.eval_comp a.1 b.1 (g.app (op U) x)).symm))⟩
  id_comp a := Subtype.ext (C.id_comp a.1)
  comp_id a := Subtype.ext (C.comp_id a.1)
  assoc a b c := Subtype.ext (C.assoc a.1 b.1 c.1)
  base u := ⟨C.base u, fun x => ConcreteCategory.congr_hom (g.naturality u.op) x⟩
  base_id S := Subtype.ext (C.base_id S)
  base_comp a b := Subtype.ext (C.base_comp a b)

noncomputable def compatibleTheory {C : GlobularTheory.{v}} {R Y : C.Model}
    (g : R.tuples.presheaf ⟶ Y.tuples.presheaf) : GlobularTheory.{v} where
  toTheoryData := compatibleData g
  sums S b h hl hr := by
    apply IsPushout.mk'
    · apply Subtype.ext
      exact (C.sums S b h hl hr).w
    · intro T a a' ha hb
      apply Subtype.ext
      apply (C.sums S b h hl hr).hom_ext (W := (⟨T.shape⟩ : C.Obj))
      · exact congrArg Subtype.val ha
      · exact congrArg Subtype.val hb
    · intro T a b' hab
      let d : C.Hom (S.attach b h hl hr) T.shape :=
        (C.sums S b h hl hr).desc (W := (⟨T.shape⟩ : C.Obj)) a.1 b'.1
          (congrArg Subtype.val hab)
      have hd₀ : C.comp (C.base (S.inl b h hl hr)) d = a.1 :=
        (C.sums S b h hl hr).inl_desc _ _ _
      have hd₁ : C.comp (C.base (S.inr b h hl hr)) d = b'.1 :=
        (C.sums S b h hl hr).inr_desc _ _ _
      have hd : OperationCompatible g d := by
        intro x
        apply Types.ext_of_isPullback (Y.sums S b h hl hr)
        · have w := ConcreteCategory.congr_hom
            (g.naturality (S.inl b h hl hr).op) (R.eval d x)
          change g.app (op S) (R.eval (C.base (S.inl b h hl hr)) (R.eval d x)) = _ at w
          have wr := (R.eval_comp (C.base (S.inl b h hl hr)) d x).symm.trans
            (congrArg (fun z => R.eval z x) hd₀)
          have wy := (Y.eval_comp (C.base (S.inl b h hl hr)) d
            (g.app (op T.shape) x)).symm.trans
            (congrArg (fun z => Y.eval z (g.app (op T.shape) x)) hd₀)
          exact w.symm.trans ((congrArg (g.app (op S)) wr).trans ((a.2 x).trans wy.symm))
        · have w := ConcreteCategory.congr_hom
            (g.naturality (S.inr b h hl hr).op) (R.eval d x)
          have wr := (R.eval_comp (C.base (S.inr b h hl hr)) d x).symm.trans
            (congrArg (fun z => R.eval z x) hd₁)
          have wy := (Y.eval_comp (C.base (S.inr b h hl hr)) d
            (g.app (op T.shape) x)).symm.trans
            (congrArg (fun z => Y.eval z (g.app (op T.shape) x)) hd₁)
          exact w.symm.trans ((congrArg (g.app (op (Shape.globe h))) wr).trans
            ((b'.2 x).trans wy.symm))
      exact ⟨⟨d, hd⟩, Subtype.ext hd₀, Subtype.ext hd₁⟩

noncomputable def compatibleProjection {C : GlobularTheory.{v}} {R Y : C.Model}
    (g : R.tuples.presheaf ⟶ Y.tuples.presheaf) : Morphism (compatibleTheory g) C where
  map u := u.1
  map_id _ := rfl
  map_comp _ _ := rfl
  map_base _ := rfl

theorem compatibleProjection_liftsFillers {C : GlobularTheory.{v}}
    {X R Y : C.Model} (η : X ⟶ R) (f : X ⟶ Y)
    (g : R.tuples.presheaf ⟶ Y.tuples.presheaf) (q : ℕ)
    (hη : ∀ k, k ≤ q → Function.Bijective ((underlyingMap η).app k))
    (hY : ∀ j, q < j → Function.Bijective (Y.underlying.boundary j))
    (hg : (Functor.whiskerLeft C.toTheoryData.arity.op η) ≫ g =
      Functor.whiskerLeft C.toTheoryData.arity.op f) :
    LiftsFillers (compatibleProjection g) := by
  intro p z hz
  have hnat : OperationCompatible g z := by
    intro x
    by_cases hn : p.n+1 ≤ q
    · have ht : Function.Bijective
          ((Functor.whiskerLeft C.toTheoryData.arity.op η).app (op p.arity)) :=
        TupleSystem.bijective_of_globes (T := X.tuples) (U := R.tuples)
          (Functor.whiskerLeft C.toTheoryData.arity.op η) q hη p.arity (p.height.trans hn)
      obtain ⟨x, rfl⟩ := ht.2 x
      have hηz := ConcreteCategory.congr_hom
        (η.naturality (show (⟨Shape.globe (p.n+1)⟩ : C.Obj) ⟶ ⟨p.arity⟩ from z).op) x
      have hfz := ConcreteCategory.congr_hom
        (f.naturality (show (⟨Shape.globe (p.n+1)⟩ : C.Obj) ⟶ ⟨p.arity⟩ from z).op) x
      have fac (S : Shape) (x : X.presheaf.obj (op (⟨S⟩ : C.Obj))) :
          g.app (op S) (η.app (op ⟨S⟩) x) = f.app (op ⟨S⟩) x :=
        ConcreteCategory.congr_hom (congrArg (fun k : X.tuples.presheaf ⟶ Y.tuples.presheaf => k.app (op S)) hg) x
      exact (congrArg (g.app (op (Shape.globe (p.n+1)))) hηz.symm).trans
        ((fac (Shape.globe (p.n+1)) (X.eval z x)).trans
          (hfz.trans (congrArg (Y.eval z) (fac p.arity x).symm)))
    · apply (hY (p.n+1) (by omega)).1
      apply Subtype.ext
      apply Prod.ext
      · have gs := ConcreteCategory.congr_hom
          (g.naturality (Shape.source p.n).op) (R.eval z x)
        have hs : C.comp (C.base (Shape.source p.n)) z = p.source.1 := hz.1
        have wr := (R.eval_comp (C.base (Shape.source p.n)) z x).symm.trans
          (congrArg (fun u => R.eval u x) hs)
        have wy := (Y.eval_comp (C.base (Shape.source p.n)) z (g.app (op p.arity) x)).symm.trans
          (congrArg (fun u => Y.eval u (g.app (op p.arity) x)) hs)
        exact gs.symm.trans ((congrArg (g.app (op (Shape.globe p.n))) wr).trans
          ((p.source.2 x).trans wy.symm))
      · have gt := ConcreteCategory.congr_hom
          (g.naturality (Shape.target p.n).op) (R.eval z x)
        have ht : C.comp (C.base (Shape.target p.n)) z = p.target.1 := hz.2
        have wr := (R.eval_comp (C.base (Shape.target p.n)) z x).symm.trans
          (congrArg (fun u => R.eval u x) ht)
        have wy := (Y.eval_comp (C.base (Shape.target p.n)) z (g.app (op p.arity) x)).symm.trans
          (congrArg (fun u => Y.eval u (g.app (op p.arity) x)) ht)
        exact gt.symm.trans ((congrArg (g.app (op (Shape.globe p.n))) wr).trans
          ((p.target.2 x).trans wy.symm))
  refine ⟨⟨z, hnat⟩, ?_, rfl⟩
  exact ⟨Subtype.ext hz.1, Subtype.ext hz.2⟩


theorem existsUnique_factor_coskeletal {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    {X R Y : C.Model} (η : X ⟶ R) (f : X ⟶ Y) (q : ℕ)
    (hη : ∀ k, k ≤ q → Function.Bijective ((underlyingMap η).app k))
    (hY : ∀ j, q < j → Function.Bijective (Y.underlying.boundary j)) :
    ∃! l : R ⟶ Y, η ≫ l = f := by
  obtain ⟨g₀, hg₀, hgUnique⟩ := GlobularSet.existsUnique_factor_low_bijective
    (underlyingMap η) (underlyingMap f) q hη hY
  let g : R.tuples.presheaf ⟶ Y.tuples.presheaf := TupleSystem.mapFromUnderlying (T := R.tuples) (U := Y.tuples) g₀
  have hg : (Functor.whiskerLeft C.toTheoryData.arity.op η) ≫ g =
      Functor.whiskerLeft C.toTheoryData.arity.op f := by
    apply TupleSystem.hom_ext_globes (T := X.tuples) (U := Y.tuples)
    intro n
    apply ConcreteCategory.hom_ext
    intro x
    change (TupleSystem.mapFromUnderlying (T := R.tuples) (U := Y.tuples) g₀).app (op (Shape.globe n))
      ((underlyingMap η).app n x) = (underlyingMap f).app n x
    exact (TupleSystem.mapFromUnderlying_globe (T := R.tuples) (U := Y.tuples) g₀ n _).trans
      (congrArg (fun h : GlobularSet.Hom X.underlying Y.underlying => h.app n x) hg₀)
  obtain ⟨a, ha⟩ := hC.1.some.lift (compatibleProjection g)
    (compatibleProjection_liftsFillers η f g q hη hY hg) (Morphism.id C)
  have hav {S T : Shape} (u : C.Hom S T) : (a.map u).1 = u :=
    congrArg (fun k : Morphism C C => k.map u) ha
  let l : R ⟶ Y :=
    { app S := g.app (op S.unop.shape)
      naturality S T u := by
        apply ConcreteCategory.hom_ext
        intro x
        have w := (a.map u.unop).2 x
        exact (congrArg (g.app (op T.unop.shape))
          (congrArg (fun z => R.eval z x) (hav u.unop)).symm).trans
          (w.trans (congrArg (fun z => Y.eval z (g.app (op S.unop.shape) x)) (hav u.unop))) }
  have hl : η ≫ l = f := by
    apply NatTrans.ext
    funext S
    exact congrArg (fun k => k.app (op S.unop.shape)) hg
  have hlg : underlyingMap l = g₀ := by
    ext n x
    exact TupleSystem.mapFromUnderlying_globe (T := R.tuples) (U := Y.tuples) g₀ n x
  refine ⟨l, hl, ?_⟩
  intro l' hl'
  apply underlyingMap_injective
  apply Eq.trans _ hlg.symm
  apply hgUnique
  exact congrArg (fun k : X ⟶ Y => underlyingMap k) hl'

def IsCoskeletal {C : GlobularTheory.{v}} (X : C.Model) (q : ℕ) : Prop :=
  ∀ j, q < j → Function.Bijective (X.underlying.boundary j)

theorem exists_cutoff_reflection {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (X : C.Model) (q : ℕ) :
    ∃ (R : C.Model) (η : X ⟶ R),
      (∀ n, n ≤ q → Function.Bijective ((underlyingMap η).app n)) ∧
      R.IsCoskeletal q ∧
      ∀ (Y : C.Model), Y.IsCoskeletal q → ∀ f : X ⟶ Y, ∃! l : R ⟶ Y, η ≫ l = f := by
  obtain ⟨R, η, hlo, hhi⟩ := exists_cutoff hC X q
  exact ⟨R, η, hlo, hhi, fun _ hY f => existsUnique_factor_coskeletal hC η f q hlo hY⟩


def CoskeletalLocalMap {C : GlobularTheory.{v}} (q : ℕ) {X Y : C.Model}
    (i : X ⟶ Y) : Prop :=
  ∀ (Z : C.Model), Z.IsCoskeletal q → ∀ g : X ⟶ Z, ∃! h : Y ⟶ Z, i ≫ h = g

theorem coskeletalLocalMap_iff {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q : ℕ) {X Y : C.Model} (i : X ⟶ Y) :
    CoskeletalLocalMap q i ↔
      ∀ k, k ≤ q → Function.Bijective ((underlyingMap i).app k) := by
  constructor
  · intro hi
    obtain ⟨RX, ηX, hX, hRX, uX⟩ := exists_cutoff_reflection hC X q
    obtain ⟨RY, ηY, hY, hRY, _⟩ := exists_cutoff_reflection hC Y q
    obtain ⟨g, hg, _⟩ := hi RX hRX ηX
    obtain ⟨a, ha, _⟩ := uX RY hRY (i ≫ ηY)
    obtain ⟨_, _, unique⟩ := hi RY hRY (i ≫ ηY)
    have hy : g ≫ a = ηY := (unique (g ≫ a)
      ((Category.assoc i g a).symm.trans ((congrArg (· ≫ a) hg).trans ha))).trans
      (unique ηY rfl).symm
    intro k hk
    constructor
    · intro x y h
      apply (hX k hk).1
      have fac := congrArg (fun f : X ⟶ RX => (underlyingMap f).app k) hg
      exact (congrFun fac x).symm.trans ((congrArg ((underlyingMap g).app k) h).trans
        (congrFun fac y))
    · intro y
      obtain ⟨x, hx⟩ := (hX k hk).2 ((underlyingMap g).app k y)
      refine ⟨x, (hY k hk).1 ?_⟩
      have fac := congrArg (fun f : X ⟶ RY => (underlyingMap f).app k x) ha
      have fac' := congrArg (fun f : Y ⟶ RY => (underlyingMap f).app k y) hy
      exact fac.symm.trans ((congrArg ((underlyingMap a).app k) hx).trans fac')
  · intro hi Z hZ g
    exact existsUnique_factor_coskeletal hC i g q hi hZ

theorem BoundaryAttachment.coskeletalLocalMap {C : GlobularTheory.{v}}
    {X Y : C.Model} {i : X ⟶ Y} (A : BoundaryAttachment i) (q : ℕ)
    (hA : ∀ k, q < A.dimension k) : CoskeletalLocalMap q i := by
  intro Z hZ g
  have cells : ∀ k, ∃! z, Z.underlying.boundary (A.dimension k) z =
      (underlyingMap g).boundaryMap _ (A.boundary k) := by
    intro k
    exact (hZ (A.dimension k) (hA k)).existsUnique _
  choose z hz uniqueCell using cells
  obtain ⟨h, hh, unique⟩ := A.universal Z g z hz
  refine ⟨h, hh.1, ?_⟩
  intro h' hh'
  apply unique h'
  refine ⟨hh', ?_⟩
  intro k
  apply uniqueCell
  rw [← (underlyingMap h').boundary_app, A.cell_boundary]
  simpa only [underlyingMap_comp, GlobularSet.Hom.boundaryMap_comp] using
    congrArg (fun f : X ⟶ Z => (underlyingMap f).boundaryMap _ (A.boundary k)) hh'

theorem BoundaryAttachment.low_bijective {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    {X Y : C.Model} {i : X ⟶ Y} (A : BoundaryAttachment i) (q : ℕ)
    (hA : ∀ k, q < A.dimension k) (j : ℕ) (hj : j ≤ q) :
    Function.Bijective ((underlyingMap i).app j) :=
  (coskeletalLocalMap_iff hC q i).1 (A.coskeletalLocalMap q hA) j hj

end GlobularTheory.Model

end Grothendieck

end OAI
