import OAI.CategoryTheory.Globular.Basic

namespace OAI

universe u v w

namespace Grothendieck

open CategoryTheory CategoryTheory.Limits Opposite

namespace GlobularSet

theorem Parallel.symm {X : GlobularSet.{u}} {n} {x y : X.Cell n}
    (h : X.Parallel n x y) : X.Parallel n y x := by
  cases n with
  | zero => trivial
  | succ n => exact ⟨h.1.symm, h.2.symm⟩

theorem outer_parallel {X : GlobularSet.{u}} {n} {f g : X.Cell (n + 1)}
    (h : X.target n f = X.source n g) :
    X.Parallel n (X.source n f) (X.target n g) := by
  cases n with
  | zero => trivial
  | succ n =>
    exact ⟨(X.source_source n f).trans ((congrArg (X.source n) h).trans
      (X.source_source n g)),
      (X.target_source n f).trans ((congrArg (X.target n) h).trans
      (X.target_source n g))⟩

def LiftsBoundaries {X Y : GlobularSet.{u}} (f : Hom X Y) : Prop :=
  ∀ (n) (b : X.Boundary n) (y : Y.Cell n), Y.boundary n y = f.boundaryMap n b →
    ∃ x : X.Cell n, X.boundary n x = b ∧ f.app n x = y

theorem exactBoundaryTest_endpoint_section {P X : GlobularSet.{u}}
    (p₀ p₁ : Hom P X) (h : Hom X P)
    (h₀ : LiftsBoundaries p₀) (h₁ : LiftsBoundaries p₁)
    (s : ∀ n x, p₀.app n (h.app n x) = x)
    (units : ∀ n x, X.Joined n x x) : ExactBoundaryTest (h.comp p₁) := by
  intro n b y hy
  obtain ⟨z, hz, hzy⟩ := h₁ n (h.boundaryMap n b) y
    (by simpa only [Hom.boundaryMap_comp] using hy)
  let x := p₀.app n z
  have hb : X.boundary n x = b := by
    rw [← p₀.boundary_app, hz]
    cases n with
    | zero => rfl
    | succ n => exact Subtype.ext (Prod.ext (s n _) (s n _))
  have hp : P.Parallel n (h.app n x) z := by
    rw [parallel_iff_boundary_eq, ← h.boundary_app, hb, hz]
  obtain ⟨e, es, et⟩ := units n x
  have he : X.boundary (n + 1) e =
      p₀.boundaryMap (n + 1) (⟨(h.app n x, z), hp⟩ : P.Boundary (n + 1)) := by
    apply Subtype.ext
    exact Prod.ext (es.trans (s n x).symm) et
  obtain ⟨c, hc, _⟩ := h₀ (n + 1) ⟨(h.app n x, z), hp⟩ e he
  have hc' := congrArg Subtype.val hc
  refine ⟨x, hb, ?_⟩
  have joined : P.Joined n (h.app n x) z :=
    ⟨c, congrArg Prod.fst hc', congrArg Prod.snd hc'⟩
  simpa only [Hom.comp_app, hzy] using p₁.map_joined joined

end GlobularSet

namespace Shape

theorem source_source (n : ℕ) :
    source n ≫ source (n + 1) = source n ≫ target (n + 1) := by
  have h := congrArg (fun f => GlobularTheory.shapeGlobes.map f) (Globe.source_source n)
  exact (GlobularTheory.shapeGlobes.map_comp _ _).symm.trans
    (h.trans (GlobularTheory.shapeGlobes.map_comp _ _))

theorem target_source (n : ℕ) :
    target n ≫ source (n + 1) = target n ≫ target (n + 1) := by
  have h := congrArg (fun f => GlobularTheory.shapeGlobes.map f) (Globe.target_source n)
  exact (GlobularTheory.shapeGlobes.map_comp _ _).symm.trans
    (h.trans (GlobularTheory.shapeGlobes.map_comp _ _))

theorem seam_inl (S : Shape) (b h : ℕ) (hl : b < S.1) (hr : b < h) :
    S.seam hl ≫ S.inl b h hl hr = face hr false ≫ S.inr b h hl hr := by
  have eq := pushout.condition (f := GlobularPresheaf.face hl true ≫ S.2.lastInclusion)
    (g := GlobularPresheaf.face hr false)
  exact eq

@[simp]
theorem globe_seam (n : ℕ) : (globe (n + 1)).seam (Nat.lt_succ_self n) = target n := by
  exact Category.comp_id (GlobularPresheaf.face (Nat.lt_succ_self n) true)

end Shape

namespace GlobularTheory

noncomputable def inversePair (C : GlobularTheory.{v}) (n : ℕ) : C.AdmissiblePair where
  n := n
  arity := Shape.globe (n + 1)
  height := le_rfl
  source := C.base (Shape.target n)
  target := C.base (Shape.source n)
  parallel := by
    cases n with
    | zero => trivial
    | succ n =>
      constructor
      · rw [← C.base_comp, ← C.base_comp]
        exact congrArg C.base (Shape.source_source n).symm
      · rw [← C.base_comp, ← C.base_comp]
        exact congrArg C.base (Shape.target_source n).symm

namespace Model

theorem joined_refl {C : GlobularTheory.{v}} (X : C.Model) (hC : C.IsCoherator)
    (n : ℕ) (x : X.underlying.Cell n) : X.underlying.Joined n x x :=
  ⟨X.unitCell hC n x, X.unitCell_source hC n x, X.unitCell_target hC n x⟩

theorem joined_symm {C : GlobularTheory.{v}} (X : C.Model) (hC : C.IsCoherator)
    {n : ℕ} {x y : X.underlying.Cell n} (h : X.underlying.Joined n x y) :
    X.underlying.Joined n y x := by
  obtain ⟨z, rfl, rfl⟩ := h
  obtain ⟨w, hs, ht⟩ := hC.2 (C.inversePair n)
  change C.Hom (Shape.globe (n + 1)) (Shape.globe (n + 1)) at w
  change C.comp (C.base (Shape.source n)) w = C.base (Shape.target n) at hs
  change C.comp (C.base (Shape.target n)) w = C.base (Shape.source n) at ht
  refine ⟨X.eval w z, ?_, ?_⟩
  · change X.presheaf.obj (op (⟨Shape.globe (n + 1)⟩ : C.Obj)) at z
    change X.eval (C.base (Shape.source n)) (X.eval w z) =
      X.eval (C.base (Shape.target n)) z
    rw [← eval_comp, hs]
  · change X.presheaf.obj (op (⟨Shape.globe (n + 1)⟩ : C.Obj)) at z
    change X.eval (C.base (Shape.target n)) (X.eval w z) =
      X.eval (C.base (Shape.source n)) z
    rw [← eval_comp, ht]

end Model

def compositionShape (n : ℕ) : Shape :=
  (Shape.globe (n + 1)).attach n (n + 1) (Nat.lt_succ_self n) (Nat.lt_succ_self n)

noncomputable def compositionLeft (n : ℕ) : Shape.globe (n + 1) ⟶ compositionShape n :=
  (Shape.globe (n + 1)).inl n (n + 1) (Nat.lt_succ_self n) (Nat.lt_succ_self n)

noncomputable def compositionRight (n : ℕ) : Shape.globe (n + 1) ⟶ compositionShape n :=
  (Shape.globe (n + 1)).inr n (n + 1) (Nat.lt_succ_self n) (Nat.lt_succ_self n)

theorem composition_seam (n : ℕ) :
    Shape.target n ≫ compositionLeft n = Shape.source n ≫ compositionRight n := by
  simpa only [Shape.globe_seam, Shape.source, compositionLeft, compositionRight,
    compositionShape] using Shape.seam_inl (Shape.globe (n + 1)) n
    (n + 1) (Nat.lt_succ_self n) (Nat.lt_succ_self n)

noncomputable def compositionPair (C : GlobularTheory.{v}) (n : ℕ) : C.AdmissiblePair where
  n := n
  arity := compositionShape n
  height := Nat.max_self (n + 1) ▸ le_rfl
  source := C.base (Shape.source n ≫ compositionLeft n)
  target := C.base (Shape.target n ≫ compositionRight n)
  parallel := by
    cases n with
    | zero => trivial
    | succ n =>
      constructor
      · rw [← C.base_comp, ← C.base_comp]
        apply congrArg C.base
        calc
          _ = (Shape.source n ≫ Shape.target (n+1)) ≫ compositionLeft (n+1) := by
            rw [← Category.assoc, Shape.source_source]
          _ = Shape.source n ≫ (Shape.source (n+1) ≫ compositionRight (n+1)) := by
            rw [Category.assoc, composition_seam]
          _ = _ := by rw [← Category.assoc, Shape.source_source, Category.assoc]
      · rw [← C.base_comp, ← C.base_comp]
        apply congrArg C.base
        calc
          _ = (Shape.target n ≫ Shape.target (n+1)) ≫ compositionLeft (n+1) := by
            rw [← Category.assoc, Shape.target_source]
          _ = Shape.target n ≫ (Shape.source (n+1) ≫ compositionRight (n+1)) := by
            rw [Category.assoc, composition_seam]
          _ = _ := by rw [← Category.assoc, Shape.target_source, Category.assoc]

namespace Model

theorem joined_trans {C : GlobularTheory.{v}} (X : C.Model) (hC : C.IsCoherator)
    {n : ℕ} {x y z : X.underlying.Cell n}
    (h : X.underlying.Joined n x y) (k : X.underlying.Joined n y z) :
    X.underlying.Joined n x z := by
  obtain ⟨a, ha, ha'⟩ := h
  obtain ⟨b, hb, hb'⟩ := k
  have hab : X.eval (C.base ((Shape.globe (n+1)).seam (Nat.lt_succ_self n))) a =
      X.eval (C.base (Shape.face (Nat.lt_succ_self n) false)) b := by
    rw [Shape.globe_seam]
    exact ha'.trans hb.symm
  obtain ⟨t, htl, htr⟩ := Types.exists_of_isPullback
    (X.sums (Shape.globe (n+1)) n (n+1) (Nat.lt_succ_self n) (Nat.lt_succ_self n)) a b hab
  change X.presheaf.obj (op (⟨compositionShape n⟩ : C.Obj)) at t
  change X.eval (C.base (compositionLeft n)) t = a at htl
  change X.eval (C.base (compositionRight n)) t = b at htr
  obtain ⟨w, hs, ht⟩ := hC.2 (C.compositionPair n)
  change C.Hom (Shape.globe (n+1)) (compositionShape n) at w
  change C.comp (C.base (Shape.source n)) w = C.base (Shape.source n ≫ compositionLeft n) at hs
  change C.comp (C.base (Shape.target n)) w = C.base (Shape.target n ≫ compositionRight n) at ht
  refine ⟨X.eval w t, ?_, ?_⟩
  · change X.eval (C.base (Shape.source n)) (X.eval w t) = x
    rw [← eval_comp, hs, C.base_comp, eval_comp, htl]
    exact ha
  · change X.eval (C.base (Shape.target n)) (X.eval w t) = z
    rw [← eval_comp, ht, C.base_comp, eval_comp, htr]
    exact hb'

theorem joined_equivalence {C : GlobularTheory.{v}} (X : C.Model) (hC : C.IsCoherator)
    (n : ℕ) : Equivalence (X.underlying.Joined n) :=
  ⟨X.joined_refl hC n, X.joined_symm hC, X.joined_trans hC⟩

end Model
namespace Morphism

@[simp] theorem id_comp {C D : GlobularTheory.{v}} (f : Morphism C D) :
    (id C).comp f = f := by ext; rfl

@[simp] theorem comp_id {C D : GlobularTheory.{v}} (f : Morphism C D) :
    f.comp (id D) = f := by ext; rfl

theorem comp_assoc {B C D E : GlobularTheory.{v}}
    (f : Morphism B C) (g : Morphism C D) (h : Morphism D E) :
    (f.comp g).comp h = f.comp (g.comp h) := by ext; rfl

def mapPair {C D : GlobularTheory.{v}} (f : Morphism C D) (p : C.AdmissiblePair) :
    D.AdmissiblePair where
  n := p.n
  arity := p.arity
  height := p.height
  source := f.map p.source
  target := f.map p.target
  parallel := by
    cases p with
    | mk n S hd s t hp =>
      cases n with
      | zero => trivial
      | succ n =>
        change _ = _ ∧ _ = _
        change _ = _ ∧ _ = _ at hp
        constructor
        · rw [← f.map_base, ← f.map_comp, ← f.map_comp, hp.1]
        · rw [← f.map_base, ← f.map_comp, ← f.map_comp, hp.2]

end Morphism

theorem Fills.map {C D E : GlobularTheory.{v}} {a : Morphism C D}
    {p : C.AdmissiblePair} {z : D.Hom (Shape.globe (p.n + 1)) p.arity}
    (hz : Fills a p z) (b : Morphism D E) : Fills (a.comp b) p (b.map z) := by
  constructor
  · change E.comp (E.base _) (b.map z) = b.map (a.map p.source)
    rw [← b.map_base, ← b.map_comp, hz.1]
  · change E.comp (E.base _) (b.map z) = b.map (a.map p.target)
    rw [← b.map_base, ← b.map_comp, hz.2]

theorem IsFreeExtension.hom_ext {C D : GlobularTheory.{v}} {f : Morphism C D}
    {G : Type v} {pair : G → C.AdmissiblePair}
    {filler : ∀ g, D.Hom (Shape.globe ((pair g).n + 1)) (pair g).arity}
    (hf : IsFreeExtension f G pair filler) {E : GlobularTheory.{v}}
    (a b : Morphism D E) (h : f.comp a = f.comp b)
    (hg : ∀ g, a.map (filler g) = b.map (filler g)) : a = b := by
  obtain ⟨c, _, hc⟩ := hf.2 E (f.comp a) (fun g => a.map (filler g))
    (fun g => (hf.1 g).map a)
  exact (hc a ⟨rfl, fun _ => rfl⟩).trans
    (hc b ⟨h.symm, fun g => (hg g).symm⟩).symm

def LiftsFillers {E D : GlobularTheory.{v}} (p : Morphism E D) : Prop :=
  ∀ (a : E.AdmissiblePair) (z : D.Hom (Shape.globe (a.n + 1)) a.arity),
    Fills p a z → ∃ w, Fills (Morphism.id E) a w ∧ p.map w = z

namespace CellularPresentation

theorem hom_ext {C : GlobularTheory.{v}} (P : C.CellularPresentation)
    {D : GlobularTheory.{v}} (a b : Morphism C D)
    (h : ∀ r, (P.inclusion r).comp a = (P.inclusion r).comp b) : a = b := by
  obtain ⟨c, _, hc⟩ := P.colimit D (fun r => (P.inclusion r).comp a)
    (fun r => by rw [← Morphism.comp_assoc, P.compatible])
  exact (hc a (fun _ => rfl)).trans (hc b (fun r => (h r).symm)).symm

theorem lift {C E D : GlobularTheory.{v}} (P : C.CellularPresentation)
    (p : Morphism E D) (hp : LiftsFillers p) (f : Morphism C D) :
    ∃ a : Morphism C E, a.comp p = f := by
  classical
  let StageLift (r : ℕ) :=
    { a : Morphism (P.stage r) E // a.comp p = (P.inclusion r).comp f }
  have initial : Nonempty (StageLift 0) := by
    let : Unique (Morphism (P.stage 0) E) := (P.initial E).some
    let : Unique (Morphism (P.stage 0) D) := (P.initial D).some
    exact ⟨⟨default, Subsingleton.elim _ _⟩⟩
  have next (r : ℕ) (a : StageLift r) :
      ∃ b : StageLift (r + 1), (P.step r).comp b.1 = a.1 := by
    let z (g : P.generators r) := f.map ((P.inclusion (r+1)).map (P.filler r g))
    have hz (g : P.generators r) : Fills (a.1.comp p) (P.pair r g) (z g) := by
      have h := ((P.free r).1 g).map ((P.inclusion (r+1)).comp f)
      rw [a.2, ← Morphism.comp_assoc, P.compatible] at *
      exact h
    have hw (g : P.generators r) :
        ∃ w, Fills a.1 (P.pair r g) w ∧ p.map w = z g := by
      obtain ⟨w, hw, he⟩ := hp (a.1.mapPair (P.pair r g)) (z g) (hz g)
      exact ⟨w, hw, he⟩
    choose w hw he using hw
    obtain ⟨b, ⟨hb, hbg⟩, _⟩ := (P.free r).2 E a.1 w hw
    have hbp : b.comp p = (P.inclusion (r+1)).comp f := by
      apply (P.free r).hom_ext
      · rw [← Morphism.comp_assoc, hb, a.2, ← Morphism.comp_assoc, P.compatible]
      · intro g
        change p.map (b.map (P.filler r g)) = z g
        rw [hbg, he]
    exact ⟨⟨b, hbp⟩, hb⟩
  let a : (r : ℕ) → StageLift r := fun r => Nat.rec initial.some
    (fun r a => (next r a).choose) r
  have ha (r : ℕ) : (P.step r).comp (a (r+1)).1 = (a r).1 :=
    (next r (a r)).choose_spec
  obtain ⟨b, hb, _⟩ := P.colimit E (fun r => (a r).1) ha
  refine ⟨b, P.hom_ext _ _ (fun r => ?_)⟩
  rw [← Morphism.comp_assoc, hb, (a r).2]

end CellularPresentation
end GlobularTheory

structure TupleSystem where
  presheaf : Shapeᵒᵖ ⥤ Type v
  sums : ∀ (S : Shape) (b h : ℕ) (hl : b < S.1) (hr : b < h),
    IsPullback
      (presheaf.map (S.inl b h hl hr).op)
      (presheaf.map (S.inr b h hl hr).op)
      (presheaf.map (S.seam hl).op)
      (presheaf.map (Shape.face hr false).op)

namespace TupleSystem

noncomputable def endData (T : TupleSystem.{v}) : TheoryData.{v} where
  Hom S R := T.presheaf.obj (op R) ⟶ T.presheaf.obj (op S)
  id _ := 𝟙 _
  comp f g := g ≫ f
  id_comp f := Category.comp_id f
  comp_id f := Category.id_comp f
  assoc f g h := (Category.assoc h g f).symm
  base f := T.presheaf.map f.op
  base_id S := T.presheaf.map_id (op S)
  base_comp f g := T.presheaf.map_comp g.op f.op

noncomputable def endEmbedding (T : TupleSystem.{v}) : T.endData.Obj ⥤ (Type v)ᵒᵖ where
  obj S := op (T.presheaf.obj (op S.shape))
  map f := f.op
  map_id _ := rfl
  map_comp _ _ := rfl

noncomputable def endEmbedding_fullyFaithful (T : TupleSystem.{v}) :
    T.endEmbedding.FullyFaithful where
  preimage f := f.unop

noncomputable def endTheory (T : TupleSystem.{v}) : GlobularTheory.{v} where
  toTheoryData := T.endData
  sums S b h hl hr := by
    let : T.endEmbedding.Full := T.endEmbedding_fullyFaithful.full
    let : T.endEmbedding.Faithful := T.endEmbedding_fullyFaithful.faithful
    apply IsPushout.of_map_of_faithful T.endEmbedding
    exact (T.sums S b h hl hr).op.flip

noncomputable def model {C : GlobularTheory.{v}} (T : TupleSystem.{v})
    (a : GlobularTheory.Morphism C T.endTheory) : C.Model where
  presheaf :=
    { obj := fun S => T.presheaf.obj (op S.unop.shape)
      map := fun f => a.map f.unop
      map_id := fun S => a.map_id S.unop.shape
      map_comp := fun f g => a.map_comp g.unop f.unop }
  sums S b h hl hr := by
    change IsPullback (a.map (C.base (S.inl b h hl hr)))
      (a.map (C.base (S.inr b h hl hr))) (a.map (C.base (S.seam hl)))
      (a.map (C.base (Shape.face hr false)))
    rw [a.map_base, a.map_base, a.map_base, a.map_base]
    exact T.sums S b h hl hr

end TupleSystem

namespace GlobularTheory.Model

noncomputable abbrev tuples {C : GlobularTheory.{v}} (X : C.Model) : TupleSystem.{v} where
  presheaf := C.toTheoryData.arity.op ⋙ X.presheaf
  sums := X.sums

noncomputable def interpretation {C : GlobularTheory.{v}} (X : C.Model) :
    Morphism C X.tuples.endTheory where
  map f := X.presheaf.map (show (⟨_⟩ : C.Obj) ⟶ ⟨_⟩ from f).op
  map_id S := X.presheaf.map_id (op (⟨S⟩ : C.Obj))
  map_comp f g := X.presheaf.map_comp (show (op (⟨_⟩ : C.Obj)) ⟶ op ⟨_⟩ from Quiver.Hom.op (show (⟨_⟩ : C.Obj) ⟶ ⟨_⟩ from g))
    (show (op (⟨_⟩ : C.Obj)) ⟶ op ⟨_⟩ from
      Quiver.Hom.op (show (⟨_⟩ : C.Obj) ⟶ ⟨_⟩ from f))
  map_base _ := rfl

end GlobularTheory.Model

end Grothendieck

end OAI
