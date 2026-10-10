import OAI.CategoryTheory.Globular.Cutoff

namespace OAI

universe u v w

namespace Grothendieck

open CategoryTheory CategoryTheory.Limits Opposite

namespace Shape

noncomputable def realization : Shape ⥤ GlobularPresheaf.{0} where
  obj := realize
  map f := f

noncomputable def liftedRealization : Shape ⥤ GlobularPresheaf.{v} :=
  realization ⋙ (Functor.whiskeringRight Globeᵒᵖ (Type) (Type v)).obj uliftFunctor.{v,0}

theorem realization_pushout (S : Shape) (b h : ℕ) (hl : b < S.1) (hr : b < h) :
    IsPushout (realization.map (S.seam hl)) (realization.map (face hr false))
      (realization.map (S.inl b h hl hr)) (realization.map (S.inr b h hl hr)) :=
  IsPushout.of_hasPushout _ _

theorem liftedRealization_pushout (S : Shape) (b h : ℕ) (hl : b < S.1) (hr : b < h) :
    IsPushout (liftedRealization.{v}.map (S.seam hl))
      (liftedRealization.{v}.map (face hr false))
      (liftedRealization.{v}.map (S.inl b h hl hr))
      (liftedRealization.{v}.map (S.inr b h hl hr)) :=
  (realization_pushout S b h hl hr).map
    ((Functor.whiskeringRight Globeᵒᵖ (Type) (Type v)).obj uliftFunctor.{v,0})

end Shape

namespace GlobularPresheaf

noncomputable def tuples (X : GlobularPresheaf.{v}) : TupleSystem.{v} where
  presheaf := Shape.liftedRealization.op ⋙ yoneda.obj X
  sums S b h hl hr :=
    ((Shape.liftedRealization_pushout S b h hl hr).op.flip).map (yoneda.obj X)

end GlobularPresheaf

namespace TupleSystem

noncomputable def relativeData {T U : TupleSystem.{v}} (f : T.presheaf ⟶ U.presheaf) :
    TheoryData.{v} where
  Hom S R := Arrow.mk (f.app (op R)) ⟶ Arrow.mk (f.app (op S))
  id _ := 𝟙 _
  comp a b := b ≫ a
  id_comp a := Category.comp_id a
  comp_id a := Category.id_comp a
  assoc a b c := (Category.assoc c b a).symm
  base a := Arrow.homMk (T.presheaf.map a.op) (U.presheaf.map a.op) (f.naturality a.op)
  base_id S := by apply Arrow.hom_ext <;> exact CategoryTheory.Functor.map_id _ _
  base_comp a b := by apply Arrow.hom_ext <;> exact CategoryTheory.Functor.map_comp _ b.op a.op

noncomputable def relativeEmbedding {T U : TupleSystem.{v}}
    (f : T.presheaf ⟶ U.presheaf) : (relativeData f).Obj ⥤ (Arrow (Type v))ᵒᵖ where
  obj S := op (Arrow.mk (f.app (op S.shape)))
  map a := a.op

noncomputable def relativeEmbedding_fullyFaithful {T U : TupleSystem.{v}}
    (f : T.presheaf ⟶ U.presheaf) : (relativeEmbedding f).FullyFaithful where
  preimage a := a.unop

private theorem arrow_isPullback {P X Y Z : Arrow (Type v)}
    {a : P ⟶ X} {b : P ⟶ Y} {c : X ⟶ Z} {d : Y ⟶ Z}
    (hl : IsPullback a.left b.left c.left d.left)
    (hr : IsPullback a.right b.right c.right d.right) : IsPullback a b c d where
  w := Arrow.hom_ext _ _ hl.w hr.w
  isLimit' := ⟨Comma.fstSndJointlyReflectLimit
    ((PullbackCone.isLimitMapConeEquiv _ _).symm hl.isLimit)
    ((PullbackCone.isLimitMapConeEquiv _ _).symm hr.isLimit)⟩

noncomputable def relativeTheory {T U : TupleSystem.{v}}
    (f : T.presheaf ⟶ U.presheaf) : GlobularTheory.{v} where
  toTheoryData := relativeData f
  sums S b h hl hr := by
    let : (relativeEmbedding f).Full := (relativeEmbedding_fullyFaithful f).full
    let : (relativeEmbedding f).Faithful := (relativeEmbedding_fullyFaithful f).faithful
    apply IsPushout.of_map_of_faithful (relativeEmbedding f)
    exact (arrow_isPullback (T.sums S b h hl hr) (U.sums S b h hl hr)).op.flip

noncomputable def relativeSource {T U : TupleSystem.{v}}
    (f : T.presheaf ⟶ U.presheaf) : GlobularTheory.Morphism (relativeTheory f) T.endTheory where
  map a := a.left
  map_id _ := rfl
  map_comp _ _ := rfl
  map_base _ := rfl

noncomputable def relativeTarget {T U : TupleSystem.{v}}
    (f : T.presheaf ⟶ U.presheaf) : GlobularTheory.Morphism (relativeTheory f) U.endTheory where
  map a := a.right
  map_id _ := rfl
  map_comp _ _ := rfl
  map_base _ := rfl

noncomputable def relativeModelMap {C : GlobularTheory.{v}} {T U : TupleSystem.{v}}
    (f : T.presheaf ⟶ U.presheaf) (a : GlobularTheory.Morphism C (relativeTheory f)) :
    T.model (a.comp (relativeSource f)) ⟶ U.model (a.comp (relativeTarget f)) where
  app S := f.app (op S.unop.shape)
  naturality _ _ g := (a.map g.unop).w

end TupleSystem

namespace GlobularSet

theorem lift_operation {X Y : GlobularSet.{v}} (η : X.Hom Y)
    {A B : Type v} (f : A → B) (n : ℕ)
    (s t : A → X.Cell n) (s' t' : B → Y.Cell n)
    (hs : ∀ a, η.app n (s a) = s' (f a))
    (ht : ∀ a, η.app n (t a) = t' (f a))
    (hp : ∀ b, Y.Parallel n (s' b) (t' b))
    (z : A → X.Cell (n+1)) (hzs : ∀ a, X.source n (z a) = s a)
    (hzt : ∀ a, X.target n (z a) = t a)
    (h : Function.Bijective f ∨ Function.Bijective (Y.boundary (n+1))) :
    ∃ z' : B → Y.Cell (n+1),
      (∀ b, Y.source n (z' b) = s' b) ∧
      (∀ b, Y.target n (z' b) = t' b) ∧
      (∀ a, η.app (n+1) (z a) = z' (f a)) := by
  classical
  rcases h with h | h
  · let e : A ≃ B := Equiv.ofBijective f h
    refine ⟨fun b => η.app (n+1) (z (e.symm b)), ?_, ?_, ?_⟩
    · intro b
      rw [← η.source_app, hzs, hs]
      exact congrArg s' (e.apply_symm_apply b)
    · intro b
      rw [← η.target_app, hzt, ht]
      exact congrArg t' (e.apply_symm_apply b)
    · intro a
      exact congrArg (fun a => η.app (n+1) (z a)) (e.symm_apply_apply a).symm
  · let e : Y.Cell (n+1) ≃ Y.Boundary (n+1) := Equiv.ofBijective _ h
    let b (x : B) : Y.Boundary (n+1) := ⟨(s' x, t' x), hp x⟩
    have hb (x : B) : Y.boundary (n+1) (e.symm (b x)) = b x := e.apply_symm_apply _
    refine ⟨fun x => e.symm (b x), ?_, ?_, ?_⟩
    · intro x
      exact congrArg (fun a => a.1.1) (hb x)
    · intro x
      exact congrArg (fun a => a.1.2) (hb x)
    · intro a
      apply h.1
      rw [hb, ← η.boundary_app]
      apply Subtype.ext
      change (η.app n (X.source n (z a)), η.app n (X.target n (z a))) =
        (s' (f a), t' (f a))
      rw [hzs, hs, hzt, ht]

end GlobularSet

namespace TupleSystem

noncomputable def underlying (T : TupleSystem.{v}) : GlobularSet.{v} :=
  GlobularPresheaf.underlying (GlobularTheory.shapeGlobes.op ⋙ T.presheaf)

noncomputable def underlyingMap {T U : TupleSystem.{v}} (f : T.presheaf ⟶ U.presheaf) :
    T.underlying.Hom U.underlying :=
  GlobularPresheaf.underlyingMap (Functor.whiskerLeft GlobularTheory.shapeGlobes.op f)

theorem parallel_eval (T : TupleSystem.{v}) {S : Shape} (n : ℕ)
    (s t : T.presheaf.obj (op S) ⟶ T.presheaf.obj (op (Shape.globe n)))
    (hp : T.endTheory.Parallel n s t)
    (x : T.presheaf.obj (op S)) : T.underlying.Parallel n (s x) (t x) := by
  cases n with
  | zero => trivial
  | succ n =>
    exact ⟨ConcreteCategory.congr_hom hp.1 x, ConcreteCategory.congr_hom hp.2 x⟩

theorem relativeSource_liftsFillers {T U : TupleSystem.{v}}
    (f : T.presheaf ⟶ U.presheaf) (q : ℕ)
    (hlow : ∀ S : Shape, S.height ≤ q → Function.Bijective (f.app (op S)))
    (hhigh : ∀ k, q < k → Function.Bijective (U.underlying.boundary k)) :
    GlobularTheory.LiftsFillers (relativeSource f) := by
  intro a z hz
  change T.presheaf.obj (op a.arity) ⟶ T.presheaf.obj (op (Shape.globe (a.n+1))) at z
  have hp := U.parallel_eval a.n a.source.right a.target.right
    ((relativeTarget f).mapPair a).parallel
  have choice : Function.Bijective (f.app (op a.arity)) ∨
      Function.Bijective (U.underlying.boundary (a.n+1)) := by
    by_cases h : a.n+1 ≤ q
    · exact Or.inl (hlow _ (a.height.trans h))
    · exact Or.inr (hhigh _ (Nat.lt_of_not_ge h))
  obtain ⟨z', hzs, hzt, hη⟩ := GlobularSet.lift_operation (underlyingMap f)
    (f.app (op a.arity)) a.n a.source.left a.target.left a.source.right a.target.right
    (fun x => ConcreteCategory.congr_hom a.source.w x)
    (fun x => ConcreteCategory.congr_hom a.target.w x) hp z
    (fun x => ConcreteCategory.congr_hom hz.1 x)
    (fun x => ConcreteCategory.congr_hom hz.2 x) choice
  let w : (relativeTheory f).Hom (Shape.globe (a.n+1)) a.arity :=
    Arrow.homMk z (TypeCat.ofHom z') (ConcreteCategory.hom_ext _ _ hη)
  refine ⟨w, ⟨?_, ?_⟩, rfl⟩
  · apply Arrow.hom_ext
    · exact hz.1
    · exact ConcreteCategory.hom_ext _ _ hzs
  · apply Arrow.hom_ext
    · exact hz.2
    · exact ConcreteCategory.hom_ext _ _ hzt


private theorem bijective_pullback_map
    {P A B R P' A' B' R' : Type v}
    (l : P ⟶ A) (r : P ⟶ B) (s : A ⟶ R) (t : B ⟶ R)
    (l' : P' ⟶ A') (r' : P' ⟶ B') (s' : A' ⟶ R') (t' : B' ⟶ R')
    (h : IsPullback l r s t) (h' : IsPullback l' r' s' t')
    (p : P ⟶ P') (a : A ⟶ A') (b : B ⟶ B') (c : R ⟶ R')
    (wl : l ≫ a = p ≫ l') (wr : r ≫ b = p ≫ r')
    (ws : s ≫ c = a ≫ s') (wt : t ≫ c = b ≫ t')
    (ha : Function.Bijective a) (hb : Function.Bijective b)
    (hc : Function.Injective c) : Function.Bijective p := by
  have hl (x : P) : a (l x) = l' (p x) := ConcreteCategory.congr_hom wl x
  have hr (x : P) : b (r x) = r' (p x) := ConcreteCategory.congr_hom wr x
  have hs (x : A) : c (s x) = s' (a x) := ConcreteCategory.congr_hom ws x
  have ht (x : B) : c (t x) = t' (b x) := ConcreteCategory.congr_hom wt x
  constructor
  · intro x y hp
    apply Types.ext_of_isPullback h
    · apply ha.1
      rw [hl, hl, hp]
    · apply hb.1
      rw [hr, hr, hp]
  · intro x
    obtain ⟨y, hy⟩ := ha.2 (l' x)
    obtain ⟨z, hz⟩ := hb.2 (r' x)
    have w : s y = t z := by
      apply hc
      rw [hs, ht, hy, hz]
      exact ConcreteCategory.congr_hom h'.w x
    obtain ⟨u, hu, hv⟩ := Types.exists_of_isPullback h y z w
    refine ⟨u, Types.ext_of_isPullback h' ?_ ?_⟩
    · rw [← hl, hu, hy]
    · rw [← hr, hv, hz]

theorem bijective_of_globes {T U : TupleSystem.{v}} (f : T.presheaf ⟶ U.presheaf)
    (q : ℕ) (hg : ∀ k, k ≤ q → Function.Bijective (f.app (op (Shape.globe k))))
    (S : Shape) (hS : S.height ≤ q) : Function.Bijective (f.app (op S)) := by
  cases S with
  | mk k table =>
    induction table with
    | globe k => exact hg k hS
    | @attach last tab b h hl hr ih =>
      have htab : (Shape.height ⟨last, tab⟩) ≤ q := (max_le_iff.mp hS).1
      have hh : h ≤ q := (max_le_iff.mp hS).2
      apply bijective_pullback_map
        (T.presheaf.map (Shape.inl ⟨last, tab⟩ b h hl hr).op)
        (T.presheaf.map (Shape.inr ⟨last, tab⟩ b h hl hr).op)
        (T.presheaf.map (Shape.seam ⟨last, tab⟩ hl).op)
        (T.presheaf.map (Shape.face hr false).op)
        (U.presheaf.map (Shape.inl ⟨last, tab⟩ b h hl hr).op)
        (U.presheaf.map (Shape.inr ⟨last, tab⟩ b h hl hr).op)
        (U.presheaf.map (Shape.seam ⟨last, tab⟩ hl).op)
        (U.presheaf.map (Shape.face hr false).op)
        (T.sums _ b h hl hr) (U.sums _ b h hl hr)
        _ (f.app (op ⟨last, tab⟩)) (f.app (op (Shape.globe h)))
        (f.app (op (Shape.globe b)))
      · exact f.naturality _
      · exact f.naturality _
      · exact f.naturality _
      · exact f.naturality _
      · exact ih htab
      · exact hg h hh
      · exact (hg b (Nat.le_trans (Nat.le_of_lt hr) hh)).1

end TupleSystem

end Grothendieck

end OAI
