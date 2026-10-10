import OAI.CategoryTheory.Globular.CutoffCells

namespace OAI

universe u v w

namespace Grothendieck

open CategoryTheory CategoryTheory.Limits Opposite

namespace GlobularSet

theorem Hom.reflects_parallel {X Y : GlobularSet.{u}} (f : Hom X Y)
    (hf : ∀ n, Function.Injective (f.app n)) {n : ℕ} {x y : X.Cell n}
    (h : Y.Parallel n (f.app n x) (f.app n y)) : X.Parallel n x y := by
  cases n with
  | zero => trivial
  | succ n =>
    exact ⟨hf n (by rw [f.source_app, f.source_app]; exact h.1),
      hf n (by rw [f.target_app, f.target_app]; exact h.2)⟩

theorem Hom.boundaryMap_bijective {X Y : GlobularSet.{u}} (f : Hom X Y)
    (hf : ∀ n, Function.Bijective (f.app n)) (n : ℕ) :
    Function.Bijective (f.boundaryMap n) := by
  cases n with
  | zero =>
    change Function.Bijective (fun _ : PUnit => (PUnit.unit : PUnit))
    exact ⟨fun _ _ _ => Subsingleton.elim _ _, fun _ => ⟨PUnit.unit, rfl⟩⟩
  | succ n =>
    constructor
    · intro x y h
      have hv := congrArg Subtype.val h
      exact Subtype.ext (Prod.ext ((hf n).1 (congrArg Prod.fst hv))
        ((hf n).1 (congrArg Prod.snd hv)))
    · intro b
      obtain ⟨x, hx⟩ := (hf n).2 b.1.1
      obtain ⟨y, hy⟩ := (hf n).2 b.1.2
      have hp : X.Parallel n x y := f.reflects_parallel (fun k => (hf k).1)
        (by rw [hx, hy]; exact b.2)
      exact ⟨⟨(x,y), hp⟩, Subtype.ext (Prod.ext hx hy)⟩

theorem Hom.boundary_bijective_iff {X Y : GlobularSet.{u}} (f : Hom X Y)
    (hf : ∀ n, Function.Bijective (f.app n)) (n : ℕ) :
    Function.Bijective (X.boundary n) ↔ Function.Bijective (Y.boundary n) := by
  have w : f.boundaryMap n ∘ X.boundary n = Y.boundary n ∘ f.app n := by
    funext x; exact f.boundary_app n x
  constructor
  · intro h
    have hb := (f.boundaryMap_bijective hf n).comp h
    rw [w] at hb
    exact (Function.Bijective.of_comp_iff _ (hf n)).mp hb
  · intro h
    have hb := h.comp (hf n)
    rw [← w] at hb
    constructor
    · exact fun _ _ hxy => hb.1 (congrArg (f.boundaryMap n) hxy)
    · intro b
      obtain ⟨x, hx⟩ := hb.2 (f.boundaryMap n b)
      exact ⟨x, (f.boundaryMap_bijective hf n).1 hx⟩

end GlobularSet

namespace Shape

noncomputable def cellArrow (S : Shape) (k : Globeᵒᵖ) (x : S.realize.obj k) :
    globe k.unop.dim ⟶ S := uliftYonedaEquiv.symm x

theorem cellArrow_map (S : Shape) {k l : Globeᵒᵖ} (a : k ⟶ l) (x : S.realize.obj k) :
    S.cellArrow l (S.realize.map a x) =
      GlobularTheory.shapeGlobes.map a.unop ≫ S.cellArrow k x :=
  uliftYonedaEquiv_symm_map a x

theorem cellArrow_naturality {S R : Shape} (f : S ⟶ R) (k : Globeᵒᵖ)
    (x : S.realize.obj k) :
    R.cellArrow k (f.app k x) = S.cellArrow k x ≫ f :=
  (uliftYonedaEquiv_symm_comp x f).symm

theorem cellArrow_identity (n : ℕ) :
    (globe n).cellArrow (op (Globe.mk n)) ⟨𝟙 (Globe.mk n)⟩ = 𝟙 (globe n) := by
  apply uliftYonedaEquiv.injective
  simp only [cellArrow]
  rfl

end Shape

namespace TupleSystem

noncomputable def globularPresheaf (T : TupleSystem.{v}) : GlobularPresheaf.{v} :=
  GlobularTheory.shapeGlobes.op ⋙ T.presheaf

noncomputable def evaluation (T : TupleSystem.{v}) :
    T.presheaf ⟶ T.globularPresheaf.tuples.presheaf where
  app S := TypeCat.ofHom (fun x =>
    { app k := TypeCat.ofHom (fun s => T.presheaf.map (S.unop.cellArrow k s.down).op x)
      naturality k l a := by
        apply ConcreteCategory.hom_ext
        intro s
        change ULift.{v} (S.unop.realize.obj k) at s
        change T.presheaf.map
            (S.unop.cellArrow l (S.unop.realize.map a s.down)).op x =
          T.presheaf.map (GlobularTheory.shapeGlobes.map a.unop).op
            (T.presheaf.map (S.unop.cellArrow k s.down).op x)
        rw [Shape.cellArrow_map]
        exact ConcreteCategory.congr_hom (T.presheaf.map_comp _ _) x })
  naturality S R f := by
    apply ConcreteCategory.hom_ext
    intro x
    apply NatTrans.ext
    funext k
    apply ConcreteCategory.hom_ext
    intro s
    change ULift.{v} (R.unop.realize.obj k) at s
    change T.presheaf.map (R.unop.cellArrow k s.down).op (T.presheaf.map f x) =
      T.presheaf.map (S.unop.cellArrow k (f.unop.app k s.down)).op x
    rw [Shape.cellArrow_naturality]
    exact (ConcreteCategory.congr_hom (T.presheaf.map_comp _ _) x).symm

@[simp]
theorem evaluation_globe (T : TupleSystem.{v}) (n : ℕ)
    (x : T.presheaf.obj (op (Shape.globe n))) :
    T.globularPresheaf.tupleCellEquiv n ((T.evaluation.app (op (Shape.globe n))) x) = x := by
  change T.presheaf.map
    ((Shape.globe n).cellArrow (op (Globe.mk n)) ⟨𝟙 (Globe.mk n)⟩).op x = x
  rw [Shape.cellArrow_identity, op_id, T.presheaf.map_id]
  rfl

theorem evaluation_bijective_globe (T : TupleSystem.{v}) (n : ℕ) :
    Function.Bijective (T.evaluation.app (op (Shape.globe n))) := by
  have h : (fun x => T.evaluation.app (op (Shape.globe n)) x) =
      (T.globularPresheaf.tupleCellEquiv n).symm := by
    funext x
    apply (T.globularPresheaf.tupleCellEquiv n).injective
    exact (T.evaluation_globe n x).trans (Equiv.apply_symm_apply _ _).symm
  change Function.Bijective (fun x => T.evaluation.app (op (Shape.globe n)) x)
  rw [h]
  exact (T.globularPresheaf.tupleCellEquiv n).symm.bijective

theorem evaluation_bijective (T : TupleSystem.{v}) (S : Shape) :
    Function.Bijective (T.evaluation.app (op S)) :=
  bijective_of_globes T.evaluation S.height (fun k _ => T.evaluation_bijective_globe k) S le_rfl

end TupleSystem

namespace GlobularPresheaf

theorem underlying_evalFace (X : GlobularPresheaf.{u}) {k j : ℕ}
    (a : Globe.Face k j) (x : X.obj (op (Globe.mk j))) :
    X.underlying.evalFace a x = X.map (show Globe.mk k ⟶ Globe.mk j from a).op x := by
  cases a with
  | id =>
    change x = X.map (𝟙 _) x
    rw [X.map_id]
    rfl
  | @face j h side =>
    change X.underlying.faceMap h side x = X.map (Globe.face h side).op x
    induction j, h using Nat.le_induction with
    | base =>
      rw [GlobularSet.faceMap_succ]
      cases side <;> rfl
    | succ j h ih =>
      apply (X.underlying.faceMap_source h side x).trans
      apply (ih (X.underlying.source j x)).trans
      have w : Globe.face (Nat.lt_succ_of_lt h) side = Globe.face h side ≫ Globe.source j := rfl
      rw [w, op_comp, X.map_comp]
      rfl

def underlyingPresheafIso (X : GlobularPresheaf.{u}) : X.underlying.presheaf ≅ X where
  hom :=
    { app _ := 𝟙 _
      naturality k j a := by
        apply ConcreteCategory.hom_ext
        intro x
        exact X.underlying_evalFace a.unop x }
  inv :=
    { app _ := 𝟙 _
      naturality k j a := by
        apply ConcreteCategory.hom_ext
        intro x
        exact (X.underlying_evalFace a.unop x).symm }

end GlobularPresheaf

namespace GlobularSet

def presheafUnderlyingMap (X : GlobularSet.{u}) : Hom X.presheaf.underlying X where
  app _ := _root_.id
  source_app n x := by
    change X.faceMap (Nat.lt_succ_self n) false x = X.source n x
    rw [X.faceMap_succ]
    rfl
  target_app n x := by
    change X.faceMap (Nat.lt_succ_self n) true x = X.target n x
    rw [X.faceMap_succ]
    rfl

end GlobularSet

namespace TupleSystem

noncomputable def modelUnderlyingMap {C : GlobularTheory.{v}} (T : TupleSystem.{v})
    (a : GlobularTheory.Morphism C T.endTheory) :
    GlobularSet.Hom (T.model a).underlying T.underlying where
  app _ := _root_.id
  source_app n x := ConcreteCategory.congr_hom (a.map_base (Shape.source n)) x
  target_app n x := ConcreteCategory.congr_hom (a.map_base (Shape.target n)) x

end TupleSystem

namespace GlobularTheory.Model

theorem exists_cutoff {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (X : C.Model) (q : ℕ) :
    ∃ (R : C.Model) (η : X ⟶ R),
      (∀ n, n ≤ q → Function.Bijective ((underlyingMap η).app n)) ∧
      (∀ j, q < j → Function.Bijective (R.underlying.boundary j)) := by
  let G := X.tuples.globularPresheaf
  let Z := G.underlying.cutoff q
  let U := Z.presheaf.tuples
  let g : G ⟶ Z.presheaf := G.underlyingPresheafIso.inv ≫
    (G.underlying.cutoffUnit q).presheafMap
  let f : X.tuples.presheaf ⟶ U.presheaf := X.tuples.evaluation ≫
    GlobularPresheaf.tuplesMap g
  have hlow (S : Shape) (hS : S.height ≤ q) : Function.Bijective (f.app (op S)) := by
    apply TupleSystem.bijective_of_globes f q _ S hS
    intro k hk
    exact (GlobularPresheaf.tuplesMap_bijective_globe g k
      (G.underlying.cutoffUnit_bijective hk)).comp (X.tuples.evaluation_bijective_globe k)
  have hhigh (j : ℕ) (hj : q < j) : Function.Bijective (U.underlying.boundary j) := by
    apply ((Z.presheaf.tupleUnderlyingMap).boundary_bijective_iff
      (fun k => (Z.presheaf.tupleCellEquiv k).bijective) j).mpr
    apply (Z.presheafUnderlyingMap.boundary_bijective_iff
      (fun _ => Function.bijective_id) j).mpr
    exact G.underlying.cutoff_boundary_bijective q j hj
  obtain ⟨a, ha⟩ := hC.1.some.lift (TupleSystem.relativeSource f)
    (TupleSystem.relativeSource_liftsFillers f q hlow hhigh) X.interpretation
  let R := U.model (a.comp (TupleSystem.relativeTarget f))
  let η : X ⟶ R :=
    { app S := f.app (op S.unop.shape)
      naturality S T g := by
        have w := (a.map g.unop).w
        have hm := congrArg (fun z : Morphism C X.tuples.endTheory => z.map g.unop) ha
        change (a.map g.unop).left = X.presheaf.map g at hm
        rw [hm] at w
        exact w }
  refine ⟨R, η, ?_, ?_⟩
  · intro k hk
    exact hlow (Shape.globe k) hk
  · intro j hj
    exact ((U.modelUnderlyingMap (a.comp (TupleSystem.relativeTarget f))).boundary_bijective_iff
      (fun _ => Function.bijective_id) j).mpr (hhigh j hj)

end GlobularTheory.Model

end Grothendieck

end OAI
