import OAI.CategoryTheory.Globular.CutoffExistence

namespace OAI

universe u v w

namespace Grothendieck

open CategoryTheory CategoryTheory.Limits Opposite

namespace GlobularSet

structure FactorStage {X R Y : GlobularSet.{v}} (η : Hom X R) (f : Hom X Y) (n : ℕ) where
  app : ∀ k, k ≤ n → R.Cell k → Y.Cell k
  source_app : ∀ k (h : k+1 ≤ n) x,
    app k (by omega) (R.source k x) = Y.source k (app (k+1) h x)
  target_app : ∀ k (h : k+1 ≤ n) x,
    app k (by omega) (R.target k x) = Y.target k (app (k+1) h x)
  fac : ∀ k (h : k ≤ n) x, app k h (η.app k x) = f.app k x

namespace FactorStage

variable {X R Y : GlobularSet.{v}} {η : Hom X R} {f : Hom X Y}

noncomputable def zero (h : Function.Bijective (η.app 0)) : FactorStage η f 0 where
  app k hk x := by
    have e : k = 0 := by omega
    subst k
    exact f.app 0 ((Equiv.ofBijective _ h).symm x)
  source_app k hk := by omega
  target_app k hk := by omega
  fac k hk x := by
    have e : k = 0 := by omega
    subst k
    exact congrArg (f.app 0) ((Equiv.ofBijective _ h).symm_apply_apply x)

def nextBoundary {n : ℕ} (a : FactorStage η f n) (x : R.Cell (n+1)) :
    Y.Boundary (n+1) :=
  ⟨(a.app n le_rfl (R.source n x), a.app n le_rfl (R.target n x)), by
    cases n with
    | zero => trivial
    | succ n =>
      constructor
      · rw [← a.source_app n le_rfl, ← a.source_app n le_rfl, R.source_source]
      · rw [← a.target_app n le_rfl, ← a.target_app n le_rfl, R.target_source]⟩

def extend {n : ℕ} (a : FactorStage η f n) (z : R.Cell (n+1) → Y.Cell (n+1))
    (hs : ∀ x, a.app n le_rfl (R.source n x) = Y.source n (z x))
    (ht : ∀ x, a.app n le_rfl (R.target n x) = Y.target n (z x))
    (hf : ∀ x, z (η.app (n+1) x) = f.app (n+1) x) : FactorStage η f (n+1) where
  app k hk x := if h : k ≤ n then a.app k h x else by
    have e : k = n+1 := by omega
    subst k
    exact z x
  source_app k hk x := by
    dsimp only
    split_ifs with h h'
    · exact a.source_app k h' x
    · have e : k = n := by omega
      subst k
      exact hs x
    · omega
    · omega
  target_app k hk x := by
    dsimp only
    split_ifs with h h'
    · exact a.target_app k h' x
    · have e : k = n := by omega
      subst k
      exact ht x
    · omega
    · omega
  fac k hk x := by
    dsimp only
    split_ifs with h
    · exact a.fac k h x
    · have e : k = n+1 := by omega
      subst k
      exact hf x

@[simp] theorem extend_old {n : ℕ} (a : FactorStage η f n) (z hs ht hf)
    (k : ℕ) (hk : k ≤ n) (x : R.Cell k) :
    (a.extend z hs ht hf).app k (by omega) x = a.app k hk x := by
  simp only [extend, dite_eq_left hk]

theorem exists_extend {n q : ℕ} (a : FactorStage η f n)
    (hη : ∀ k, k ≤ q → Function.Bijective (η.app k))
    (hY : ∀ j, q < j → Function.Bijective (Y.boundary j)) :
    ∃ b : FactorStage η f (n+1), ∀ k (hk : k ≤ n) x,
      b.app k (by omega) x = a.app k hk x := by
  classical
  by_cases hn : n+1 ≤ q
  · let e := Equiv.ofBijective (η.app (n+1)) (hη _ hn)
    let z (x : R.Cell (n+1)) := f.app (n+1) (e.symm x)
    have hs x : a.app n le_rfl (R.source n x) = Y.source n (z x) := by
      rw [show x = η.app (n+1) (e.symm x) from (e.apply_symm_apply x).symm,
        ← η.source_app, a.fac, f.source_app]
      exact congrArg (fun x => Y.source n (f.app (n+1) x)) (e.symm_apply_apply _).symm
    have ht x : a.app n le_rfl (R.target n x) = Y.target n (z x) := by
      rw [show x = η.app (n+1) (e.symm x) from (e.apply_symm_apply x).symm,
        ← η.target_app, a.fac, f.target_app]
      exact congrArg (fun x => Y.target n (f.app (n+1) x)) (e.symm_apply_apply _).symm
    have hf x : z (η.app (n+1) x) = f.app (n+1) x :=
      congrArg (f.app (n+1)) (e.symm_apply_apply x)
    exact ⟨a.extend z hs ht hf, fun k hk x => a.extend_old z hs ht hf k hk x⟩
  · let e := Equiv.ofBijective (Y.boundary (n+1)) (hY _ (by omega))
    let z (x : R.Cell (n+1)) := e.symm (a.nextBoundary x)
    have hb x : Y.boundary (n+1) (z x) = a.nextBoundary x := e.apply_symm_apply _
    have hs x : a.app n le_rfl (R.source n x) = Y.source n (z x) :=
      (congrArg (fun b => b.1.1) (hb x)).symm
    have ht x : a.app n le_rfl (R.target n x) = Y.target n (z x) :=
      (congrArg (fun b => b.1.2) (hb x)).symm
    have hf x : z (η.app (n+1) x) = f.app (n+1) x := by
      apply e.injective
      change Y.boundary (n+1) (z _) = Y.boundary (n+1) _
      rw [hb, ← f.boundary_app]
      apply Subtype.ext
      apply Prod.ext
      · change a.app n _ (R.source n (η.app (n+1) x)) = f.app n (X.source n x)
        rw [← η.source_app, a.fac]
      · change a.app n _ (R.target n (η.app (n+1) x)) = f.app n (X.target n x)
        rw [← η.target_app, a.fac]
    exact ⟨a.extend z hs ht hf, fun k hk x => a.extend_old z hs ht hf k hk x⟩

end FactorStage

theorem existsUnique_factor_low_bijective {X R Y : GlobularSet.{v}}
    (η : Hom X R) (f : Hom X Y) (q : ℕ)
    (hη : ∀ k, k ≤ q → Function.Bijective (η.app k))
    (hY : ∀ j, q < j → Function.Bijective (Y.boundary j)) :
    ∃! g : Hom R Y, η.comp g = f := by
  classical
  let a : (n : ℕ) → FactorStage η f n := fun n => Nat.rec
    (FactorStage.zero (hη 0 (Nat.zero_le _)))
    (fun _ a => (a.exists_extend hη hY).choose) n
  have ha (n k : ℕ) (hk : k ≤ n) (x : R.Cell k) :
      (a (n+1)).app k (by omega) x = (a n).app k hk x :=
    (FactorStage.exists_extend (a n) hη hY).choose_spec k hk x
  let g : Hom R Y :=
    { app n := (a n).app n le_rfl
      source_app n x := by
        rw [← ha n n le_rfl]
        exact (a (n+1)).source_app n le_rfl x
      target_app n x := by
        rw [← ha n n le_rfl]
        exact (a (n+1)).target_app n le_rfl x }
  have hg : η.comp g = f := by
    ext n x
    exact (a n).fac n le_rfl x
  refine ⟨g, hg, ?_⟩
  intro g' hg'
  ext n x
  induction n with
  | zero =>
    obtain ⟨y, rfl⟩ := (hη 0 (Nat.zero_le q)).2 x
    exact (congrArg (fun h : Hom X Y => h.app 0 y) hg').trans
      (congrArg (fun h : Hom X Y => h.app 0 y) hg).symm
  | succ n ih =>
    by_cases hn : n+1 ≤ q
    · obtain ⟨y, rfl⟩ := (hη (n+1) hn).2 x
      exact (congrArg (fun h : Hom X Y => h.app (n+1) y) hg').trans
        (congrArg (fun h : Hom X Y => h.app (n+1) y) hg).symm
    · apply (hY (n+1) (by omega)).1
      apply Subtype.ext
      apply Prod.ext
      · exact (g'.source_app n x).symm.trans ((ih _).trans (g.source_app n x))
      · exact (g'.target_app n x).symm.trans ((ih _).trans (g.target_app n x))

end GlobularSet

namespace TupleSystem

noncomputable def evaluationIso (T : TupleSystem.{v}) :
    T.presheaf ≅ T.globularPresheaf.tuples.presheaf :=
  NatIso.ofComponents
    (fun S => (Equiv.ofBijective (T.evaluation.app S) (T.evaluation_bijective S.unop)).toIso)
    (fun g => T.evaluation.naturality g)

theorem hom_ext_globes {T U : TupleSystem.{v}} (f g : T.presheaf ⟶ U.presheaf)
    (h : ∀ n, f.app (op (Shape.globe n)) = g.app (op (Shape.globe n))) : f = g := by
  apply NatTrans.ext
  funext S
  apply ConcreteCategory.hom_ext
  intro x
  apply (U.evaluation_bijective S.unop).1
  apply NatTrans.ext
  funext k
  apply ConcreteCategory.hom_ext
  intro z
  change U.presheaf.map (S.unop.cellArrow k z.down).op (f.app S x) =
    U.presheaf.map (S.unop.cellArrow k z.down).op (g.app S x)
  have hf := ConcreteCategory.congr_hom (f.naturality (S.unop.cellArrow k z.down).op) x
  have hg := ConcreteCategory.congr_hom (g.naturality (S.unop.cellArrow k z.down).op) x
  change f.app (op (Shape.globe k.unop.dim)) _ = _ at hf
  change g.app (op (Shape.globe k.unop.dim)) _ = _ at hg
  rw [h] at hf
  exact hf.symm.trans hg

noncomputable def mapFromUnderlying {T U : TupleSystem.{v}}
    (g : GlobularSet.Hom T.underlying U.underlying) : T.presheaf ⟶ U.presheaf :=
  T.evaluationIso.hom ≫ GlobularPresheaf.tuplesMap
    (T.globularPresheaf.underlyingPresheafIso.inv ≫ g.presheafMap ≫
      U.globularPresheaf.underlyingPresheafIso.hom) ≫ U.evaluationIso.inv

@[simp] theorem mapFromUnderlying_globe {T U : TupleSystem.{v}}
    (g : GlobularSet.Hom T.underlying U.underlying) (n : ℕ)
    (x : T.underlying.Cell n) :
    (mapFromUnderlying g).app (op (Shape.globe n)) x = g.app n x := by
  apply (U.evaluation_bijective_globe n).1
  change U.evaluationIso.hom.app (op (Shape.globe n))
    (U.evaluationIso.inv.app (op (Shape.globe n)) _) = _
  rw [Iso.inv_hom_id_app_apply]
  apply U.globularPresheaf.tupleCellEquiv n |>.injective
  have w := GlobularPresheaf.tupleCellEquiv_map
    (T.globularPresheaf.underlyingPresheafIso.inv ≫ g.presheafMap ≫
      U.globularPresheaf.underlyingPresheafIso.hom) n (T.evaluation.app _ x)
  apply w.trans
  change g.app n (T.globularPresheaf.tupleCellEquiv n (T.evaluation.app _ x)) =
    U.globularPresheaf.tupleCellEquiv n (U.evaluation.app _ (g.app n x))
  exact (congrArg (g.app n) (T.evaluation_globe n x)).trans
    (U.evaluation_globe n (g.app n x)).symm

end TupleSystem

namespace GlobularTheory.Model

theorem underlyingMap_injective {C : GlobularTheory.{v}} {X Y : C.Model} :
    Function.Injective (@underlyingMap _ X Y) := by
  intro f g h
  have w : (show X.tuples.presheaf ⟶ Y.tuples.presheaf from
      Functor.whiskerLeft C.toTheoryData.arity.op f) =
      Functor.whiskerLeft C.toTheoryData.arity.op g := by
    apply TupleSystem.hom_ext_globes
    intro n
    apply ConcreteCategory.hom_ext
    intro x
    exact congrArg (fun k : GlobularSet.Hom X.underlying Y.underlying => k.app n x) h
  apply NatTrans.ext
  funext S
  exact congrArg (fun k => k.app (op S.unop.shape)) w

end GlobularTheory.Model

end Grothendieck

end OAI
