import OAI.CategoryTheory.Globular.Spines

namespace OAI

universe u v w

namespace Grothendieck

open CategoryTheory CategoryTheory.Limits Opposite

namespace GlobularTheory.Model

noncomputable def freeShapeMap (C : GlobularTheory.{v}) {S T : Shape}
    (f : S ⟶ T) : freeShape C S ⟶ freeShape C T :=
  yoneda.map (C.toTheoryData.arity.map f)

theorem freeShapeMap_low_bijective {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    {S T : Shape} (f : S ⟶ T) (q : ℕ)
    (hf : ∀ k, k ≤ q → Function.Bijective (f.app (op (Globe.mk k)))) :
    ∀ k, k ≤ q → Function.Bijective ((underlyingMap (freeShapeMap C f)).app k) := by
  apply (coskeletalLocalMap_iff hC q (freeShapeMap C f)).mp
  intro Z hZ g
  have hb := TupleSystem.map_bijective_of_low (T := Z.tuples) f q hf hZ
  obtain ⟨x, hx⟩ := hb.2 (yonedaEquiv g)
  let h : freeShape C T ⟶ Z := yonedaEquiv.symm x
  have hh : freeShapeMap C f ≫ h = g := by
    apply yonedaEquiv.injective
    have hv : yonedaEquiv h = x := Equiv.apply_symm_apply _ _
    exact (yonedaEquiv_naturality h (C.toTheoryData.arity.map f)).symm.trans
      ((congrArg (Z.tuples.presheaf.map f.op) hv).trans hx)
  refine ⟨h, hh, ?_⟩
  intro h' hh'
  apply yonedaEquiv.injective
  apply hb.1
  exact (yonedaEquiv_naturality h' (C.toTheoryData.arity.map f)).trans
    ((congrArg yonedaEquiv hh').trans
      ((congrArg yonedaEquiv hh).symm.trans
        (yonedaEquiv_naturality h (C.toTheoryData.arity.map f)).symm))

end GlobularTheory.Model

namespace GlobularSet

def HasFillers (X : GlobularSet.{u}) : Prop := ∀ n, Function.Surjective (X.boundary n)

theorem Hom.reflects_parallel_of_low {X Y : GlobularSet.{u}} (f : Hom X Y)
    {n : ℕ} (hf : ∀ k, k < n → Function.Injective (f.app k))
    {a b : X.Cell n} (h : Y.Parallel n (f.app n a) (f.app n b)) :
    X.Parallel n a b := by
  cases n with
  | zero => trivial
  | succ n =>
    exact ⟨hf n (Nat.lt_succ_self n) (by rw [f.source_app, f.source_app]; exact h.1),
      hf n (Nat.lt_succ_self n) (by rw [f.target_app, f.target_app]; exact h.2)⟩

theorem Hom.boundaryMap_bijective_of_low {X Y : GlobularSet.{u}} (f : Hom X Y)
    (n : ℕ) (hf : ∀ k, k < n → Function.Bijective (f.app k)) :
    Function.Bijective (f.boundaryMap n) := by
  cases n with
  | zero =>
    change Function.Bijective (fun _ : PUnit => (PUnit.unit : PUnit))
    exact ⟨fun _ _ _ => Subsingleton.elim _ _, fun _ => ⟨PUnit.unit, rfl⟩⟩
  | succ n =>
    constructor
    · intro a b h
      exact Subtype.ext (Prod.ext
        ((hf n (Nat.lt_succ_self n)).1 (congrArg (fun b => b.1.1) h))
        ((hf n (Nat.lt_succ_self n)).1 (congrArg (fun b => b.1.2) h)))
    · intro b
      obtain ⟨x, hx⟩ := (hf n (Nat.lt_succ_self n)).2 b.1.1
      obtain ⟨y, hy⟩ := (hf n (Nat.lt_succ_self n)).2 b.1.2
      have hp : X.Parallel n x y := f.reflects_parallel_of_low
        (fun k hk => (hf k (by omega)).1) (by rw [hx, hy]; exact b.2)
      exact ⟨⟨(x, y), hp⟩, Subtype.ext (Prod.ext hx hy)⟩

theorem HasFillers.of_low_bijective {X Y : GlobularSet.{u}}
    (hX : X.HasFillers) (f : Hom X Y) (q : ℕ)
    (hf : ∀ k, k ≤ q → Function.Bijective (f.app k))
    (hY : ∀ j, q < j → Function.Surjective (Y.boundary j)) : Y.HasFillers := by
  intro n
  by_cases hn : n ≤ q
  · intro b
    obtain ⟨b', hb'⟩ := (f.boundaryMap_bijective_of_low n (fun k hk => hf k (by omega))).2 b
    obtain ⟨x, hx⟩ := hX n b'
    exact ⟨f.app n x, (f.boundary_app n x).symm.trans ((congrArg (f.boundaryMap n) hx).trans hb')⟩
  · exact hY n (by omega)

end GlobularSet

namespace GlobularTheory.Model

theorem freeShape_joined (C : GlobularTheory.{v}) (hC : C.IsCoherator) (S : Shape)
    (n : ℕ) (a b : (freeShape C S).underlying.Cell n)
    (hp : (freeShape C S).underlying.Parallel n a b) :
    (freeShape C S).underlying.Joined n a b := by
  let P := S.2.spine n
  let f : P.S ⟶ S := P.map
  let i := underlyingMap (freeShapeMap C f)
  have hi : ∀ k, k ≤ n → Function.Bijective (i.app k) :=
    freeShapeMap_low_bijective hC f n P.low_bijective
  obtain ⟨a', ha⟩ := (hi n le_rfl).2 a
  obtain ⟨b', hb⟩ := (hi n le_rfl).2 b
  have hp' : (freeShape C P.S).underlying.Parallel n a' b' :=
    i.reflects_parallel_of_low (fun k hk => (hi k (by omega)).1) (by rw [ha, hb]; exact hp)
  have hp'' : C.Parallel n a' b' := by
    cases n <;> exact hp'
  let pair : C.AdmissiblePair := ⟨n, P.S, P.height_le, a', b', hp''⟩
  obtain ⟨z, hs, ht⟩ := hC.2 pair
  have hz : (freeShape C P.S).underlying.Joined n a' b' := ⟨z, hs, ht⟩
  have hz' := i.map_joined hz
  rw [ha, hb] at hz'
  exact hz'

theorem freeShape_hasFillers (C : GlobularTheory.{v}) (hC : C.IsCoherator) (S : Shape) :
    (freeShape C S).underlying.HasFillers := by
  intro n
  cases n with
  | zero =>
    intro b
    let f : Shape.globe 0 ⟶ S :=
      show GlobularPresheaf.disk 0 ⟶ S.realize from
        GlobularPresheaf.faceLE (Nat.zero_le S.1) false ≫ S.last
    refine ⟨C.base f, ?_⟩
    change PUnit.unit = b
    exact Subsingleton.elim _ _
  | succ n =>
    intro b
    obtain ⟨z, hs, ht⟩ := freeShape_joined C hC S n b.1.1 b.1.2 b.2
    exact ⟨z, Subtype.ext (Prod.ext hs ht)⟩

theorem cutoff_freeShape_hasFillers (C : GlobularTheory.{v}) (hC : C.IsCoherator)
    (S : Shape) (q : ℕ) :
    (chosenCutoff hC q (freeShape C S)).underlying.HasFillers :=
  (freeShape_hasFillers C hC S).of_low_bijective
    (underlyingMap (cutoffUnit hC q (freeShape C S))) q
    (cutoffUnit_low_bijective hC q _)
    (fun j hj => (chosenCutoff_coskeletal hC q _ j hj).2)

end GlobularTheory.Model

end Grothendieck

namespace Grothendieck.GlobularTheory.Model

open CategoryTheory CategoryTheory.Limits Opposite

def presheafFunctor (C : GlobularTheory.{v}) : C.Model ⥤ (C.Objᵒᵖ ⥤ Type v) where
  obj X := X.presheaf
  map f := f

noncomputable def forgetGlobular (C : GlobularTheory.{v}) : C.Model ⥤ GlobularPresheaf.{v} :=
  presheafFunctor C ⋙ (Functor.whiskeringLeft Globeᵒᵖ C.Objᵒᵖ (Type v)).obj C.globes.op

@[instance_reducible] noncomputable def presheafReflection (C : GlobularTheory.{v}) :
    Reflective C.sumComparisons.isLocal.ι := by
  let := C.sumComparisons_rightAdjoint
  exact ⟨_, Adjunction.ofIsRightAdjoint C.sumComparisons.isLocal.ι⟩

noncomputable def freePresheaf (C : GlobularTheory.{v}) :
    (C.Objᵒᵖ ⥤ Type v) ⥤ C.Model := by
  let := presheafReflection C
  exact reflector C.sumComparisons.isLocal.ι ⋙ fromLocal C

noncomputable def presheafAdjunction (C : GlobularTheory.{v}) :
    freePresheaf C ⊣ presheafFunctor C := by
  let := presheafReflection C
  exact ((reflectorAdjunction C.sumComparisons.isLocal.ι).comp
    (localEquivalence C).symm.toAdjunction)

noncomputable def freeGlobular (C : GlobularTheory.{v}) : GlobularPresheaf.{v} ⥤ C.Model :=
  C.globes.op.lan ⋙ freePresheaf C

noncomputable def globularAdjunction (C : GlobularTheory.{v}) :
    freeGlobular C ⊣ forgetGlobular C :=
  (C.globes.op.lanAdjunction (Type v)).comp (presheafAdjunction C)

instance freeGlobular_preservesColimits (C : GlobularTheory.{v}) :
    PreservesColimitsOfSize.{v,v} (freeGlobular C) :=
  (globularAdjunction C).leftAdjoint_preservesColimits

end Grothendieck.GlobularTheory.Model

namespace Grothendieck
open CategoryTheory CategoryTheory.Limits Opposite

namespace GlobularTheory

noncomputable def composition (C : GlobularTheory.{v}) (hC : C.IsCoherator) (n : ℕ) :
    C.Hom (Shape.globe (n+1)) (compositionShape n) :=
  (hC.2 (C.compositionPair n)).choose

theorem composition_source (C : GlobularTheory.{v}) (hC : C.IsCoherator) (n : ℕ) :
    C.comp (C.base (Shape.source n)) (C.composition hC n) =
      C.base (Shape.source n ≫ compositionLeft n) :=
  (hC.2 (C.compositionPair n)).choose_spec.1

theorem composition_target (C : GlobularTheory.{v}) (hC : C.IsCoherator) (n : ℕ) :
    C.comp (C.base (Shape.target n)) (C.composition hC n) =
      C.base (Shape.target n ≫ compositionRight n) :=
  (hC.2 (C.compositionPair n)).choose_spec.2

noncomputable def inverse (C : GlobularTheory.{v}) (hC : C.IsCoherator) (n : ℕ) :
    C.Hom (Shape.globe (n+1)) (Shape.globe (n+1)) :=
  (hC.2 (C.inversePair n)).choose

theorem inverse_source (C : GlobularTheory.{v}) (hC : C.IsCoherator) (n : ℕ) :
    C.comp (C.base (Shape.source n)) (C.inverse hC n) = C.base (Shape.target n) :=
  (hC.2 (C.inversePair n)).choose_spec.1

theorem inverse_target (C : GlobularTheory.{v}) (hC : C.IsCoherator) (n : ℕ) :
    C.comp (C.base (Shape.target n)) (C.inverse hC n) = C.base (Shape.source n) :=
  (hC.2 (C.inversePair n)).choose_spec.2

namespace Model

theorem map_eval {C : GlobularTheory.{v}} {X Y : C.Model} (f : X ⟶ Y)
    {S T : Shape} (a : C.Hom S T) (t : X.presheaf.obj (op (⟨T⟩ : C.Obj))) :
    f.app (op (⟨S⟩ : C.Obj)) (X.eval a t) =
      Y.eval a (f.app (op (⟨T⟩ : C.Obj)) t) :=
  (ConcreteCategory.congr_hom (f.naturality
    (show (op (⟨T⟩ : C.Obj)) ⟶ op ⟨S⟩ from Quiver.Hom.op a)) t)

noncomputable def sumTuple {C : GlobularTheory.{v}} (X : C.Model)
    (S : Shape) (b h : ℕ) (hl : b < S.1) (hr : b < h)
    (a : X.presheaf.obj (op (⟨S⟩ : C.Obj))) (d : X.underlying.Cell h)
    (w : X.eval (C.base (S.seam hl)) a = X.eval (C.base (Shape.face hr false)) d) :
    X.presheaf.obj (op (⟨S.attach b h hl hr⟩ : C.Obj)) :=
  (Types.exists_of_isPullback (X.sums S b h hl hr) a d w).choose

@[simp] theorem sumTuple_left {C : GlobularTheory.{v}} (X : C.Model)
    (S : Shape) (b h : ℕ) (hl : b < S.1) (hr : b < h)
    (a : X.presheaf.obj (op (⟨S⟩ : C.Obj))) (d : X.underlying.Cell h)
    (w : X.eval (C.base (S.seam hl)) a = X.eval (C.base (Shape.face hr false)) d) :
    X.eval (C.base (S.inl b h hl hr)) (X.sumTuple S b h hl hr a d w) = a :=
  (Types.exists_of_isPullback (X.sums S b h hl hr) a d w).choose_spec.1

@[simp] theorem sumTuple_right {C : GlobularTheory.{v}} (X : C.Model)
    (S : Shape) (b h : ℕ) (hl : b < S.1) (hr : b < h)
    (a : X.presheaf.obj (op (⟨S⟩ : C.Obj))) (d : X.underlying.Cell h)
    (w : X.eval (C.base (S.seam hl)) a = X.eval (C.base (Shape.face hr false)) d) :
    X.eval (C.base (S.inr b h hl hr)) (X.sumTuple S b h hl hr a d w) = d :=
  (Types.exists_of_isPullback (X.sums S b h hl hr) a d w).choose_spec.2

noncomputable def compositionTuple {C : GlobularTheory.{v}} (X : C.Model) (n : ℕ)
    (a b : X.underlying.Cell (n+1)) (hab : X.underlying.target n a = X.underlying.source n b) :
    X.presheaf.obj (op (⟨compositionShape n⟩ : C.Obj)) :=
  X.sumTuple (Shape.globe (n+1)) n (n+1) (Nat.lt_succ_self n) (Nat.lt_succ_self n)
    a b (by rw [Shape.globe_seam]; exact hab)

@[simp] theorem compositionTuple_left {C : GlobularTheory.{v}} (X : C.Model) (n : ℕ)
    (a b : X.underlying.Cell (n+1)) (hab : X.underlying.target n a = X.underlying.source n b) :
    X.eval (C.base (compositionLeft n)) (X.compositionTuple n a b hab) = a :=
  X.sumTuple_left _ _ _ _ _ _ _ _

@[simp] theorem compositionTuple_right {C : GlobularTheory.{v}} (X : C.Model) (n : ℕ)
    (a b : X.underlying.Cell (n+1)) (hab : X.underlying.target n a = X.underlying.source n b) :
    X.eval (C.base (compositionRight n)) (X.compositionTuple n a b hab) = b :=
  X.sumTuple_right _ _ _ _ _ _ _ _

noncomputable def compCell {C : GlobularTheory.{v}} (X : C.Model) (hC : C.IsCoherator) (n : ℕ)
    (a b : X.underlying.Cell (n+1)) (hab : X.underlying.target n a = X.underlying.source n b) :
    X.underlying.Cell (n+1) := X.eval (C.composition hC n) (X.compositionTuple n a b hab)

@[simp] theorem compCell_source {C : GlobularTheory.{v}} (X : C.Model) (hC : C.IsCoherator) (n : ℕ)
    (a b : X.underlying.Cell (n+1)) (hab : X.underlying.target n a = X.underlying.source n b) :
    X.underlying.source n (X.compCell hC n a b hab) = X.underlying.source n a := by
  change X.eval (C.base (Shape.source n)) (X.eval _ _) = _
  rw [← eval_comp, composition_source, C.base_comp, eval_comp, compositionTuple_left]
  rfl

@[simp] theorem compCell_target {C : GlobularTheory.{v}} (X : C.Model) (hC : C.IsCoherator) (n : ℕ)
    (a b : X.underlying.Cell (n+1)) (hab : X.underlying.target n a = X.underlying.source n b) :
    X.underlying.target n (X.compCell hC n a b hab) = X.underlying.target n b := by
  change X.eval (C.base (Shape.target n)) (X.eval _ _) = _
  rw [← eval_comp, composition_target, C.base_comp, eval_comp, compositionTuple_right]
  rfl

noncomputable def inverseCell {C : GlobularTheory.{v}} (X : C.Model) (hC : C.IsCoherator) (n : ℕ)
    (a : X.underlying.Cell (n+1)) : X.underlying.Cell (n+1) := X.eval (C.inverse hC n) a

@[simp] theorem inverseCell_source {C : GlobularTheory.{v}} (X : C.Model) (hC : C.IsCoherator)
    (n : ℕ) (a : X.underlying.Cell (n+1)) :
    X.underlying.source n (X.inverseCell hC n a) = X.underlying.target n a := by
  change X.presheaf.obj (op (⟨Shape.globe (n+1)⟩ : C.Obj)) at a
  change X.eval (C.base (Shape.source n)) (X.eval _ a) = _
  rw [← eval_comp, inverse_source]
  rfl

@[simp] theorem inverseCell_target {C : GlobularTheory.{v}} (X : C.Model) (hC : C.IsCoherator)
    (n : ℕ) (a : X.underlying.Cell (n+1)) :
    X.underlying.target n (X.inverseCell hC n a) = X.underlying.source n a := by
  change X.presheaf.obj (op (⟨Shape.globe (n+1)⟩ : C.Obj)) at a
  change X.eval (C.base (Shape.target n)) (X.eval _ a) = _
  rw [← eval_comp, inverse_target]
  rfl

theorem map_inverseCell {C : GlobularTheory.{v}} {X Y : C.Model} (f : X ⟶ Y)
    (hC : C.IsCoherator) (n : ℕ) (a : X.underlying.Cell (n+1)) :
    (underlyingMap f).app (n+1) (X.inverseCell hC n a) =
      Y.inverseCell hC n ((underlyingMap f).app (n+1) a) :=
  map_eval f (C.inverse hC n) a

end Model
end GlobularTheory
end Grothendieck

end OAI
