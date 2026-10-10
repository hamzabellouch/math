import OAI.CategoryTheory.Globular.Composition

namespace OAI

universe u v w

namespace Grothendieck
open CategoryTheory CategoryTheory.Limits Opposite

namespace Shape

theorem face_two_source (n : ℕ) (side : Bool) :
    face (show n < n+2 by omega) side =
      face (Nat.lt_succ_self n) side ≫ source (n+1) :=
  GlobularTheory.shapeGlobes.map_comp (Globe.face (Nat.lt_succ_self n) side) (Globe.source (n+1))

theorem globe_seam_general (n k : ℕ) (h : k < n) :
    (globe n).seam h = face h true := Category.comp_id _

end Shape

namespace GlobularTheory.Model

theorem compCell_congr_left {C : GlobularTheory.{v}} (X : C.Model) (hC : C.IsCoherator)
    (n : ℕ) (a₀ a₁ b : X.underlying.Cell (n+1))
    (hab₀ : X.underlying.target n a₀ = X.underlying.source n b)
    (hab₁ : X.underlying.target n a₁ = X.underlying.source n b)
    (ha : X.underlying.Joined (n+1) a₀ a₁) :
    X.underlying.Joined (n+1) (X.compCell hC n a₀ b hab₀) (X.compCell hC n a₁ b hab₁) := by
  obtain ⟨h, hs, ht⟩ := ha
  let hn : n < n+2 := by omega
  let S := (Shape.globe (n+2)).attach n (n+1) hn (Nat.lt_succ_self n)
  let D := freeShape C S
  let l : Shape.globe (n+2) ⟶ S := (Shape.globe (n+2)).inl n (n+1) hn (Nat.lt_succ_self n)
  let r : Shape.globe (n+1) ⟶ S := (Shape.globe (n+2)).inr n (n+1) hn (Nat.lt_succ_self n)
  let H : D.underlying.Cell (n+2) := C.base l
  let B : D.underlying.Cell (n+1) := C.base r
  let A₀ := D.underlying.source (n+1) H
  let A₁ := D.underlying.target (n+1) H
  have hAB₀ : D.underlying.target n A₀ = D.underlying.source n B := by
    change C.comp (C.base (Shape.face (Nat.lt_succ_self n) true))
        (C.comp (C.base (Shape.source (n+1))) (C.base l)) =
      C.comp (C.base (Shape.source n)) (C.base r)
    rw [← C.assoc, ← C.base_comp, ← Shape.face_two_source, ← C.base_comp, ← C.base_comp]
    exact congrArg C.base (by
      simpa only [S, l, r, Shape.globe_seam_general, Shape.source] using
        Shape.seam_inl (Shape.globe (n+2)) n (n+1) hn (Nat.lt_succ_self n))
  have hAB₁ : D.underlying.target n A₁ = D.underlying.source n B :=
    (D.underlying.target_source n H).symm.trans hAB₀
  let t := X.sumTuple (Shape.globe (n+2)) n (n+1) hn (Nat.lt_succ_self n) h b (by
    change X.presheaf.obj (op (⟨Shape.globe (n+2)⟩ : C.Obj)) at h
    change X.presheaf.obj (op (⟨Shape.globe (n+1)⟩ : C.Obj)) at b
    rw [Shape.globe_seam_general, Shape.face_two_source, C.base_comp, eval_comp]
    change X.underlying.target n (X.underlying.source (n+1) h) = X.underlying.source n b
    rw [hs, hab₀])
  let f : D ⟶ X := X.tupleMap S t
  have hfH : (underlyingMap f).app (n+2) H = h := X.sumTuple_left _ _ _ _ _ _ _ _
  have hfB : (underlyingMap f).app (n+1) B = b := X.sumTuple_right _ _ _ _ _ _ _ _
  have hfA₀ : (underlyingMap f).app (n+1) A₀ = a₀ := by
    rw [(underlyingMap f).source_app, hfH, hs]
  have hfA₁ : (underlyingMap f).app (n+1) A₁ = a₁ := by
    rw [(underlyingMap f).target_app, hfH, ht]
  let u := D.compCell hC n A₀ B hAB₀
  let z := D.compCell hC n A₁ B hAB₁
  have hp : D.underlying.Parallel (n+1) u z := by
    constructor
    · dsimp [u, z]
      simp only [compCell_source]
      exact D.underlying.source_source n H
    · dsimp [u, z]
      simp only [compCell_target]
  have hz := (underlyingMap f).map_joined (freeShape_joined C hC S (n+1) u z hp)
  simpa only [u, z, map_compCell f, hfA₀, hfA₁, hfB] using hz

theorem compCell_congr_right {C : GlobularTheory.{v}} (X : C.Model) (hC : C.IsCoherator)
    (n : ℕ) (a b₀ b₁ : X.underlying.Cell (n+1))
    (hab₀ : X.underlying.target n a = X.underlying.source n b₀)
    (hab₁ : X.underlying.target n a = X.underlying.source n b₁)
    (hb : X.underlying.Joined (n+1) b₀ b₁) :
    X.underlying.Joined (n+1) (X.compCell hC n a b₀ hab₀) (X.compCell hC n a b₁ hab₁) := by
  obtain ⟨h, hs, ht⟩ := hb
  let hn : n < n+2 := by omega
  let S := (Shape.globe (n+1)).attach n (n+2) (Nat.lt_succ_self n) hn
  let D := freeShape C S
  let l : Shape.globe (n+1) ⟶ S := (Shape.globe (n+1)).inl n (n+2) (Nat.lt_succ_self n) hn
  let r : Shape.globe (n+2) ⟶ S := (Shape.globe (n+1)).inr n (n+2) (Nat.lt_succ_self n) hn
  let A : D.underlying.Cell (n+1) := C.base l
  let H : D.underlying.Cell (n+2) := C.base r
  let B₀ := D.underlying.source (n+1) H
  let B₁ := D.underlying.target (n+1) H
  have hAB₀ : D.underlying.target n A = D.underlying.source n B₀ := by
    change C.comp (C.base (Shape.target n)) (C.base l) =
      C.comp (C.base (Shape.face (Nat.lt_succ_self n) false))
        (C.comp (C.base (Shape.source (n+1))) (C.base r))
    rw [← C.assoc]
    simp only [← C.base_comp]
    rw [← Shape.face_two_source]
    exact congrArg C.base (by
      simpa only [Shape.globe_seam] using
        Shape.seam_inl (Shape.globe (n+1)) n (n+2) (Nat.lt_succ_self n) hn)
  have hAB₁ : D.underlying.target n A = D.underlying.source n B₁ :=
    hAB₀.trans (D.underlying.source_source n H)
  let t := X.sumTuple (Shape.globe (n+1)) n (n+2) (Nat.lt_succ_self n) hn a h (by
    change X.presheaf.obj (op (⟨Shape.globe (n+2)⟩ : C.Obj)) at h
    change X.presheaf.obj (op (⟨Shape.globe (n+1)⟩ : C.Obj)) at a
    rw [Shape.globe_seam, Shape.face_two_source, C.base_comp, eval_comp]
    change X.underlying.target n a = X.underlying.source n (X.underlying.source (n+1) h)
    rw [hs, hab₀])
  let f : D ⟶ X := X.tupleMap S t
  have hfA : (underlyingMap f).app (n+1) A = a := X.sumTuple_left _ _ _ _ _ _ _ _
  have hfH : (underlyingMap f).app (n+2) H = h := X.sumTuple_right _ _ _ _ _ _ _ _
  have hfB₀ : (underlyingMap f).app (n+1) B₀ = b₀ := by
    rw [(underlyingMap f).source_app, hfH, hs]
  have hfB₁ : (underlyingMap f).app (n+1) B₁ = b₁ := by
    rw [(underlyingMap f).target_app, hfH, ht]
  let u := D.compCell hC n A B₀ hAB₀
  let z := D.compCell hC n A B₁ hAB₁
  have hp : D.underlying.Parallel (n+1) u z := by
    constructor
    · dsimp [u, z]
      simp only [compCell_source]
    · dsimp [u, z]
      simp only [compCell_target]
      exact D.underlying.target_source n H
  have hz := (underlyingMap f).map_joined (freeShape_joined C hC S (n+1) u z hp)
  simpa only [u, z, map_compCell f, hfA, hfB₀, hfB₁] using hz

end GlobularTheory.Model
end Grothendieck

namespace Grothendieck.GlobularTheory.Model
open CategoryTheory CategoryTheory.Limits Opposite

noncomputable def targetDisk (C : GlobularTheory.{v}) (n : ℕ) :
    disk C n ⟶ disk C (n+1) :=
  show (disk C n).presheaf ⟶ (disk C (n+1)).presheaf from
    yoneda.map (show (⟨Shape.globe n⟩ : C.Obj) ⟶ ⟨Shape.globe (n+1)⟩ from
      C.base (Shape.target n))

@[simp] theorem cellEquiv_targetDisk {C : GlobularTheory.{v}} {X : C.Model}
    (n : ℕ) (a : disk C (n+1) ⟶ X) :
    cellEquiv X n (targetDisk C n ≫ a) = X.underlying.target n (cellEquiv X (n+1) a) :=
  (yonedaEquiv_naturality a
    (show (⟨Shape.globe n⟩ : C.Obj) ⟶ ⟨Shape.globe (n+1)⟩ from
      C.base (Shape.target n))).symm

structure BoundaryRepresentation (C : GlobularTheory.{v}) (n : ℕ) where
  obj : C.Model
  inclusion : obj ⟶ disk C n
  equiv : ∀ X : C.Model, (obj ⟶ X) ≃ X.underlying.Boundary n
  naturality : ∀ {X Y : C.Model} (f : obj ⟶ X) (g : X ⟶ Y),
    equiv Y (f ≫ g) = (underlyingMap g).boundaryMap n (equiv X f)
  inclusion_boundary : ∀ {X : C.Model} (f : disk C n ⟶ X),
    equiv X (inclusion ≫ f) = X.underlying.boundary n (cellEquiv X n f)

namespace BoundaryRepresentation

noncomputable def zero (C : GlobularTheory.{v}) : BoundaryRepresentation C 0 where
  obj := ⊥_ C.Model
  inclusion := initial.to _
  equiv X :=
    { toFun := fun _ => PUnit.unit
      invFun := fun _ => initial.to X
      left_inv := fun _ => initial.hom_ext _ _
      right_inv := fun _ => by change (PUnit.unit : PUnit) = _; exact Subsingleton.elim _ _ }
  naturality _ _ := rfl
  inclusion_boundary _ := rfl

variable {C : GlobularTheory.{v}} {n : ℕ} (R : BoundaryRepresentation C n)

noncomputable abbrev nextObj : C.Model := pushout R.inclusion R.inclusion

noncomputable def nextValue (X : C.Model) (f : R.nextObj ⟶ X) :
    X.underlying.Boundary (n+1) :=
  ⟨(cellEquiv X n (pushout.inl _ _ ≫ f), cellEquiv X n (pushout.inr _ _ ≫ f)), by
    rw [GlobularSet.parallel_iff_boundary_eq,
      ← R.inclusion_boundary, ← R.inclusion_boundary, ← Category.assoc, ← Category.assoc,
      pushout.condition]⟩

theorem nextValue_bijective (X : C.Model) : Function.Bijective (R.nextValue X) := by
  constructor
  · intro f g h
    apply pushout.hom_ext
    · apply (cellEquiv X n).injective
      exact congrArg (fun b => b.1.1) h
    · apply (cellEquiv X n).injective
      exact congrArg (fun b => b.1.2) h
  · intro b
    let f := (cellEquiv X n).symm b.1.1
    let g := (cellEquiv X n).symm b.1.2
    have hfg : R.inclusion ≫ f = R.inclusion ≫ g := by
      apply (R.equiv X).injective
      simp only [R.inclusion_boundary, f, g, Equiv.apply_symm_apply]
      exact (GlobularSet.parallel_iff_boundary_eq _ _ _ _).1 b.2
    refine ⟨pushout.desc f g hfg, ?_⟩
    apply Subtype.ext
    change (cellEquiv X n (pushout.inl _ _ ≫ pushout.desc f g hfg),
      cellEquiv X n (pushout.inr _ _ ≫ pushout.desc f g hfg)) = b.1
    simp only [pushout.inl_desc, pushout.inr_desc, f, g, Equiv.apply_symm_apply]

theorem face_condition : R.inclusion ≫ J C n = R.inclusion ≫ targetDisk C n := by
  apply (R.equiv (disk C (n+1))).injective
  rw [R.inclusion_boundary, R.inclusion_boundary]
  have h := GlobularSet.Joined.parallel
    (⟨cellEquiv (disk C (n+1)) (n+1) (𝟙 _), rfl, rfl⟩ :
      (disk C (n+1)).underlying.Joined n
        ((disk C (n+1)).underlying.source n (cellEquiv _ (n+1) (𝟙 _)))
        ((disk C (n+1)).underlying.target n (cellEquiv _ (n+1) (𝟙 _))))
  have hs := cellEquiv_J (X := disk C (n+1)) n (𝟙 _)
  have ht := cellEquiv_targetDisk (X := disk C (n+1)) n (𝟙 _)
  rw [Category.comp_id] at hs ht
  rw [hs, ht]
  exact (GlobularSet.parallel_iff_boundary_eq _ _ _ _).1 h

noncomputable def succ : BoundaryRepresentation C (n+1) where
  obj := R.nextObj
  inclusion := pushout.desc (J C n) (targetDisk C n) R.face_condition
  equiv X := Equiv.ofBijective (R.nextValue X) (R.nextValue_bijective X)
  naturality f g := by
    apply Subtype.ext
    apply Prod.ext <;> change cellEquiv _ n (_ ≫ (f ≫ g)) = _
    · rw [← Category.assoc, cellEquiv_comp]; rfl
    · rw [← Category.assoc, cellEquiv_comp]; rfl
  inclusion_boundary f := by
    apply Subtype.ext
    change (cellEquiv _ n (pushout.inl _ _ ≫ (pushout.desc _ _ _ ≫ f)),
      cellEquiv _ n (pushout.inr _ _ ≫ (pushout.desc _ _ _ ≫ f))) =
      (_, _)
    simp only [← Category.assoc, pushout.inl_desc, pushout.inr_desc,
      cellEquiv_J, cellEquiv_targetDisk]

end BoundaryRepresentation

noncomputable def boundaryRepresentation (C : GlobularTheory.{v}) :
    (n : ℕ) → BoundaryRepresentation C n
  | 0 => BoundaryRepresentation.zero C
  | n+1 => (boundaryRepresentation C n).succ

noncomputable abbrev boundaryDisk (C : GlobularTheory.{v}) (n : ℕ) : C.Model :=
  (boundaryRepresentation C n).obj

noncomputable abbrev I (C : GlobularTheory.{v}) (n : ℕ) : boundaryDisk C n ⟶ disk C n :=
  (boundaryRepresentation C n).inclusion

open CategoryTheory CategoryTheory.Limits Opposite

theorem hasLiftingProperty_I_iff {C : GlobularTheory.{v}} {X Y : C.Model}
    (n : ℕ) (p : X ⟶ Y) :
    HasLiftingProperty (I C n) p ↔
      ∀ (b : X.underlying.Boundary n) (y : Y.underlying.Cell n),
        Y.underlying.boundary n y = (underlyingMap p).boundaryMap n b →
        ∃ x : X.underlying.Cell n,
          X.underlying.boundary n x = b ∧ (underlyingMap p).app n x = y := by
  let R := boundaryRepresentation C n
  constructor
  · intro hp b y hy
    let f : boundaryDisk C n ⟶ X := (R.equiv X).symm b
    let g : disk C n ⟶ Y := (cellEquiv Y n).symm y
    have sq : CommSq f (I C n) p g := by
      constructor
      apply (R.equiv Y).injective
      rw [R.naturality, R.inclusion_boundary]
      simpa only [f, g, Equiv.apply_symm_apply] using hy.symm
    let := hp
    refine ⟨cellEquiv X n sq.lift, ?_, ?_⟩
    · rw [← R.inclusion_boundary, sq.fac_left]
      exact (R.equiv X).apply_symm_apply b
    · rw [← cellEquiv_comp, sq.fac_right]
      exact (cellEquiv Y n).apply_symm_apply y
  · intro hp
    constructor
    intro f g sq
    have h : Y.underlying.boundary n (cellEquiv Y n g) =
        (underlyingMap p).boundaryMap n (R.equiv X f) := by
      rw [← R.inclusion_boundary, ← R.naturality, sq.w]
    obtain ⟨x, hx, hpx⟩ := hp (R.equiv X f) (cellEquiv Y n g) h
    let l : disk C n ⟶ X := (cellEquiv X n).symm x
    refine CommSq.HasLift.mk' { l := l, fac_left := ?_, fac_right := ?_ }
    · apply (R.equiv X).injective
      rw [R.inclusion_boundary]
      simpa only [l, Equiv.apply_symm_apply] using hx
    · apply (cellEquiv Y n).injective
      rw [cellEquiv_comp]
      simpa only [l, Equiv.apply_symm_apply] using hpx

theorem liftsBoundaries_iff {C : GlobularTheory.{v}} {X Y : C.Model} (p : X ⟶ Y) :
    GlobularSet.LiftsBoundaries (underlyingMap p) ↔ ∀ n, HasLiftingProperty (I C n) p := by
  simp only [hasLiftingProperty_I_iff, GlobularSet.LiftsBoundaries]

theorem hasLiftingProperty_J_iff {C : GlobularTheory.{v}} {X Y : C.Model}
    (n : ℕ) (p : X ⟶ Y) :
    HasLiftingProperty (J C n) p ↔
      ∀ (x : X.underlying.Cell n) (y : Y.underlying.Cell (n+1)),
        Y.underlying.source n y = (underlyingMap p).app n x →
        ∃ z : X.underlying.Cell (n+1),
          X.underlying.source n z = x ∧ (underlyingMap p).app (n+1) z = y := by
  constructor
  · intro hp x y hy
    let f : disk C n ⟶ X := (cellEquiv X n).symm x
    let g : disk C (n+1) ⟶ Y := (cellEquiv Y (n+1)).symm y
    have sq : CommSq f (J C n) p g := by
      constructor
      apply (cellEquiv Y n).injective
      rw [cellEquiv_comp, cellEquiv_J]
      simpa only [f, g, Equiv.apply_symm_apply] using hy.symm
    let := hp
    refine ⟨cellEquiv X (n+1) sq.lift, ?_, ?_⟩
    · rw [← cellEquiv_J, sq.fac_left]
      exact (cellEquiv X n).apply_symm_apply x
    · rw [← cellEquiv_comp, sq.fac_right]
      exact (cellEquiv Y (n+1)).apply_symm_apply y
  · intro hp
    constructor
    intro f g sq
    have h : Y.underlying.source n (cellEquiv Y (n+1) g) =
        (underlyingMap p).app n (cellEquiv X n f) := by
      rw [← cellEquiv_J, ← cellEquiv_comp, sq.w]
    obtain ⟨z, hz, hpz⟩ := hp (cellEquiv X n f) (cellEquiv Y (n+1) g) h
    let l : disk C (n+1) ⟶ X := (cellEquiv X (n+1)).symm z
    refine CommSq.HasLift.mk' { l := l, fac_left := ?_, fac_right := ?_ }
    · apply (cellEquiv X n).injective
      rw [cellEquiv_J]
      simpa only [l, Equiv.apply_symm_apply] using hz
    · apply (cellEquiv Y (n+1)).injective
      rw [cellEquiv_comp]
      simpa only [l, Equiv.apply_symm_apply] using hpz

end Grothendieck.GlobularTheory.Model

end OAI
