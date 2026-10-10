import OAI.CategoryTheory.Thomason.Gray.FixedPathCylinders
import OAI.CategoryTheory.Thomason.Simplicial.ConstructedPosetCosieves
import OAI.CategoryTheory.Thomason.Simplicial.FixedInternalPathMaps
import OAI.CategoryTheory.Thomason.Simplicial.TruncationCongruence

namespace OAI

section

/-! # Singular fixed-endpoint paths as the actual internal path subcomplex -/

namespace Thomason.Construction

open CategoryTheory MonoidalCategory
open scoped Simplicial

noncomputable section

/-- Transposing a continuous family of fixed paths lands in the exact
fixed-endpoint subcomplex of the singular internal hom. -/
def fixedPathToInternal {K : SSet.{0}} {X : TopCat.{0}} {x y : X}
    (f : K ⟶ TopCat.toSSet.obj (TopCat.of (Path x y))) :
    K ⟶ fixedInternalPaths (TopCat.toSSet.obj X)
      (TopCat.toSSetObj₀Equiv.symm x) (TopCat.toSSetObj₀Equiv.symm y) :=
  fixedInternalPathsLift _ _ (internalPathTranspose (fixedPathCylinder f))
    (by rw [← internalPathCylinder_start, internalPathCylinder_transpose,
        fixedPathCylinder_zero])
    (by rw [← internalPathCylinder_end, internalPathCylinder_transpose,
        fixedPathCylinder_one])

/-- Evaluation reverses this construction on a family in the actual
fixed-endpoint internal path complex. -/
def internalToFixedPath {K : SSet.{0}} {X : TopCat.{0}} {x y : X}
    (a : K ⟶ fixedInternalPaths (TopCat.toSSet.obj X)
      (TopCat.toSSetObj₀Equiv.symm x) (TopCat.toSSetObj₀Equiv.symm y)) :
    K ⟶ TopCat.toSSet.obj (TopCat.of (Path x y)) :=
  sSetTopAdj.homEquiv _ _ (fixedPathRealization
    (internalPathCylinder (a ≫ (fixedInternalPathSubcomplex _ _ _).ι))
    (by rw [internalPathCylinder_start, Category.assoc,
        fixedInternalPaths_start, SSet.comp_const])
    (by rw [internalPathCylinder_end, Category.assoc,
        fixedInternalPaths_end, SSet.comp_const]))

theorem internalToFixedPath_left_inverse {K : SSet.{0}} {X : TopCat.{0}} {x y : X}
    (f : K ⟶ TopCat.toSSet.obj (TopCat.of (Path x y))) :
    internalToFixedPath (fixedPathToInternal f) = f := by
  apply (sSetTopAdj.homEquiv K _).symm.injective
  unfold internalToFixedPath
  rw [Equiv.symm_apply_apply]
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro z
  apply Path.ext
  funext t
  change evaluateSingularCylinder
    (internalPathCylinder (fixedPathToInternal f ≫ (fixedInternalPathSubcomplex _ _ _).ι))
      (t, z) = _
  rw [fixedPathToInternal, fixedInternalPathsLift_ι,
    internalPathCylinder_transpose, fixedPathCylinder_evaluate]

theorem internalToFixedPath_cylinder {K : SSet.{0}} {X : TopCat.{0}} {x y : X}
    (a : K ⟶ fixedInternalPaths (TopCat.toSSet.obj X)
      (TopCat.toSSetObj₀Equiv.symm x) (TopCat.toSSetObj₀Equiv.symm y)) :
    fixedPathCylinder (internalToFixedPath a) =
      internalPathCylinder (a ≫ (fixedInternalPathSubcomplex _ _ _).ι) := by
  apply evaluateSingularCylinder_injective
  apply ContinuousMap.ext
  rintro ⟨t, z⟩
  rw [fixedPathCylinder_evaluate]
  unfold internalToFixedPath
  rw [Equiv.symm_apply_apply]
  rfl

theorem fixedPathToInternal_right_inverse {K : SSet.{0}} {X : TopCat.{0}} {x y : X}
    (a : K ⟶ fixedInternalPaths (TopCat.toSSet.obj X)
      (TopCat.toSSetObj₀Equiv.symm x) (TopCat.toSSetObj₀Equiv.symm y)) :
    fixedPathToInternal (internalToFixedPath a) = a := by
  apply (cancel_mono (fixedInternalPathSubcomplex _ _ _).ι).mp
  rw [fixedPathToInternal, fixedInternalPathsLift_ι]
  apply internalPathCylinder_injective
  rw [internalPathCylinder_transpose, internalToFixedPath_cylinder]

/-- This is an isomorphism of hom sets, not merely a bijection of components. -/
def fixedPathInternalEquiv (K : SSet.{0}) (X : TopCat.{0}) (x y : X) :
    (K ⟶ TopCat.toSSet.obj (TopCat.of (Path x y))) ≃
      (K ⟶ fixedInternalPaths (TopCat.toSSet.obj X)
        (TopCat.toSSetObj₀Equiv.symm x) (TopCat.toSSetObj₀Equiv.symm y)) where
  toFun := fixedPathToInternal
  invFun := internalToFixedPath
  left_inv := internalToFixedPath_left_inverse
  right_inv := fixedPathToInternal_right_inverse

theorem fixedPathToInternal_naturality {A K : SSet.{0}} {X : TopCat.{0}} {x y : X}
    (i : A ⟶ K) (f : K ⟶ TopCat.toSSet.obj (TopCat.of (Path x y))) :
    fixedPathToInternal (i ≫ f) = i ≫ fixedPathToInternal f := by
  apply (cancel_mono (fixedInternalPathSubcomplex _ _ _).ι).mp
  rw [Category.assoc, fixedPathToInternal, fixedInternalPathsLift_ι]
  apply internalPathCylinder_injective
  rw [internalPathCylinder_transpose, fixedPathCylinder_naturality,
    internalPathCylinder_naturality, fixedPathToInternal, fixedInternalPathsLift_ι,
    internalPathCylinder_transpose]

/-- The singular complex of the genuine fixed-endpoint path space is the
actual fixed-endpoint subcomplex of the simplicial internal hom. -/
def fixedPathInternalIso (X : TopCat.{0}) (x y : X) :
    TopCat.toSSet.obj (TopCat.of (Path x y)) ≅
      fixedInternalPaths (TopCat.toSSet.obj X)
        (TopCat.toSSetObj₀Equiv.symm x) (TopCat.toSSetObj₀Equiv.symm y) :=
  Yoneda.ext _ _ (fun {_} => fixedPathInternalEquiv _ X x y)
    (fun {_} => (fixedPathInternalEquiv _ X x y).symm)
    (fun _ => Equiv.symm_apply_apply _ _) (fun _ => Equiv.apply_symm_apply _ _)
    (fun i f => fixedPathToInternal_naturality i f)

end

end Thomason.Construction

end

section

/-! # Singular Kan lifting on fixed-endpoint path spaces -/

namespace Thomason.Construction

open CategoryTheory MonoidalCategory
open SSet.modelCategoryQuillen
open scoped Simplicial

noncomputable section

/-- Passing to paths with prescribed endpoints preserves lifting against
every anodyne parameter inclusion. -/
theorem fixedPath_singular_lifting {A K : SSet.{0}} (i : A ⟶ K)
    (hi : SSet.anodyneExtensions i) {X Y : TopCat.{0}} (p : X ⟶ Y)
    [HomotopicalAlgebra.Fibration (TopCat.toSSet.map p)] (x y : X) :
    HasLiftingProperty i (TopCat.toSSet.map
      (TopCat.ofHom (PathSpace.map p.hom (x := x) (y := y)))) := by
  refine ⟨fun {a b} sq => ?_⟩
  have hab : fixedPathCylinder a ≫ TopCat.toSSet.map p =
      i ▷ Δ[1] ≫ fixedPathCylinder b := by
    rw [← fixedPathCylinder_postcomp, ← fixedPathCylinder_naturality, sq.w]
  have hb₀ : SSet.ι₀ ≫ fixedPathCylinder b =
      SSet.const ((TopCat.toSSet.map p).app _ (TopCat.toSSetObj₀Equiv.symm x)) := by
    rw [fixedPathCylinder_zero]
    rfl
  have hb₁ : SSet.ι₁ ≫ fixedPathCylinder b =
      SSet.const ((TopCat.toSSet.map p).app _ (TopCat.toSSetObj₀Equiv.symm y)) := by
    rw [fixedPathCylinder_one]
    rfl
  obtain ⟨e, hei, hep, he₀, he₁⟩ := exists_kan_fixed_endpoint_lift i hi
    (TopCat.toSSet.map p) (TopCat.toSSetObj₀Equiv.symm x)
    (TopCat.toSSetObj₀Equiv.symm y) (fixedPathCylinder a) (fixedPathCylinder b)
    (fixedPathCylinder_zero a) (fixedPathCylinder_one a) hb₀ hb₁ hab
  let E := fixedPathRealization e he₀ he₁
  let l := sSetTopAdj.homEquiv K (TopCat.of (Path x y)) E
  refine ⟨⟨{ l := l, fac_left := ?_, fac_right := ?_ }⟩⟩
  · apply (sSetTopAdj.homEquiv A _).symm.injective
    rw [sSetTopAdj.homEquiv_naturality_left_symm]
    dsimp only [l]
    rw [Equiv.symm_apply_apply]
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro z
    apply Path.ext
    funext t
    change evaluateSingularCylinder e (t, (SSet.toTop.map i).hom z) =
      ((sSetTopAdj.homEquiv A _).symm a).hom z t
    rw [evaluateSingularCylinder_naturality, hei, fixedPathCylinder_evaluate]
  · apply (sSetTopAdj.homEquiv K _).symm.injective
    rw [sSetTopAdj.homEquiv_naturality_right_symm]
    dsimp only [l]
    rw [Equiv.symm_apply_apply]
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro z
    apply Path.ext
    funext t
    change p.hom (evaluateSingularCylinder e (t, z)) =
      ((sSetTopAdj.homEquiv K _).symm b).hom z t
    rw [← evaluateSingularCylinder_postcomp, hep, fixedPathCylinder_evaluate]

/-- The actual map on fixed-endpoint path spaces is a singular Kan fibration. -/
theorem fixedPath_singular_fibration {X Y : TopCat.{0}} (p : X ⟶ Y)
    [HomotopicalAlgebra.Fibration (TopCat.toSSet.map p)] (x y : X) :
    HomotopicalAlgebra.Fibration (TopCat.toSSet.map
      (TopCat.ofHom (PathSpace.map p.hom (x := x) (y := y)))) := by
  rw [fibration_iff]
  intro A K i hi
  apply fixedPath_singular_lifting i _ p x y
  rw [SSet.anodyneExtensions_eq_llp_rlp]
  exact MorphismProperty.le_llp_rlp _ _ hi

end

end Thomason.Construction

end

section

/-! # Exact lifting of based cubical homotopies in every dimension -/

namespace Thomason.Construction

open CategoryTheory
open SSet.modelCategoryQuillen

noncomputable section

/-- A singular Kan fibration which is an actual weak equivalence lifts based
cubical homotopies with both endpoint cubes and the entire boundary fixed. -/
theorem singular_fibration_lift_based_homotopy (n : ℕ) {X Y : TopCat.{0}}
    (p : X ⟶ Y) [HomotopicalAlgebra.Fibration (TopCat.toSSet.map p)]
    (hp : IsWeakHomotopyEquivalence p.hom) {x : X}
    (a b : GenLoop (Fin n) X x)
    (H : (HomotopyMaps.loopMap p.hom a).val.HomotopyRel
      (HomotopyMaps.loopMap p.hom b).val (Cube.boundary (Fin n))) :
    ∃ F : a.val.HomotopyRel b.val (Cube.boundary (Fin n)),
      ∀ z, p.hom (F z) = H z := by
  induction n generalizing X Y with
  | zero =>
    let t₀ : Fin 0 → unitInterval := fun i => Fin.elim0 i
    let γ : Path (p.hom (a t₀)) (p.hom (b t₀)) := {
      toFun s := H (s, t₀)
      continuous_toFun := H.continuous.comp (by fun_prop)
      source' := H.apply_zero t₀
      target' := H.apply_one t₀ }
    obtain ⟨q, hq⟩ := singular_fibration_lift_path_endpoints p hp γ
    let F : a.val.HomotopyRel b.val (Cube.boundary (Fin 0)) := {
      toFun z := q z.1
      continuous_toFun := q.continuous.comp continuous_fst
      map_zero_left t := q.source.trans (congrArg a (Subsingleton.elim _ _))
      map_one_left t := q.target.trans (congrArg b (Subsingleton.elim _ _))
      prop' _ _ ht := by obtain ⟨i, _⟩ := ht; exact Fin.elim0 i }
    refine ⟨F, fun z => ?_⟩
    exact (hq z.1).trans (congrArg (fun t => H (z.1, t)) (Subsingleton.elim _ _))
  | succ n ih =>
    let P : TopCat.of (Path x x) ⟶ TopCat.of (Path (p.hom x) (p.hom x)) :=
      TopCat.ofHom (PathSpace.map p.hom)
    let : HomotopicalAlgebra.Fibration (TopCat.toSSet.map P) :=
      fixedPath_singular_fibration p x x
    have hP : IsWeakHomotopyEquivalence P.hom := PathSpace.map_weak p.hom hp x x
    let Hc : (HomotopyMaps.loopMap P.hom (HomotopyMaps.curryLoop a)).val.HomotopyRel
        (HomotopyMaps.loopMap P.hom (HomotopyMaps.curryLoop b)).val
        (Cube.boundary (Fin n)) := HomotopyMaps.curryLoopHomotopy H
    obtain ⟨F, hF⟩ := ih P hP (HomotopyMaps.curryLoop a) (HomotopyMaps.curryLoop b) Hc
    let F' : a.val.HomotopyRel b.val (Cube.boundary (Fin (n+1))) :=
      (HomotopyMaps.uncurryLoopHomotopy F).cast
        (congrArg Subtype.val (HomotopyMaps.uncurry_curryLoop a))
        (congrArg Subtype.val (HomotopyMaps.uncurry_curryLoop b))
    refine ⟨F', fun z => ?_⟩
    have he := congrArg (fun q : Path (p.hom x) (p.hom x) => q (z.2 0))
      (hF (z.1, Fin.tail z.2))
    dsimp only [P, PathSpace.map, Hc, HomotopyMaps.curryLoopHomotopy] at he
    change p.hom (F (z.1, Fin.tail z.2) (z.2 0)) =
      H (z.1, Fin.cons (z.2 0) (Fin.tail z.2)) at he
    rw [Fin.cons_self_tail] at he
    exact he

/-- The same exact relative homotopy lift under the singular realization test. -/
theorem singular_acyclic_lift_based_homotopy (n : ℕ) {X Y : TopCat.{0}}
    (p : X ⟶ Y) [HomotopicalAlgebra.Fibration (TopCat.toSSet.map p)]
    (hp : realizationWeakEquivalences (TopCat.toSSet.map p)) {x : X}
    (a b : GenLoop (Fin n) X x)
    (H : (HomotopyMaps.loopMap p.hom a).val.HomotopyRel
      (HomotopyMaps.loopMap p.hom b).val (Cube.boundary (Fin n))) :
    ∃ F : a.val.HomotopyRel b.val (Cube.boundary (Fin n)),
      ∀ z, p.hom (F z) = H z :=
  singular_fibration_lift_based_homotopy n p (singular_realization_reflects_weak p hp) a b H

end

end Thomason.Construction

end

section

/-! # Actual fibres of singular acyclic fibrations are weakly contractible -/

namespace Thomason.Construction

open CategoryTheory
open SSet.modelCategoryQuillen

noncomputable section

theorem singular_fibration_fiber_nonempty {X Y : TopCat.{0}} (p : X ⟶ Y)
    [HomotopicalAlgebra.Fibration (TopCat.toSSet.map p)]
    (hp : IsWeakHomotopyEquivalence p.hom) (y : Y) :
    Nonempty {x : X // p.hom x = y} := by
  obtain ⟨x, hx⟩ := singular_fibration_surjective_of_weak p hp y
  exact ⟨⟨x, hx⟩⟩

theorem singular_fibration_fiber_joined {X Y : TopCat.{0}} (p : X ⟶ Y)
    [HomotopicalAlgebra.Fibration (TopCat.toSSet.map p)]
    (hp : IsWeakHomotopyEquivalence p.hom) (y : Y)
    (a b : {x : X // p.hom x = y}) : Joined a b := by
  let γ : Path (p.hom a.val) (p.hom b.val) := {
    toFun _ := y
    continuous_toFun := continuous_const
    source' := a.property.symm
    target' := b.property.symm }
  obtain ⟨q, hq⟩ := singular_fibration_lift_path_endpoints p hp γ
  exact ⟨{
    toFun t := ⟨q t, hq t⟩
    continuous_toFun := q.continuous.subtype_mk _
    source' := Subtype.ext q.source
    target' := Subtype.ext q.target }⟩

/-- Every based cubical map into a point fibre has a nullhomotopy inside
that same fibre, relative to the complete cubical boundary. -/
theorem singular_fibration_fiber_nullhomotopy {X Y : TopCat.{0}} (p : X ⟶ Y)
    [HomotopicalAlgebra.Fibration (TopCat.toSSet.map p)]
    (hp : IsWeakHomotopyEquivalence p.hom) (y : Y)
    (x : {z : X // p.hom z = y}) (n : ℕ)
    (a : GenLoop (Fin n) {z : X // p.hom z = y} x) :
    Nonempty (a.val.HomotopyRel (ContinuousMap.const _ x) (Cube.boundary (Fin n))) := by
  let inc : C({z : X // p.hom z = y}, X) := ⟨Subtype.val, continuous_subtype_val⟩
  let b : GenLoop (Fin n) X x.val := ⟨ContinuousMap.const _ x.val, fun _ _ => rfl⟩
  let H : (HomotopyMaps.loopMap p.hom (HomotopyMaps.loopMap inc a)).val.HomotopyRel
      (HomotopyMaps.loopMap p.hom b).val (Cube.boundary (Fin n)) := {
    toFun _ := p.hom x.val
    continuous_toFun := continuous_const
    map_zero_left t := x.property.trans (a t).property.symm
    map_one_left _ := rfl
    prop' _ t _ := x.property.trans (a t).property.symm }
  obtain ⟨F, hF⟩ := singular_fibration_lift_based_homotopy n p hp
    (HomotopyMaps.loopMap inc a) b H
  exact ⟨{
    toFun z := ⟨F z, (hF z).trans x.property⟩
    continuous_toFun := F.continuous.subtype_mk _
    map_zero_left t := Subtype.ext (F.apply_zero t)
    map_one_left t := Subtype.ext (F.apply_one t)
    prop' s t ht := Subtype.ext (F.eq_fst s ht) }⟩

/-- The fibre has a single component. -/
theorem singular_fibration_fiber_components_subsingleton {X Y : TopCat.{0}} (p : X ⟶ Y)
    [HomotopicalAlgebra.Fibration (TopCat.toSSet.map p)]
    (hp : IsWeakHomotopyEquivalence p.hom) (y : Y) :
    Subsingleton (ZerothHomotopy {x : X // p.hom x = y}) := by
  constructor
  intro a b
  induction a using ZerothHomotopy.rec with
  | mk a =>
    induction b using ZerothHomotopy.rec with
    | mk b => exact Quotient.sound (singular_fibration_fiber_joined p hp y a b)

/-- Every based homotopy group of the fibre is trivial, including degree zero
in the cubical quotient convention. -/
theorem singular_fibration_fiber_groups_subsingleton {X Y : TopCat.{0}} (p : X ⟶ Y)
    [HomotopicalAlgebra.Fibration (TopCat.toSSet.map p)]
    (hp : IsWeakHomotopyEquivalence p.hom) (y : Y)
    (x : {z : X // p.hom z = y}) (n : ℕ) :
    Subsingleton (HomotopyGroup.Pi n {z : X // p.hom z = y} x) := by
  constructor
  intro a b
  induction a using Quotient.inductionOn with
  | h a =>
    induction b using Quotient.inductionOn with
    | h b =>
      obtain ⟨ha⟩ := singular_fibration_fiber_nullhomotopy p hp y x n a
      obtain ⟨hb⟩ := singular_fibration_fiber_nullhomotopy p hp y x n b
      let c : GenLoop (Fin n) {z : X // p.hom z = y} x :=
        ⟨ContinuousMap.const _ x, fun _ _ => rfl⟩
      exact (Quotient.sound (show GenLoop.Homotopic a c from ⟨ha⟩)).trans
        (Quotient.sound (show GenLoop.Homotopic b c from ⟨hb⟩)).symm

/-- The map from each actual point fibre to a point is a weak homotopy
equivalence, with no assumption about a singular counit. -/
theorem singular_fibration_fiber_weak {X Y : TopCat.{0}} (p : X ⟶ Y)
    [HomotopicalAlgebra.Fibration (TopCat.toSSet.map p)]
    (hp : IsWeakHomotopyEquivalence p.hom) (y : Y) :
    IsWeakHomotopyEquivalence
      (ContinuousMap.const {x : X // p.hom x = y} ()) := by
  let := singular_fibration_fiber_components_subsingleton p hp y
  let x := (singular_fibration_fiber_nonempty p hp y).some
  constructor
  · exact ⟨fun _ _ _ => Subsingleton.elim _ _, fun b =>
      ⟨ZerothHomotopy.mk x, Subsingleton.elim _ _⟩⟩
  · intro n a
    let := singular_fibration_fiber_groups_subsingleton p hp y a (n+1)
    let c : GenLoop (Fin (n+1)) {x : X // p.hom x = y} a :=
      ⟨ContinuousMap.const _ a, fun _ _ => rfl⟩
    refine ⟨fun _ _ _ => Subsingleton.elim _ _, fun b => ⟨Quotient.mk _ c, ?_⟩⟩
    induction b using Quotient.inductionOn with
    | h b =>
      apply congrArg (Quotient.mk _)
      apply GenLoop.ext
      intro t
      exact Subsingleton.elim _ _

theorem singular_acyclic_fiber_weak {X Y : TopCat.{0}} (p : X ⟶ Y)
    [HomotopicalAlgebra.Fibration (TopCat.toSSet.map p)]
    (hp : realizationWeakEquivalences (TopCat.toSSet.map p)) (y : Y) :
    IsWeakHomotopyEquivalence (ContinuousMap.const {x : X // p.hom x = y} ()) :=
  singular_fibration_fiber_weak p (singular_realization_reflects_weak p hp) y

end

end Thomason.Construction

end

end OAI
