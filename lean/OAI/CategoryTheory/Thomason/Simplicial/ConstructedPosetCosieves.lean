import OAI.CategoryTheory.Thomason.Simplicial.ExhaustionWeakEquivalence
import OAI.CategoryTheory.Thomason.Simplicial.FinitePosetCoordinates
import OAI.CategoryTheory.Thomason.Simplicial.HornWeakEquivalences
import OAI.CategoryTheory.Thomason.Simplicial.RealizationCellClosure
import OAI.CategoryTheory.Thomason.Simplicial.SingularCounitSurjectivity
import OAI.CategoryTheory.Thomason.Simplicial.SingularKanComplex
import OAI.CategoryTheory.Thomason.Simplicial.SingularPathSpaceAdjunction
import OAI.CategoryTheory.Thomason.Simplicial.TerminalConeUniversal
import OAI.CategoryTheory.Thomason.Simplicial.TruncationQuotientComposition
import OAI.CategoryTheory.Thomason.Simplicial.WeakPathSurjectivity
import OAI.CategoryTheory.Thomason.Strict.UnderlyingCategory
import OAI.CategoryTheory.Thomason.Transfer.StrictPushoutGeneration
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.Data.Fin.Rev

namespace OAI

section

/-! # Acyclic singular fibrations lift paths with both endpoints prescribed -/

namespace Thomason.Construction

open CategoryTheory Convexity
open SSet.modelCategoryQuillen

noncomputable section

/-- A weak continuous map whose singular map is Kan lifts paths with arbitrary
prescribed endpoints in their fibres. The projection of the lift is exactly
the given path, not just its homotopy class. -/
theorem singular_fibration_lift_path_endpoints {X Y : TopCat.{0}} (p : X ⟶ Y)
    [HomotopicalAlgebra.Fibration (TopCat.toSSet.map p)]
    (hp : IsWeakHomotopyEquivalence p.hom) {x₀ x₁ : X}
    (γ : Path (p.hom x₀) (p.hom x₁)) :
    ∃ q : Path x₀ x₁, ∀ t, p.hom (q t) = γ t := by
  obtain ⟨α, ⟨Hα⟩⟩ := weak_path_homotopy_surjective p.hom hp γ
  let f : C(Fin 1 → unitInterval, X) :=
    ⟨fun u => α (u 0), α.continuous.comp (continuous_apply 0)⟩
  let a : C(unitInterval × Cube.boundary (Fin 1), X) :=
    ⟨fun u => α (u.2.val 0), α.continuous.comp
      ((continuous_apply 0).comp (continuous_subtype_val.comp continuous_snd))⟩
  let H : C(unitInterval × (Fin 1 → unitInterval), Y) :=
    ⟨fun u => Hα (u.1, u.2 0), Hα.continuous.comp
      (continuous_fst.prodMk ((continuous_apply 0).comp continuous_snd))⟩
  have ha₀ : ∀ x : Cube.boundary (Fin 1), a (0, x) = f x.val := fun _ => rfl
  have hap : ∀ t (x : Cube.boundary (Fin 1)), p.hom (a (t, x)) = H (t, x.val) := by
    intro t x
    obtain ⟨i, hi⟩ := x.property
    have hi₀ : i = 0 := Subsingleton.elim _ _
    subst i
    change p.hom (α (x.val 0)) = Hα (t, x.val 0)
    rcases hi with hi | hi
    · rw [hi, α.source, Hα.source]
    · rw [hi, α.target, Hα.target]
  have hf₀ : ∀ x, p.hom (f x) = H (0, x) := by
    intro x
    exact (Hα.map_zero_left (x 0)).symm
  obtain ⟨F, _, hFa, hFp⟩ := RealizedCube.singular_fibration_cube_lifting
    p 0 f a H ha₀ hap hf₀
  let q : Path x₀ x₁ := {
    toFun t := F (1, fun _ => t)
    continuous_toFun := F.continuous.comp (by fun_prop)
    source' := by
      have he := hFa 1 ⟨fun _ => 0, ⟨0, Or.inl rfl⟩⟩
      exact he.trans α.source
    target' := by
      have he := hFa 1 ⟨fun _ => 1, ⟨0, Or.inr rfl⟩⟩
      exact he.trans α.target }
  refine ⟨q, fun t => ?_⟩
  exact (hFp 1 (fun _ => t)).trans (Hα.map_one_left t)

/-- The endpoint-preserving lift applies directly to the actual simplicial
weak-equivalence hypothesis on a singular Kan fibration. -/
theorem singular_acyclic_lift_path_endpoints {X Y : TopCat.{0}} (p : X ⟶ Y)
    [HomotopicalAlgebra.Fibration (TopCat.toSSet.map p)]
    (hp : realizationWeakEquivalences (TopCat.toSSet.map p)) {x₀ x₁ : X}
    (γ : Path (p.hom x₀) (p.hom x₁)) :
    ∃ q : Path x₀ x₁, ∀ t, p.hom (q t) = γ t :=
  singular_fibration_lift_path_endpoints p (singular_realization_reflects_weak p hp) γ

end

end Thomason.Construction

end

section

/-! # Exact based cubical lifting in every positive dimension

Surjectivity of the actual homotopy-group map first supplies a lift up to
homotopy relative to the entire boundary. The relative Kan cylinder lift then
corrects its projection without moving that boundary. This is the
constant-boundary case of acyclic boundary lifting, in all dimensions.
-/

namespace Thomason.Construction

open CategoryTheory Convexity
open SSet.modelCategoryQuillen

noncomputable section

/-- A weak continuous map with singular Kan lifting lifts every based cube
exactly, keeping the entire boundary at the prescribed point. -/
theorem singular_fibration_lift_based_cube {X Y : TopCat.{0}} (p : X ⟶ Y)
    [HomotopicalAlgebra.Fibration (TopCat.toSSet.map p)]
    (hp : IsWeakHomotopyEquivalence p.hom) (x : X) (n : ℕ)
    (γ : GenLoop (Fin (n+1)) Y (p.hom x)) :
    ∃ q : GenLoop (Fin (n+1)) X x, ∀ t, p.hom (q t) = γ t := by
  obtain ⟨a, ha⟩ := (hp.2 n x).2 (Quotient.mk _ γ)
  induction a using Quotient.inductionOn with
  | h α =>
    obtain ⟨H⟩ : GenLoop.Homotopic (HomotopyMaps.loopMap p.hom α) γ :=
      Quotient.exact ha
    let a : C(unitInterval × Cube.boundary (Fin (n+1)), X) :=
      ContinuousMap.const _ x
    have ha₀ : ∀ z : Cube.boundary (Fin (n+1)), a (0, z) = α z.val := by
      intro z
      exact (α.property z.val z.property).symm
    have hap : ∀ t (z : Cube.boundary (Fin (n+1))),
        p.hom (a (t, z)) = H (t, z.val) := by
      intro t z
      exact ((H.eq_fst t z.property).trans
        (congrArg p.hom (α.property z.val z.property))).symm
    have hf₀ : ∀ z, p.hom (α z) = H (0, z) := by
      intro z
      exact (H.apply_zero z).symm
    obtain ⟨F, _, hFa, hFp⟩ := RealizedCube.singular_fibration_cube_lifting
      p n α.val a H.toContinuousMap ha₀ hap hf₀
    let q : GenLoop (Fin (n+1)) X x :=
      ⟨⟨fun z => F (1, z), F.continuous.comp (continuous_const.prodMk continuous_id)⟩,
        fun z hz => hFa 1 ⟨z, hz⟩⟩
    refine ⟨q, fun z => ?_⟩
    exact (hFp 1 z).trans (H.apply_one z)

/-- The actual realization weak-equivalence test on a singular Kan fibration
already suffices for exact based cube lifting in every dimension. -/
theorem singular_acyclic_lift_based_cube {X Y : TopCat.{0}} (p : X ⟶ Y)
    [HomotopicalAlgebra.Fibration (TopCat.toSSet.map p)]
    (hp : realizationWeakEquivalences (TopCat.toSSet.map p)) (x : X) (n : ℕ)
    (γ : GenLoop (Fin (n+1)) Y (p.hom x)) :
    ∃ q : GenLoop (Fin (n+1)) X x, ∀ t, p.hom (q t) = γ t :=
  singular_fibration_lift_based_cube p (singular_realization_reflects_weak p hp) x n γ

end

end Thomason.Construction

end

section

/-! # Simplicial cubical boundary lifting with a prescribed constant boundary

This is a statement about the actual singular simplicial map. Its boundary
condition covers the complete cubical subcomplex in every positive dimension.
-/

namespace Thomason.Construction.RealizedCube

open CategoryTheory
open SSet.modelCategoryQuillen

noncomputable section

theorem singularMap_boundary_comp {X : TopCat.{0}} {x : X} (n : ℕ)
    (q : GenLoop (Fin (n+1)) X x) :
    (boundary n).ι ≫ singularMap (n+1) q.val =
      SSet.const (TopCat.toSSetObj₀Equiv.symm x) := by
  change (boundary n).ι ≫ sSetTopAdj.homEquiv _ _
    (TopCat.ofHom (q.val.comp (coordinates (n+1)))) = _
  rw [← sSetTopAdj.homEquiv_naturality_left]
  rw [← singular_adjoint_const]
  congr 1
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro z
  exact q.property _ (coordinates_boundary n z)

/-- A singular Kan fibration which is an actual topological weak equivalence
fills every cubical boundary diagram whose top map is the specified constant. -/
theorem singular_fibration_constant_boundary_lift {X Y : TopCat.{0}} (p : X ⟶ Y)
    [HomotopicalAlgebra.Fibration (TopCat.toSSet.map p)]
    (hp : IsWeakHomotopyEquivalence p.hom) (x : X) (n : ℕ)
    (b : obj (n+1) ⟶ TopCat.toSSet.obj Y)
    (hb : (boundary n).ι ≫ b = SSet.const (TopCat.toSSetObj₀Equiv.symm (p.hom x))) :
    ∃ l : obj (n+1) ⟶ TopCat.toSSet.obj X,
      (boundary n).ι ≫ l = SSet.const (TopCat.toSSetObj₀Equiv.symm x) ∧
      l ≫ TopCat.toSSet.map p = b := by
  let B := (sSetTopAdj.homEquiv _ Y).symm b
  have hB : SSet.toTop.map (boundary n).ι ≫ B = TopCat.const (p.hom x) := by
    apply (sSetTopAdj.homEquiv _ Y).injective
    rw [sSetTopAdj.homEquiv_naturality_left, singular_adjoint_const]
    simpa only [B, Equiv.apply_symm_apply] using hb
  let γ : GenLoop (Fin (n+1)) Y (p.hom x) :=
    ⟨B.hom.comp (sectionMap (n+1)), fun t ht => by
      change B.hom (sectionMap (n+1) t) = p.hom x
      rw [← boundarySection_inclusion n ⟨t, ht⟩]
      exact congrArg (fun f => f.hom (boundarySection n ⟨t, ht⟩)) hB⟩
  obtain ⟨q, hq⟩ := singular_fibration_lift_based_cube p hp x n γ
  refine ⟨singularMap (n+1) q.val, singularMap_boundary_comp n q, ?_⟩
  change sSetTopAdj.homEquiv _ _ (TopCat.ofHom (q.val.comp (coordinates (n+1)))) ≫
    TopCat.toSSet.map p = b
  rw [← sSetTopAdj.homEquiv_naturality_right]
  apply (sSetTopAdj.homEquiv _ Y).symm.injective
  rw [Equiv.symm_apply_apply]
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro z
  change p.hom (q (coordinates (n+1) z)) = B.hom z
  rw [hq]
  change B.hom (sectionMap (n+1) (coordinates (n+1) z)) = B.hom z
  rw [section_coordinates]

/-- The same all-dimensional boundary lift from the actual simplicial weak test. -/
theorem singular_acyclic_constant_boundary_lift {X Y : TopCat.{0}} (p : X ⟶ Y)
    [HomotopicalAlgebra.Fibration (TopCat.toSSet.map p)]
    (hp : realizationWeakEquivalences (TopCat.toSSet.map p)) (x : X) (n : ℕ)
    (b : obj (n+1) ⟶ TopCat.toSSet.obj Y)
    (hb : (boundary n).ι ≫ b = SSet.const (TopCat.toSSetObj₀Equiv.symm (p.hom x))) :
    ∃ l : obj (n+1) ⟶ TopCat.toSSet.obj X,
      (boundary n).ι ≫ l = SSet.const (TopCat.toSSetObj₀Equiv.symm x) ∧
      l ≫ TopCat.toSSet.map p = b :=
  singular_fibration_constant_boundary_lift p (singular_realization_reflects_weak p hp)
    x n b hb

end

end Thomason.Construction.RealizedCube

end

section

/-! # Boundary lifting in dimension one for actual singular acyclic fibrations -/

namespace Thomason.Construction

open CategoryTheory Convexity
open SSet.modelCategoryQuillen

noncomputable section

/-- A weak map with singular Kan lifting solves every lifting problem for the
ordinary interval and its two endpoints. -/
theorem singular_fibration_interval_boundary_lifting {X Y : TopCat.{0}}
    (p : X ⟶ Y) [HomotopicalAlgebra.Fibration (TopCat.toSSet.map p)]
    (hp : IsWeakHomotopyEquivalence p.hom) :
    HasLiftingProperty (RealizedCube.boundaryInclusion 0) p := by
  refine ⟨fun {a b} sq => ?_⟩
  let z₀ : Cube.boundary (Fin 1) := ⟨fun _ => 0, ⟨0, Or.inl rfl⟩⟩
  let z₁ : Cube.boundary (Fin 1) := ⟨fun _ => 1, ⟨0, Or.inr rfl⟩⟩
  have hc (z : Cube.boundary (Fin 1)) : p.hom (a.hom z) = b.hom z.val :=
    congrArg (fun f => f.hom z) sq.w
  let γ : Path (p.hom (a.hom z₀)) (p.hom (a.hom z₁)) := {
    toFun t := b.hom (fun _ => t)
    continuous_toFun := b.hom.continuous.comp (by fun_prop)
    source' := (hc z₀).symm
    target' := (hc z₁).symm }
  obtain ⟨q, hq⟩ := singular_fibration_lift_path_endpoints p hp γ
  let l : TopCat.of (Fin 1 → unitInterval) ⟶ X :=
    TopCat.ofHom ⟨fun u => q (u 0), q.continuous.comp (continuous_apply 0)⟩
  refine ⟨⟨{ l := l, fac_left := ?_, fac_right := ?_ }⟩⟩
  · apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro z
    have hz : z.val 0 = 0 ∨ z.val 0 = 1 := by
      obtain ⟨i, hi⟩ := z.property
      simpa only [show i = 0 from @Subsingleton.elim (Fin 1) inferInstance _ _] using hi
    rcases hz with hz | hz
    · have he : z = z₀ := by
        apply Subtype.ext
        funext i
        simpa only [show i = 0 from @Subsingleton.elim (Fin 1) inferInstance _ _] using hz
      subst z
      exact q.source
    · have he : z = z₁ := by
        apply Subtype.ext
        funext i
        simpa only [show i = 0 from @Subsingleton.elim (Fin 1) inferInstance _ _] using hz
      subst z
      exact q.target
  · apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro u
    change p.hom (q (u 0)) = b.hom u
    rw [hq]
    change b.hom (fun _ => u 0) = b.hom u
    congr 1
    funext i
    exact congrArg u (@Subsingleton.elim (Fin 1) inferInstance 0 i)

/-- The same boundary lift under the actual realization weak-equivalence
hypothesis on the singular map. -/
theorem singular_acyclic_interval_boundary_lifting {X Y : TopCat.{0}}
    (p : X ⟶ Y) [HomotopicalAlgebra.Fibration (TopCat.toSSet.map p)]
    (hp : realizationWeakEquivalences (TopCat.toSSet.map p)) :
    HasLiftingProperty (RealizedCube.boundaryInclusion 0) p :=
  singular_fibration_interval_boundary_lifting p (singular_realization_reflects_weak p hp)

end

end Thomason.Construction

end

section

/-! # The full one-simplex boundary lifting case for singular acyclic fibrations -/

namespace Thomason.Construction

open CategoryTheory Convexity
open SSet.modelCategoryQuillen

noncomputable section

def intervalOneCube : unitInterval ≃ₜ (Fin 1 → unitInterval) where
  toFun t := fun _ => t
  invFun u := u 0
  left_inv _ := rfl
  right_inv u := by funext i; exact congrArg u (@Subsingleton.elim (Fin 1) inferInstance 0 i)
  continuous_toFun := by fun_prop
  continuous_invFun := continuous_apply 0

def simplexOneCube : StdSimplex ℝ (Fin 2) ≃ₜ (Fin 1 → unitInterval) :=
  StdSimplex.homeomorphI.trans intervalOneCube

theorem simplexOneCube_boundary (s : StdSimplex ℝ (Fin 2)) :
    s ∈ RealizationPrism.boundaryLocus 1 ↔
      simplexOneCube s ∈ Cube.boundary (Fin 1) := by
  have hsum : s.weights 0 + s.weights 1 = 1 := by
    have h := s.total
    rw [Finsupp.sum_fintype _ _ (by intro; rfl)] at h
    simpa only [Fin.sum_univ_two] using h
  change (∃ i, s.weights i = 0) ↔
    ∃ i : Fin 1, StdSimplex.homeomorphI s = 0 ∨ StdSimplex.homeomorphI s = 1
  constructor
  · rintro ⟨i, hi⟩
    refine ⟨0, ?_⟩
    fin_cases i
    · right
      change s.weights 0 = 0 at hi
      apply Subtype.ext
      change s.weights 1 = 1
      linarith
    · left
      change s.weights 1 = 0 at hi
      apply Subtype.ext
      exact hi
  · rintro ⟨_, h | h⟩
    · exact ⟨1, congrArg Subtype.val h⟩
    · refine ⟨0, ?_⟩
      have ht : s.weights 1 = 1 := congrArg Subtype.val h
      linarith

def simplexOneBoundaryArrowIso :
    Arrow.mk (RealizationPrism.boundaryInclusion 1) ≅
      Arrow.mk (RealizedCube.boundaryInclusion 0) :=
  Arrow.isoMk' _ _
    (TopCat.isoOfHomeo (simplexOneCube.subtype simplexOneCube_boundary))
    (TopCat.isoOfHomeo simplexOneCube) (by rfl)

/-- This is the entire simplicial `∂Δ[1]` lifting problem, with arbitrary
specified endpoints, for an actual singular Kan fibration satisfying W. -/
theorem singular_acyclic_boundary_one {X Y : TopCat.{0}} (p : X ⟶ Y)
    [HomotopicalAlgebra.Fibration (TopCat.toSSet.map p)]
    (hp : realizationWeakEquivalences (TopCat.toSSet.map p)) :
    HasLiftingProperty (SSet.boundary 1).ι (TopCat.toSSet.map p) := by
  apply (RealizationPrism.singular_boundary_lifting_iff p 1).mpr
  exact (HasLiftingProperty.iff_of_arrow_iso_left simplexOneBoundaryArrowIso p).mpr
    (singular_acyclic_interval_boundary_lifting p hp)

end

end Thomason.Construction

end

section

/-! # Weak equivalences reflect homotopies of paths with fixed endpoints -/

namespace Thomason.Construction

open CategoryTheory

noncomputable section

theorem fundamentalGroup_map_injective {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (f : C(X, Y)) (x : X)
    (hf : Function.Injective (HomotopyMaps.groupMap f 1 x)) :
    Function.Injective (FundamentalGroup.map f x) := by
  intro a b h
  apply HomotopyGroup.pi1EquivFundamentalGroup.symm.injective
  apply hf
  apply HomotopyGroup.pi1EquivFundamentalGroup.injective
  simpa only [HomotopyMaps.piOneEquiv_naturality, Equiv.apply_symm_apply] using h

/-- Equality of fixed-endpoint path classes is reflected by the actual weak
homotopy-equivalence test. -/
theorem weak_path_homotopy_reflects {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (f : C(X, Y)) (hf : IsWeakHomotopyEquivalence f)
    {x₀ x₁ : X} {α β : Path x₀ x₁}
    (h : (α.map f.continuous).Homotopic (β.map f.continuous)) : α.Homotopic β := by
  let a : FundamentalGroupoid.mk x₀ ⟶ FundamentalGroupoid.mk x₁ :=
    Path.Homotopic.Quotient.mk α
  let b : FundamentalGroupoid.mk x₀ ⟶ FundamentalGroupoid.mk x₁ :=
    Path.Homotopic.Quotient.mk β
  let F := FundamentalGroupoid.map f
  have he : F.map a = F.map b := Quotient.sound h
  have hl : FundamentalGroup.map f x₀ (a ≫ inv b) =
      FundamentalGroup.map f x₀ (𝟙 _) := by
    change F.map (a ≫ inv b) = F.map (𝟙 _)
    rw [Functor.map_comp, he, Functor.map_inv, IsIso.hom_inv_id,
      CategoryTheory.Functor.map_id]
  have hab : a ≫ inv b = 𝟙 _ :=
    fundamentalGroup_map_injective f x₀ (hf.2 0 x₀).1 hl
  apply Path.Homotopic.Quotient.exact
  have hh := congrArg (fun c => c ≫ b) hab
  simpa only [Category.assoc, IsIso.inv_hom_id, Category.comp_id, Category.id_comp] using hh

end

end Thomason.Construction

end

section

/-! # Weak equivalences on spaces of paths with prescribed endpoints

Components use the fundamental groupoid; positive groups use the explicit
cubical dimension shift and continuous concatenation equivalences.
-/

namespace Thomason.Construction.PathSpace

open CategoryTheory

noncomputable section

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

/-- A path homotopy is a continuous path in the compact-open path space. -/
def homotopyPath {x y : X} {α β : Path x y} (H : α.Homotopy β) : Path α β where
  toFun := H.eval
  continuous_toFun := Path.continuous_uncurry_iff.mp H.continuous
  source' := H.eval_zero
  target' := H.eval_one

/-- Conversely a path in a fixed-endpoint path space is a relative homotopy. -/
def pathHomotopy {x y : X} {α β : Path x y} (H : Path α β) : α.Homotopy β where
  toFun z := H z.1 z.2
  continuous_toFun := Path.continuous_uncurry_iff.mpr H.continuous
  map_zero_left s := congrArg (fun q : Path x y => q s) H.source
  map_one_left s := congrArg (fun q : Path x y => q s) H.target
  prop' t s hs := by
    rcases hs with hs | hs
    · subst s; exact (H t).source.trans α.source.symm
    · subst s; exact (H t).target.trans α.target.symm

theorem map_components_bijective (f : C(X, Y)) (hf : IsWeakHomotopyEquivalence f)
    (x y : X) : Function.Bijective (HomotopyMaps.componentsMap (map f (x := x) (y := y))) := by
  constructor
  · intro a b hab
    induction a using ZerothHomotopy.rec with
    | mk α =>
      induction b using ZerothHomotopy.rec with
      | mk β =>
        obtain ⟨H⟩ : Joined (map f α) (map f β) := Quotient.exact hab
        obtain ⟨H'⟩ := weak_path_homotopy_reflects f hf ⟨pathHomotopy H⟩
        exact ZerothHomotopy.sound (homotopyPath H')
  · intro a
    induction a using ZerothHomotopy.rec with
    | mk γ =>
      obtain ⟨α, ⟨H⟩⟩ := weak_path_homotopy_surjective f hf γ
      exact ⟨ZerothHomotopy.mk α, ZerothHomotopy.sound (homotopyPath H)⟩

theorem rightAppend_naturality (f : C(X, Y)) {x y : X} (α : Path x y) :
    (map f (x := x) (y := y)).comp (rightAppend (a := x) α) =
      (rightAppend (a := f x) (α.map f.continuous)).comp (map f (x := x) (y := x)) := by
  apply ContinuousMap.ext
  intro q
  exact Path.map_trans q α f.continuous

/-- Every positive homotopy group of the fixed-endpoint path map is a
bijection, at an arbitrary path as basepoint. -/
theorem map_group_bijective (f : C(X, Y)) (hf : IsWeakHomotopyEquivalence f)
    {x y : X} (α : Path x y) (n : ℕ) :
    Function.Bijective (HomotopyMaps.groupMap (map f) (n+1) α) := by
  have hloop : Function.Bijective
      (HomotopyMaps.groupMap (map f (x := x) (y := x)) (n+1) (Path.refl x)) :=
    (HomotopyMaps.loopDimensionShift_bijective_iff f (n+1) x).mp (hf.2 (n+1) x)
  have hx := (homotopyEquiv_isWeakHomotopyEquivalence (rightAppendEquiv x α)).2 n
    (Path.refl x)
  have hy := (homotopyEquiv_isWeakHomotopyEquivalence
    (rightAppendEquiv (f x) (α.map f.continuous))).2 n (Path.refl (f x))
  have hc : Function.Bijective (HomotopyMaps.groupMap
      ((map f (x := x) (y := y)).comp (rightAppend (a := x) α)) (n+1) (Path.refl x)) := by
    rw [rightAppend_naturality, HomotopyMaps.groupMap_comp]
    exact hy.comp hloop
  rw [HomotopyMaps.groupMap_comp] at hc
  have hl : Function.Bijective (HomotopyMaps.groupMap (map f (x := x) (y := y))
      (n+1) (rightAppend (a := x) α (Path.refl x))) := (hx.of_comp_iff _).mp hc
  exact (HomotopyMaps.groupMap_bijective_path n (map f)
    (homotopyPath (Path.Homotopy.reflTrans α))).mp hl

/-- The actual weak-equivalence test is preserved by passing to paths between
any two specified source points, including when the path space is empty. -/
theorem map_weak (f : C(X, Y)) (hf : IsWeakHomotopyEquivalence f) (x y : X) :
    IsWeakHomotopyEquivalence (map f (x := x) (y := y)) :=
  ⟨map_components_bijective f hf x y, fun n α => map_group_bijective f hf α n⟩

end

end Thomason.Construction.PathSpace

end

section

/-! # Finite approximation of compact families of fixed-endpoint paths

A single finite subcomplex contains the whole family, including every time
coordinate. Its continuous factorization keeps both endpoints exactly fixed.
-/

namespace Thomason.Construction.RealizationPrism

open CategoryTheory

noncomputable section

theorem compact_path_family_factors {P : Type} [TopologicalSpace P] [CompactSpace P]
    (K : SSet.{0}) (f : C(P, C(unitInterval, SSet.toTop.obj K))) :
    ∃ (A : K.Subcomplex), SSet.Finite (A : SSet) ∧
      ∃ g : C(P, C(unitInterval, SSet.toTop.obj (A : SSet))),
        ∀ p t, (SSet.toTop.map A.ι).hom (g p t) = f p t := by
  obtain ⟨A, hA, g, hg⟩ := compact_map_factors K f.uncurry
  refine ⟨A, hA, g.curry, fun p t => ?_⟩
  exact congrArg (fun q : C(_, _) => q (p, t)) hg

/-- A compact family of paths with common endpoints has a finite-subcomplex
factorization with common lifted endpoints and the same exact evaluation. -/
theorem compact_fixed_path_family_factors {P : Type} [TopologicalSpace P]
    [CompactSpace P] [Nonempty P] (K : SSet.{0})
    {x y : SSet.toTop.obj K} (f : C(P, Path x y)) :
    ∃ (A : K.Subcomplex), SSet.Finite (A : SSet) ∧
      ∃ (a b : SSet.toTop.obj (A : SSet)),
        (SSet.toTop.map A.ι).hom a = x ∧ (SSet.toTop.map A.ι).hom b = y ∧
        ∃ g : C(P, Path a b), ∀ p t, (SSet.toTop.map A.ι).hom (g p t) = f p t := by
  let F : C(P × unitInterval, SSet.toTop.obj K) :=
    ⟨fun z => f z.1 z.2, Path.continuous_uncurry_iff.mpr f.continuous⟩
  obtain ⟨A, hA, G, hG⟩ := compact_map_factors K F
  have he (p : P) (t : unitInterval) :
      (SSet.toTop.map A.ι).hom (G (p, t)) = f p t :=
    congrArg (fun q : C(_, _) => q (p, t)) hG
  let p₀ : P := Classical.choice inferInstance
  let a := G (p₀, 0)
  let b := G (p₀, 1)
  have ha : (SSet.toTop.map A.ι).hom a = x := (he p₀ 0).trans (f p₀).source
  have hb : (SSet.toTop.map A.ι).hom b = y := (he p₀ 1).trans (f p₀).target
  have h₀ (p : P) : G (p, 0) = a := by
    apply inclusion_injective K A
    exact (he p 0).trans ((f p).source.trans ha.symm)
  have h₁ (p : P) : G (p, 1) = b := by
    apply inclusion_injective K A
    exact (he p 1).trans ((f p).target.trans hb.symm)
  let g : C(P, Path a b) := {
    toFun p := ⟨G.curry p, h₀ p, h₁ p⟩
    continuous_toFun := Path.continuous_uncurry_iff.mp G.continuous }
  exact ⟨A, hA, a, b, ha, hb, g, he⟩

end

end Thomason.Construction.RealizationPrism

end

section

/-! # The zero-fibre functor has the explicitly constructed right adjoint

This proves the endpoint-zero instance of the colimit consequence of
Ara–Maltsiniotis (2014), Lemma 2.8, without assuming that published input.
-/

namespace Thomason.Construction.StrictOmegaCategory.TerminalCone

open CategoryTheory CategoryTheory.Limits

noncomputable def homEquiv (X : Over (StrictPoset.category (Fin 2)))
    (C : StrictOmegaCategory.{0}) :
    (labelFiber X.hom 0 ⟶ C) ≃ (X ⟶ overFunctor.obj C) where
  toFun f := Over.homMk (extend X.hom f) (extend_label X.hom f)
  invFun g := restrict X.hom g.left (Over.w g)
  left_inv f := restrict_extend X.hom f
  right_inv g := Over.OverMorphism.ext (extend_restrict X.hom g.left (Over.w g))

/-- The actual zero-fibre / terminal-cone adjunction. -/
noncomputable def adjunction : labelFiberFunctor (Fin 2) 0 ⊣ overFunctor :=
  Adjunction.mkOfHomEquiv
    { homEquiv := homEquiv
      homEquiv_naturality_left_symm := by
        intro X' X C f g
        apply Hom.ext
        funext x
        apply Cell.old.inj
        exact (old_restrict X'.hom (f ≫ g).left (Over.w (f ≫ g)) x).trans
          (old_restrict X.hom g.left (Over.w g)
            ((labelFiberFunctor (Fin 2) 0).map f |>.toFun x)).symm
      homEquiv_naturality_right := by
        intro X C D f g
        apply Over.OverMorphism.ext
        apply Hom.ext
        funext x
        change extendCell X.hom (f ≫ g) x = mapCell g (extendCell X.hom f x)
        by_cases hl : lastLabel X.hom x = 0
        · rw [extendCell_zero X.hom (f ≫ g) x hl, extendCell_zero X.hom f x hl]
          rfl
        · by_cases hf : firstLabel X.hom x = 0
          · rw [extendCell_cross X.hom (f ≫ g) x hf hl, extendCell_cross X.hom f x hf hl]
            rfl
          · rw [extendCell_one X.hom (f ≫ g) x hf, extendCell_one X.hom f x hf]
            rfl }

/-- Formation of the actual full zero fibre preserves all small colimits. -/
theorem zeroFiber_preservesColimits :
    PreservesColimitsOfSize.{0,0} (labelFiberFunctor (Fin 2) 0) :=
  adjunction.leftAdjoint_preservesColimits

end Thomason.Construction.StrictOmegaCategory.TerminalCone

end

section

/-! # The actual zero-fibre adjunction in each positive finite dimension -/

namespace Thomason.Construction.StrictOmegaCategory.TerminalCone

open CategoryTheory CategoryTheory.Limits

def finiteCategory (n : ℕ) (C : Truncated.{0} (n+1)) : Truncated.{0} (n+1) :=
  ⟨category C.val, isTruncated (by omega) C.property⟩

/-- The terminal cone stays in the given positive finite dimension. -/
def finiteOverFunctor (n : ℕ) : Truncated.{0} (n+1) ⥤ Over (finiteInterval n) where
  obj C := Over.mk (show finiteCategory n C ⟶ finiteInterval n from label C.val)
  map f := Over.homMk (map f) (map_label f)
  map_id C := Over.OverMorphism.ext (map_id C.val)
  map_comp f g := Over.OverMorphism.ext (map_comp f g)

noncomputable def finiteHomEquiv (n : ℕ) (X : Over (finiteInterval n))
    (C : Truncated.{0} (n+1)) :
    ((finiteLabelFiberFunctor n 0).obj X ⟶ C) ≃ (X ⟶ (finiteOverFunctor n).obj C) where
  toFun f := Over.homMk (extend X.hom f) (extend_label X.hom f)
  invFun g := restrict X.hom g.left (Over.w g)
  left_inv f := restrict_extend X.hom f
  right_inv g := Over.OverMorphism.ext (extend_restrict X.hom g.left (Over.w g))

/-- Finite fibre formation is a left adjoint inside the finite category itself. -/
noncomputable def finiteAdjunction (n : ℕ) :
    finiteLabelFiberFunctor n 0 ⊣ finiteOverFunctor n :=
  Adjunction.mkOfHomEquiv
    { homEquiv := finiteHomEquiv n
      homEquiv_naturality_left_symm := by
        intro X' X C f g
        apply Hom.ext
        funext x
        apply Cell.old.inj
        exact (old_restrict X'.hom (f ≫ g).left (Over.w (f ≫ g)) x).trans
          (old_restrict X.hom g.left (Over.w g)
            ((finiteLabelFiberFunctor n 0).map f |>.toFun x)).symm
      homEquiv_naturality_right := by
        intro X C D f g
        apply Over.OverMorphism.ext
        apply Hom.ext
        funext x
        change extendCell X.hom (f ≫ g) x = mapCell g (extendCell X.hom f x)
        by_cases hl : lastLabel X.hom x = 0
        · rw [extendCell_zero X.hom (f ≫ g) x hl, extendCell_zero X.hom f x hl]
          rfl
        · by_cases hf : firstLabel X.hom x = 0
          · rw [extendCell_cross X.hom (f ≫ g) x hf hl, extendCell_cross X.hom f x hf hl]
            rfl
          · rw [extendCell_one X.hom (f ≫ g) x hf, extendCell_one X.hom f x hf]
            rfl }

/-- This preserves finite-dimensional colimits, without replacing them by omega colimits. -/
theorem finiteZeroFiber_preservesColimits (n : ℕ) :
    PreservesColimitsOfSize.{0,0} (finiteLabelFiberFunctor n 0) :=
  (finiteAdjunction n).leftAdjoint_preservesColimits

end Thomason.Construction.StrictOmegaCategory.TerminalCone

end

section

/-! # Reversing interval labels and their full fibres

Reversal changes the label-one fibre into the opposite of a label-zero
fibre. The construction lives in the actual slice over the strict interval.
-/

namespace Thomason.Construction.StrictOmegaCategory

open CategoryTheory CategoryTheory.Limits

namespace OppositeLabels

def reverseCell (x : StrictPoset.Cell (Fin 2)) : StrictPoset.Cell (Fin 2) :=
  ⟨x.last.rev, x.first.rev, Fin.rev_le_rev.mpr x.ordered⟩

/-- Reverse the strict interval together with all its directions. -/
def intervalIso : opposite (StrictPoset.category (Fin 2)) ≅ StrictPoset.category (Fin 2) where
  hom := {
    toFun := reverseCell
    map_face a n x := by
      cases n <;> cases a <;> apply StrictPoset.Cell.ext <;> rfl
    map_comp n x y h h' := by
      cases n with
      | zero => apply StrictPoset.Cell.ext <;> rfl
      | succ n => exact congrArg reverseCell h.symm }
  inv := {
    toFun := reverseCell
    map_face a n x := by
      cases n <;> cases a <;> apply StrictPoset.Cell.ext <;> rfl
    map_comp n x y h h' := by
      cases n with
      | zero => apply StrictPoset.Cell.ext <;> rfl
      | succ n => exact congrArg reverseCell h }
  hom_inv_id := by
    apply Hom.ext
    funext x
    apply StrictPoset.Cell.ext <;> exact Fin.rev_rev _
  inv_hom_id := by
    apply Hom.ext
    funext x
    apply StrictPoset.Cell.ext <;> exact Fin.rev_rev _

/-- The reversed label sends the original value one to zero. -/
def label {C : StrictOmegaCategory.{0}} (p : C ⟶ StrictPoset.category (Fin 2)) :
    opposite C ⟶ StrictPoset.category (Fin 2) := oppositeMap p ≫ intervalIso.hom

def overFunctor : Over (StrictPoset.category (Fin 2)) ⥤ Over (StrictPoset.category (Fin 2)) where
  obj X := Over.mk (label X.hom)
  map {X Y} f := Over.homMk (oppositeMap f.left) (by
    apply Hom.ext
    funext x
    exact congrArg reverseCell (congrArg (fun q => q.toFun x) (Over.w f)))
  map_id X := Over.OverMorphism.ext (by apply Hom.ext; rfl)
  map_comp f g := Over.OverMorphism.ext (by apply Hom.ext; rfl)

/-- Reversing twice recovers the original object in the slice. -/
def doubleIso (X : Over (StrictPoset.category (Fin 2))) :
    overFunctor.obj (overFunctor.obj X) ≅ X :=
  Over.isoMk (doubleOppositeIso X.left) (by
    apply Hom.ext
    funext x
    apply StrictPoset.Cell.ext <;> exact (Fin.rev_rev _).symm)

/-- Opposite interval labelling is an involutive slice equivalence. -/
def equivalence : Over (StrictPoset.category (Fin 2)) ≌ Over (StrictPoset.category (Fin 2)) where
  functor := overFunctor
  inverse := overFunctor
  unitIso := NatIso.ofComponents (fun X => (doubleIso X).symm) (by
    intro X Y f
    apply Over.OverMorphism.ext
    apply Hom.ext
    rfl)
  counitIso := NatIso.ofComponents doubleIso (by
    intro X Y f
    apply Over.OverMorphism.ext
    apply Hom.ext
    rfl)
  functor_unitIso_comp X := by
    apply Over.OverMorphism.ext
    apply Hom.ext
    rfl

/-- The condition on all cells is exactly transported by interval reversal. -/
theorem label_zero_iff {C : StrictOmegaCategory.{0}}
    (p : C ⟶ StrictPoset.category (Fin 2)) (x : C) :
    (label p).toFun x = StrictPoset.identity 0 ↔ p.toFun x = StrictPoset.identity 1 := by
  constructor
  · intro h
    have h' := congrArg reverseCell h
    apply StrictPoset.Cell.ext
    · have he := congrArg StrictPoset.Cell.first h'
      change (p.toFun x).first.rev.rev = (0 : Fin 2).rev at he
      simpa only [Fin.rev_rev, Fin.rev_zero, StrictPoset.identity, show Fin.last 1 = (1 : Fin 2) from rfl] using he
    · have he := congrArg StrictPoset.Cell.last h'
      change (p.toFun x).last.rev.rev = (0 : Fin 2).rev at he
      simpa only [Fin.rev_rev, Fin.rev_zero, StrictPoset.identity, show Fin.last 1 = (1 : Fin 2) from rfl] using he
  · intro h
    change reverseCell (p.toFun x) = StrictPoset.identity 0
    rw [h]
    apply StrictPoset.Cell.ext <;> rfl

/-- The opposite of the reversed zero fibre is the original one fibre. -/
def fiberIso (X : Over (StrictPoset.category (Fin 2))) :
    opposite (labelFiber (label X.hom) 0) ≅ labelFiber X.hom 1 where
  hom := {
    toFun x := ⟨x.val, (fullCell_label_iff X.hom 1 x.val).mpr
      ((label_zero_iff X.hom x.val).mp ((fullCell_label_iff (label X.hom) 0 x.val).mp x.property))⟩
    map_face a n x := by apply Subtype.ext; cases a <;> rfl
    map_comp n x y h h' := by apply Subtype.ext; rfl }
  inv := {
    toFun x := ⟨x.val, (fullCell_label_iff (label X.hom) 0 x.val).mpr
      ((label_zero_iff X.hom x.val).mpr ((fullCell_label_iff X.hom 1 x.val).mp x.property))⟩
    map_face a n x := by apply Subtype.ext; cases a <;> rfl
    map_comp n x y h h' := by apply Subtype.ext; rfl }
  hom_inv_id := by apply Hom.ext; funext x; apply Subtype.ext; rfl
  inv_hom_id := by apply Hom.ext; funext x; apply Subtype.ext; rfl

/-- The actual one-fibre functor is conjugate to the zero-fibre functor. -/
def fiberNatIso : overFunctor ⋙ labelFiberFunctor (Fin 2) 0 ⋙ oppositeFunctor ≅
    labelFiberFunctor (Fin 2) 1 :=
  NatIso.ofComponents fiberIso (by
    intro X Y f
    apply Hom.ext
    funext x
    apply Subtype.ext
    rfl)

/-- Full one fibres, as well as zero fibres, preserve all small colimits. -/
theorem oneFiber_preservesColimits :
    PreservesColimitsOfSize.{0,0} (labelFiberFunctor (Fin 2) 1) := by
  have := TerminalCone.zeroFiber_preservesColimits
  have : PreservesColimitsOfSize.{0,0} overFunctor := equivalence.toAdjunction.leftAdjoint_preservesColimits
  have : PreservesColimitsOfSize.{0,0} oppositeFunctor :=
    oppositeEquivalence.toAdjunction.leftAdjoint_preservesColimits
  exact preservesColimits_of_natIso fiberNatIso

end OppositeLabels

end Thomason.Construction.StrictOmegaCategory

end

section

/-! # The simplex colimit of a full cosieve fibre

The explicit binary labels give the original oriental diagram in the slice.
Its one fibre is a colimit by the constructed terminal-cone adjunction.
-/

namespace Thomason.Construction.CosieveSimplex

open CategoryTheory CategoryTheory.Limits StrictOmegaCategory
open NormalizedSimplexIdentities

variable {P : Type} [PartialOrder P] (A : Set P) (hA : IsUpperSet A)
  (h : NormalizedSimplexIdentities) [StrictColimitsInput]

/-- The binary labels of all simplices form a natural transformation. -/
noncomputable def labels :
    (CostructuredArrow.proj SSet.stdSimplex (nerve P) ⋙ h.cosimplicial) ⟶
      (Functor.const _).obj (StrictPoset.category (Fin 2)) where
  app s := label A hA (simplexOrder (SSet.yonedaEquiv s.hom)) h
  naturality s t a := by
    change h.map a.left.toOrderHom ≫
      label A hA (simplexOrder (SSet.yonedaEquiv t.hom)) h = _
    rw [label_precomp, ← simplexOrder_precomp, CostructuredArrow.w a]
    rfl

/-- The labelled diagram has the original orientals as underlying objects. -/
noncomputable abbrev diagram :
    CostructuredArrow SSet.stdSimplex (nerve P) ⥤ Over (StrictPoset.category (Fin 2)) :=
  Over.lift _ (labels A hA h)

/-- The colimit point is the original categorification with its membership label. -/
noncomputable abbrev cocone : Cocone (diagram A hA h) where
  pt := Over.mk (h.membershipLabel Aᶜ hA.compl)
  ι :=
    { app := fun s => Over.homMk (h.simplexLeg s.hom) (h.membership_simplex_label Aᶜ hA.compl s.hom)
      naturality := by
        intro s t a
        apply Over.OverMorphism.ext
        exact (h.simplexCocone (nerve P)).ι.naturality a }

/-- Forgetting the labels recovers exactly the original simplex colimit. -/
noncomputable def coconeIsColimit : IsColimit (cocone A hA h) := by
  apply isColimitOfReflects (Over.forget (StrictPoset.category (Fin 2)))
  exact h.simplexCocone_isColimit (nerve P)

/-- Its full one fibre is therefore the colimit of the full simplex fibres. -/
noncomputable abbrev fiberCocone : Cocone (diagram A hA h ⋙ labelFiberFunctor (Fin 2) 1) :=
  (labelFiberFunctor (Fin 2) 1).mapCocone (cocone A hA h)

/-- This uses the proved adjunction, with no published fibre-colimit input. -/
noncomputable def fiberCoconeIsColimit : IsColimit (fiberCocone A hA h) := by
  have := OppositeLabels.oneFiber_preservesColimits
  exact isColimitOfPreserves (labelFiberFunctor (Fin 2) 1) (coconeIsColimit A hA h)

/-- The clamping inverses form a cocone on the same full simplex fibres. -/
noncomputable def backCocone : Cocone (diagram A hA h ⋙ labelFiberFunctor (Fin 2) 1) where
  pt := h.categorification.obj (nerve A)
  ι :=
    { app := fun s => back A hA h (simplexOrder (SSet.yonedaEquiv s.hom))
      naturality := by
        intro s t a
        have he := (congrArg (fun z => simplexOrder (SSet.yonedaEquiv z))
          (CostructuredArrow.w a)).symm.trans (simplexOrder_precomp t.hom a.left)
        change _ ≫ back A hA h (simplexOrder (SSet.yonedaEquiv t.hom)) = _
        have hb := back_naturality A hA h
          (simplexOrder (SSet.yonedaEquiv t.hom)) a.left.toOrderHom
        apply Hom.ext
        funext x
        have hx := congrArg (fun f => f.toFun ⟨x.val, he ▸ x.property⟩) hb
        exact hx.trans (back_apply_congr A hA h he.symm _ x rfl) }

/-- Descending the compatible clamping maps gives the inverse of the cosieve map. -/
noncomputable def inverse :
    labelFiber (h.membershipLabel Aᶜ hA.compl) 1 ⟶ h.categorification.obj (nerve A) :=
  (fiberCoconeIsColimit A hA h).desc (backCocone A hA h)

/-- The descended map restricts to the explicit inverse on every simplex fibre. -/
theorem inverse_fac (s : CostructuredArrow SSet.stdSimplex (nerve P)) :
    (fiberCocone A hA h).ι.app s ≫ inverse A hA h =
      back A hA h (simplexOrder (SSet.yonedaEquiv s.hom)) :=
  (fiberCoconeIsColimit A hA h).fac (backCocone A hA h) s

end Thomason.Construction.CosieveSimplex

end

section

/-! # The canonical categorified sieve is its actual full one fibre

The inverse is descended from clamped simplex maps. Both inverse identities
follow from the actual simplex colimits, with empty pieces included.
-/

namespace Thomason.Construction.CosieveSimplex

open CategoryTheory CategoryTheory.Limits StrictOmegaCategory
open NormalizedSimplexIdentities

variable {P : Type} [PartialOrder P] (A : Set P) (hA : IsUpperSet A)
  (h : NormalizedSimplexIdentities) [StrictColimitsInput]

/-- Forgetting the descended inverse recovers the original fibre inclusion. -/
theorem inverse_inclusion :
    inverse A hA h ≫ h.posetMap (subposetInclusion A) =
      labelFiberInclusion (h.membershipLabel Aᶜ hA.compl) 1 := by
  apply (fiberCoconeIsColimit A hA h).hom_ext
  intro s
  let l : labelFiber (label A hA (simplexOrder (SSet.yonedaEquiv s.hom)) h) 1 ⟶
      labelFiber (h.membershipLabel Aᶜ hA.compl) 1 := (fiberCocone A hA h).ι.app s
  change l ≫ (inverse A hA h ≫ h.posetMap (subposetInclusion A)) =
    l ≫ labelFiberInclusion (h.membershipLabel Aᶜ hA.compl) 1
  have he := back_inclusion A hA h (simplexOrder (SSet.yonedaEquiv s.hom))
  rw [h.posetLeg_simplexOrder] at he
  exact (Category.assoc l _ _).symm.trans
    ((congrArg (fun k => k ≫ h.posetMap (subposetInclusion A))
      (inverse_fac A hA h s)).trans he)

/-- The descended inverse is a right inverse of the canonical sieve map. -/
theorem inverse_posetFiberMap :
    inverse A hA h ≫ h.cosievePosetFiberMap A hA = 𝟙 _ := by
  apply (cancel_mono (labelFiberInclusion (h.membershipLabel Aᶜ hA.compl) 1)).mp
  rw [Category.assoc, h.cosievePosetFiberMap_inclusion, inverse_inclusion, Category.id_comp]

/-- The whole sieve simplex maps to the original colimit leg after forgetting. -/
theorem whole_fiberLeg {m : ℕ} (s : Fin (m+1) →o A) :
    whole A hA h s ≫ (fiberCocone A hA h).ι.app
        (CostructuredArrow.mk (SSet.yonedaEquiv.symm
          (orderSimplex ((subposetInclusion A).comp s)))) =
      h.posetLeg s ≫ h.cosievePosetFiberMap A hA := by
  apply (cancel_mono (labelFiberInclusion (h.membershipLabel Aᶜ hA.compl) 1)).mp
  rw [Category.assoc, h.cosievePosetFiberMap_inclusion]
  exact (h.posetLeg_postcomp s (subposetInclusion A)).symm

/-- The inverse identity on an arbitrary simplex of the original sieve. -/
theorem posetFiberMap_inverse_on_leg {m : ℕ} (s : Fin (m+1) →o A) :
    h.posetLeg s ≫ (h.cosievePosetFiberMap A hA ≫ inverse A hA h) = h.posetLeg s := by
  let t := CostructuredArrow.mk (SSet.yonedaEquiv.symm
    (orderSimplex ((subposetInclusion A).comp s)))
  let l : labelFiber (label A hA ((subposetInclusion A).comp s) h) 1 ⟶
      labelFiber (h.membershipLabel Aᶜ hA.compl) 1 := (fiberCocone A hA h).ι.app t
  have hl : l ≫ inverse A hA h = back A hA h ((subposetInclusion A).comp s) := by
    have hv : simplexOrder (SSet.yonedaEquiv t.hom) = (subposetInclusion A).comp s := by
      change simplexOrder (SSet.yonedaEquiv (SSet.yonedaEquiv.symm
        (orderSimplex ((subposetInclusion A).comp s)))) = _
      rw [Equiv.apply_symm_apply, simplexOrder_orderSimplex]
    apply Hom.ext
    funext x
    let y : labelFiber (label A hA (simplexOrder (SSet.yonedaEquiv t.hom)) h) 1 :=
      ⟨x.val, by rw [hv]; exact x.property⟩
    have he := congrArg (fun f => f.toFun y) (inverse_fac A hA h t)
    exact he.trans (back_apply_congr A hA h hv y x rfl)
  have hw : whole A hA h s ≫ l = h.posetLeg s ≫ h.cosievePosetFiberMap A hA :=
    whole_fiberLeg A hA h s
  exact (Category.assoc (h.posetLeg s) _ _).symm.trans
    ((congrArg (fun k => k ≫ inverse A hA h) hw.symm).trans
      ((Category.assoc (whole A hA h s) l _).trans
        ((congrArg (fun k => whole A hA h s ≫ k) hl).trans (whole_back A hA h s))))

/-- The descended inverse is also a left inverse, on the original sieve colimit. -/
theorem posetFiberMap_inverse :
    h.cosievePosetFiberMap A hA ≫ inverse A hA h = 𝟙 _ := by
  apply (h.simplexCocone_isColimit (nerve A)).hom_ext
  intro t
  have he := posetFiberMap_inverse_on_leg A hA h (simplexOrder (SSet.yonedaEquiv t.hom))
  rw [h.posetLeg_simplexOrder] at he
  change h.simplexLeg t.hom ≫ (h.cosievePosetFiberMap A hA ≫ inverse A hA h) =
    h.simplexLeg t.hom ≫ 𝟙 _
  rw [Category.comp_id]
  exact he

end CosieveSimplex

namespace NormalizedSimplexIdentities

open CategoryTheory StrictOmegaCategory

/-- A poset sieve categorifies to exactly the full one fibre of membership. -/
noncomputable def posetCosieveIso (h : NormalizedSimplexIdentities) [StrictColimitsInput]
    {P : Type} [PartialOrder P] (A : Set P) (hA : IsUpperSet A) :
    h.categorification.obj (nerve A) ≅ labelFiber (h.membershipLabel Aᶜ hA.compl) 1 where
  hom := h.cosievePosetFiberMap A hA
  inv := CosieveSimplex.inverse A hA h
  hom_inv_id := CosieveSimplex.posetFiberMap_inverse A hA h
  inv_hom_id := CosieveSimplex.inverse_posetFiberMap A hA h

end NormalizedSimplexIdentities
end Thomason.Construction

end

end OAI
