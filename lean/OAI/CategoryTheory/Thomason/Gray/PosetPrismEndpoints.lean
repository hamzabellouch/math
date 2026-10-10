import OAI.CategoryTheory.Thomason.Chains.SimplexChainHeight
import OAI.CategoryTheory.Thomason.Gray.CylinderAssembly
import OAI.CategoryTheory.Thomason.Simplicial.SimplicialSpanFactorization
import OAI.CategoryTheory.Thomason.Strict.StrictIsomorphisms
import OAI.CategoryTheory.Thomason.Strict.UnderlyingCategory
import Mathlib.AlgebraicTopology.SimplicialSet.Homotopy
import Mathlib.Data.Finset.Sort
import Mathlib.Order.NonemptyFiniteChains
import Mathlib.Order.Preorder.Chain

namespace OAI

section

/-!
# From a strict Gray cylinder to a homotopy of Street nerves

The simplicial map is constructed on actual oriental-valued simplices
using the explicit interval Alexander--Whitney map. Naturality includes
all simplex operators, hence also degeneracies. No nerve-homotopy assertion
from the new manuscript is assumed.
-/

namespace Thomason.Construction

open CategoryTheory Opposite MonoidalCategory CartesianMonoidalCategory
open _root_.OAI.Thomason.Construction.DirectedComplex SimplexComplex
open scoped Simplicial

namespace SimplexComplex.AlexanderWhitneyInput

variable {h : NormalizedSimplexIdentities} (aw : AlexanderWhitneyInput h)

noncomputable def simplexMap {m : ℕ} (θ : Fin (m + 1) →o Fin 2) :
    h.object m ⟶ h.cylinderObject m := (aw.chainMap θ).realization

theorem simplexMap_naturality {l m : ℕ} (a : Fin (l + 1) →o Fin (m + 1))
    (θ : Fin (m + 1) →o Fin 2) :
    h.map a ≫ aw.simplexMap θ = aw.simplexMap (θ.comp a) ≫ h.cylinderMap a := by
  apply StrictOmegaCategory.Hom.ext
  funext x
  apply Cell.ext
  funext b p
  exact (aw.naturality a θ p (x.table b p)).symm

theorem simplexMap_const {m : ℕ} (a : Bool) :
    aw.simplexMap (OrderHom.const _ (if a then 1 else 0)) =
      (h.cylinderEndpoint a).app (.mk m) := by
  apply StrictOmegaCategory.Hom.ext
  funext x
  apply Cell.ext
  funext b p
  exact aw.chainMap_const a p (x.table b p)

theorem simplexMap_projection {m : ℕ} (θ : Fin (m + 1) →o Fin 2) :
    aw.simplexMap θ ≫ h.cylinderProjection.app (.mk m) = 𝟙 (h.object m) := by
  apply StrictOmegaCategory.Hom.ext
  funext x
  apply Cell.ext
  funext b p
  exact aw.projection_chainMap θ p (x.table b p)

end SimplexComplex.AlexanderWhitneyInput

namespace RightGrayInput

variable {h : NormalizedSimplexIdentities} (G : RightGrayInput h)
  (aw : AlexanderWhitneyInput h)

noncomputable def diagonal {m : ℕ} (θ : Fin (m + 1) →o Fin 2) :
    h.object m ⟶ G.cylinder.obj (h.object m) :=
  aw.simplexMap θ ≫ G.simplexComparison.hom.app (.mk m)

theorem diagonal_naturality {l m : ℕ} (a : Fin (l + 1) →o Fin (m + 1))
    (θ : Fin (m + 1) →o Fin 2) :
    h.map a ≫ G.diagonal aw θ =
      G.diagonal aw (θ.comp a) ≫ G.cylinder.map (h.map a) := by
  let il : h.cylinderObject l ⟶ G.cylinder.obj (h.object l) :=
    G.simplexComparison.hom.app (.mk l)
  let im : h.cylinderObject m ⟶ G.cylinder.obj (h.object m) :=
    G.simplexComparison.hom.app (.mk m)
  have hn : h.cylinderMap a ≫ im = il ≫ G.cylinder.map (h.map a) :=
    G.simplexComparison.hom.naturality (SimplexCategory.Hom.mk a)
  change h.map a ≫ (aw.simplexMap θ ≫ im) =
    (aw.simplexMap (θ.comp a) ≫ il) ≫ G.cylinder.map (h.map a)
  calc
    _ = (h.map a ≫ aw.simplexMap θ) ≫ im := (Category.assoc _ _ _).symm
    _ = (aw.simplexMap (θ.comp a) ≫ h.cylinderMap a) ≫ im :=
      congrArg (fun k => k ≫ im) (aw.simplexMap_naturality a θ)
    _ = aw.simplexMap (θ.comp a) ≫ (il ≫ G.cylinder.map (h.map a)) := by
      rw [Category.assoc, hn]
    _ = _ := (Category.assoc _ _ _).symm

theorem diagonal_const {m : ℕ} (a : Bool) :
    G.diagonal aw (OrderHom.const _ (if a then 1 else 0)) =
      (G.endpoint a).app (h.object m) := by
  unfold diagonal
  rw [aw.simplexMap_const]
  exact G.endpoint_comparison a (.mk m)

theorem diagonal_projection {m : ℕ} (θ : Fin (m + 1) →o Fin 2) :
    G.diagonal aw θ ≫ G.projection.app (h.object m) = 𝟙 (h.object m) := by
  let i : h.cylinderObject m ⟶ G.cylinder.obj (h.object m) :=
    G.simplexComparison.hom.app (.mk m)
  let π : G.cylinder.obj (h.object m) ⟶ h.object m := G.projection.app (h.object m)
  let cp : h.cylinderObject m ⟶ h.object m := h.cylinderProjection.app (.mk m)
  have hp : i ≫ π = cp := G.projection_comparison (.mk m)
  change (aw.simplexMap θ ≫ i) ≫ π = 𝟙 (h.object m)
  calc
    _ = aw.simplexMap θ ≫ cp := by rw [Category.assoc, hp]
    _ = 𝟙 (h.object m) := aw.simplexMap_projection θ

/-- The interval comparison on the Street nerve, evaluated on a simplex
`F : O_m → X` and an ordinal map `[m] → [1]`. -/
noncomputable def nerveCylinder (X : StrictOmegaCategory.{0}) :
    h.streetNerve.obj X ⊗ Δ[1] ⟶ h.streetNerve.obj (G.cylinder.obj X) where
  app m := ↾fun x => G.diagonal aw (SSet.stdSimplex.objEquiv x.2).toOrderHom ≫
    G.cylinder.map x.1
  naturality m n a := by
    ext x
    change (h.object m.unop.len ⟶ X) × (Δ[1].obj m) at x
    rcases x with ⟨F, θ⟩
    let α : h.object n.unop.len ⟶ h.object m.unop.len := h.map a.unop.toOrderHom
    let t := (SSet.stdSimplex.objEquiv θ).toOrderHom
    change G.diagonal aw (t.comp a.unop.toOrderHom) ≫ G.cylinder.map (α ≫ F) =
      α ≫ (G.diagonal aw t ≫ G.cylinder.map F)
    calc
      _ = G.diagonal aw (t.comp a.unop.toOrderHom) ≫ (G.cylinder.map α ≫ G.cylinder.map F) :=
        congrArg (fun k => G.diagonal aw (t.comp a.unop.toOrderHom) ≫ k) (G.cylinder.map_comp α F)
      _ = (G.diagonal aw (t.comp a.unop.toOrderHom) ≫ G.cylinder.map α) ≫ G.cylinder.map F :=
        (Category.assoc _ _ _).symm
      _ = (α ≫ G.diagonal aw t) ≫ G.cylinder.map F :=
        congrArg (fun k => k ≫ G.cylinder.map F) (G.diagonal_naturality aw a.unop.toOrderHom t).symm
      _ = _ := Category.assoc _ _ _

/-- The two simplicial endpoints are exactly the nerves of the strict endpoints. -/
theorem nerveCylinder_endpoint (X : StrictOmegaCategory.{0}) (a : Bool) :
    (if a then SSet.ι₁ else SSet.ι₀) ≫ G.nerveCylinder aw X =
      h.streetNerve.map ((G.endpoint a).app X) := by
  apply NatTrans.ext
  funext m
  apply ConcreteCategory.hom_ext
  intro F
  change h.object m.unop.len ⟶ X at F
  cases a <;>
    change G.diagonal aw (OrderHom.const _ _) ≫ G.cylinder.map F = F ≫ (G.endpoint _).app X
  · exact (congrArg (fun k => k ≫ G.cylinder.map F)
      (G.diagonal_const aw (m := m.unop.len) false)).trans
        ((G.endpoint false).naturality F).symm
  · exact (congrArg (fun k => k ≫ G.cylinder.map F)
      (G.diagonal_const aw (m := m.unop.len) true)).trans
        ((G.endpoint true).naturality F).symm

/-- Collapsing the Gray interval agrees with projection of simplicial sets. -/
theorem nerveCylinder_projection (X : StrictOmegaCategory.{0}) :
    G.nerveCylinder aw X ≫ h.streetNerve.map (G.projection.app X) =
      fst (h.streetNerve.obj X) Δ[1] := by
  apply NatTrans.ext
  funext m
  apply ConcreteCategory.hom_ext
  intro x
  change (h.object m.unop.len ⟶ X) × (Δ[1].obj m) at x
  rcases x with ⟨F, θ⟩
  let t := (SSet.stdSimplex.objEquiv θ).toOrderHom
  change (G.diagonal aw t ≫ G.cylinder.map F) ≫ G.projection.app X = F
  calc
    _ = G.diagonal aw t ≫ (G.projection.app (h.object m.unop.len) ≫ F) := by
      rw [Category.assoc]
      exact congrArg (fun k => G.diagonal aw t ≫ k) (G.projection.naturality F)
    _ = (G.diagonal aw t ≫ G.projection.app (h.object m.unop.len)) ≫ F :=
      (Category.assoc _ _ _).symm
    _ = (𝟙 (h.object m.unop.len) : h.object m.unop.len ⟶ h.object m.unop.len) ≫ F :=
      congrArg (fun k => k ≫ F) (G.diagonal_projection aw t)
    _ = F := Category.id_comp F

/-- Naturality in the strict category, needed for relative homotopies. -/
theorem nerveCylinder_naturality {X Y : StrictOmegaCategory.{0}} (f : X ⟶ Y) :
    h.streetNerve.map f ▷ Δ[1] ≫ G.nerveCylinder aw Y =
      G.nerveCylinder aw X ≫ h.streetNerve.map (G.cylinder.map f) := by
  apply NatTrans.ext
  funext m
  apply ConcreteCategory.hom_ext
  intro x
  change (h.object m.unop.len ⟶ X) × (Δ[1].obj m) at x
  rcases x with ⟨F, θ⟩
  let t := (SSet.stdSimplex.objEquiv θ).toOrderHom
  change G.diagonal aw t ≫ G.cylinder.map (F ≫ f) =
    (G.diagonal aw t ≫ G.cylinder.map F) ≫ G.cylinder.map f
  rw [G.cylinder.map_comp, Category.assoc]

/-- Every strict right Gray cylinder gives an actual simplicial homotopy. -/
noncomputable def nerveHomotopy {X Y : StrictOmegaCategory.{0}}
    (P : G.cylinder.obj X ⟶ Y) :
    SSet.Homotopy (h.streetNerve.map ((G.endpoint false).app X ≫ P))
      (h.streetNerve.map ((G.endpoint true).app X ≫ P)) where
  h := G.nerveCylinder aw X ≫ h.streetNerve.map P
  h₀ := by
    change SSet.ι₀ ≫ (G.nerveCylinder aw X ≫ h.streetNerve.map P) = _
    have he := G.nerveCylinder_endpoint aw X false
    change SSet.ι₀ ≫ G.nerveCylinder aw X = _ at he
    rw [← Category.assoc, he]
    exact (h.streetNerve.map_comp _ _).symm
  h₁ := by
    change SSet.ι₁ ≫ (G.nerveCylinder aw X ≫ h.streetNerve.map P) = _
    have he := G.nerveCylinder_endpoint aw X true
    change SSet.ι₁ ≫ G.nerveCylinder aw X = _ at he
    rw [← Category.assoc, he]
    exact (h.streetNerve.map_comp _ _).symm
  rel := by
    apply NatTrans.ext
    funext m
    apply ConcreteCategory.hom_ext
    intro x
    change ((⊥ : (h.streetNerve.obj X).Subcomplex).toSSet.obj m) × (Δ[1].obj m) at x
    exact False.elim x.1.property

/-- Whole-cylinder stationarity becomes equality of whole simplicial homotopies. -/
theorem nerveHomotopy_stationary {A X Y : StrictOmegaCategory.{0}}
    (a : A ⟶ X) (v : A ⟶ Y) (P : G.cylinder.obj X ⟶ Y)
    (hs : G.cylinder.map a ≫ P = G.projection.app A ≫ v) :
    h.streetNerve.map a ▷ Δ[1] ≫ (G.nerveHomotopy aw P).h =
      fst (h.streetNerve.obj A) Δ[1] ≫ h.streetNerve.map v := by
  change h.streetNerve.map a ▷ Δ[1] ≫ (G.nerveCylinder aw X ≫ h.streetNerve.map P) = _
  rw [← Category.assoc, G.nerveCylinder_naturality aw a, Category.assoc,
    ← h.streetNerve.map_comp, hs, h.streetNerve.map_comp, ← Category.assoc,
    G.nerveCylinder_projection]

end RightGrayInput
end Thomason.Construction

end

section

/-! # Finite ordered decomposition of positive simplex tables

An ordered sum of atoms above dimension r can be split into actual strict
composites at r. This performs the finite decomposition step and leaves
the lower-dimensional generation induction separate.
-/

namespace Thomason.Construction.SimplexComplex

open _root_.OAI.Thomason.Construction.DirectedComplex

/-- Vanishing of every summand's coefficient gives vanishing of the sum. -/
theorem sumCells_coefficient_zero {h : NormalizedSimplexIdentities} {m : ℕ}
    (as : List (h.object m)) (side : Bool) (n : ℕ) (b : Basis m n)
    (hz : ∀ A ∈ as, A.table side n b = 0) :
    (Cell.PositiveTable.ofCells as).table side n b = 0 := by
  induction as with
  | nil => rfl
  | cons A as ih =>
    change A.table side n b + (Cell.PositiveTable.ofCells as).table side n b = 0
    rw [hz A (by simp), ih (fun B hB => hz B (by simp [hB])), zero_add]

/-- A composition-closed predicate holding for the individual upper-table
pieces holds for their ordered sum, with an explicit zero-table base case. -/
theorem ordered_sum_induction (h : NormalizedSimplexIdentities) {m : ℕ}
    (r : ℕ) (P : h.object m → Prop)
    (hzero : ∀ X : h.object m, (∀ n, r < n → ∀ side, X.table side n = 0) → P X)
    (hcomp : ∀ (Y Z : h.object m) (hyz), P Y → P Z → P ((h.object m).comp r Y Z hyz))
    (as : List (h.object m))
    (hsep : as.Pairwise (fun A B => ∀ b : Basis m r,
      A.table false r b = 0 ∨ B.table true r b = 0))
    (hone : ∀ A ∈ as, ∀ X : h.object m,
      (∀ n, r < n → ∀ side, X.table side n = A.table side n) → P X)
    (X : h.object m)
    (he : ∀ n, r < n → ∀ side,
      X.table side n = (Cell.PositiveTable.ofCells as).table side n) : P X := by
  induction as generalizing X with
  | nil => exact hzero X he
  | cons A as ih =>
    obtain ⟨hfirst, htail⟩ := List.pairwise_cons.mp hsep
    have hdisjoint : ∀ b : Basis m r, A.table false r b = 0 ∨
        (Cell.PositiveTable.ofCells as).table true r b = 0 := by
      intro b
      by_cases hb : A.table false r b = 0
      · exact Or.inl hb
      · right
        exact sumCells_coefficient_zero as true r b
          (fun B hB => (hfirst B hB b).resolve_left hb)
    have hsum : ∀ n, r < n → ∀ side,
        X.table side n = A.table side n + (Cell.PositiveTable.ofCells as).table side n := he
    obtain ⟨Y, Z, hyz, hYZ, hY, hZ⟩ := split_of_disjoint_positiveTables h X
      (Cell.PositiveTable.ofCell A) (Cell.PositiveTable.ofCells as) r hsum hdisjoint
    have hPY := hone A (by simp) Y hY
    have hPZ := ih htail (fun B hB => hone B (by simp [hB])) Z hZ
    have hp := hcomp Y Z hyz hPY hPZ
    rwa [hYZ] at hp

end Thomason.Construction.SimplexComplex

end

section

/-! # Signed-boundary formulas for the constructed principal cells -/

namespace Thomason.Construction.SimplexComplex

open _root_.OAI.Thomason.Construction.DirectedComplex

/-- A positive chain has itself as positive part and zero as negative part. -/
theorem signedPart_positive {m p : ℕ} (a : Bool) (x : Chains m p)
    (hx : x ∈ positive m p) : signedPart a x = if a then x else 0 := by
  apply Finsupp.ext
  intro b
  have hb := hx b
  cases a <;> simp [signedPart, max_eq_left (neg_nonpos.mpr hb), max_eq_right hb]

/-- A negative positive-chain has only a negative part. -/
theorem signedPart_neg_positive {m p : ℕ} (a : Bool) (x : Chains m p)
    (hx : x ∈ positive m p) : signedPart a (-x) = if a then 0 else x := by
  apply Finsupp.ext
  intro b
  have hb := hx b
  cases a <;> simp [signedPart, max_eq_left (neg_nonpos.mpr hb), max_eq_right hb]

/-- Separate the coned and old-face parts of a boundary. -/
theorem signedPart_cone_add_prefix {m p : ℕ} (a : Bool) (x : Chains m p)
    (y : Chains m (p + 1)) (hy : y ∈ positive m (p + 1)) :
    signedPart a (prism (coneInclusion m) (coneVertex m) (cone_le m) p x +
      mapChains (coneInclusion m) (p + 1) y) =
    prism (coneInclusion m) (coneVertex m) (cone_le m) p (signedPart a x) +
      if a then mapChains (coneInclusion m) (p + 1) y else 0 := by
  rw [signedPart_add_of_disjoint a _ _ (fun b => (prefix_cone_disjoint y x b).symm),
    signedPart_cone, signedPart_positive a _ (mapChains_positive _ hy)]

/-- The analogous separation for a negative old-face boundary term. -/
theorem signedPart_cone_sub_prefix {m p : ℕ} (a : Bool) (x : Chains m p)
    (y : Chains m (p + 1)) (hy : y ∈ positive m (p + 1)) :
    signedPart a (prism (coneInclusion m) (coneVertex m) (cone_le m) p x -
      mapChains (coneInclusion m) (p + 1) y) =
    prism (coneInclusion m) (coneVertex m) (cone_le m) p (signedPart a x) +
      if a then 0 else mapChains (coneInclusion m) (p + 1) y := by
  rw [sub_eq_add_neg]
  have hd (b : Basis (m + 1) (p + 1)) :
      prism (coneInclusion m) (coneVertex m) (cone_le m) p x b = 0 ∨
        (-mapChains (coneInclusion m) (p + 1) y) b = 0 := by
    rcases prefix_cone_disjoint y x b with hp | hc
    · right
      simp [hp]
    · exact Or.inl hc
  rw [signedPart_add_of_disjoint a _ _ hd, signedPart_cone,
    signedPart_neg_positive a _ (mapChains_positive _ hy)]

/-- A constant vertex map kills positive-dimensional normalized chains. -/
theorem mapChains_coneVertex_zero {m p : ℕ} (x : Chains m (p + 1)) :
    mapChains (coneVertex m) (p + 1) x = 0 := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | single s z =>
    have hn : ¬StrictMono (fun i => coneVertex m (s i)) := by
      intro hs
      have hh := hs (0 : Fin (p + 1)).castSucc_lt_succ
      exact lt_irrefl _ hh
    rw [mapChains_single, mapBasis, dite_eq_right hn, smul_zero]

/-- In positive degree the cone table is the coned boundary plus one old face. -/
theorem coneCell_succ_table (h : NormalizedSimplexIdentities) {m : ℕ}
    (x : h.object m) (a : Bool) (p : ℕ) :
    (coneCell h x).table a (p + 1) =
      prism (coneInclusion m) (coneVertex m) (cone_le m) p (x.table a p) +
        if a = decide (Even p) then mapChains (coneInclusion m) (p + 1) (x.table a (p + 1))
          else 0 := by
  rw [coneCell_table, coneChainMap_succ_app]
  have hg (z : Chains m (p + 1)) : mapChains (coneVertex m) (p + 1) z = 0 :=
    mapChains_coneVertex_zero z
  by_cases he : Even p <;> cases a <;>
    simp only [RightCylinder.intervalCellTable, he, ↓reduceIte, decide_true,
      decide_false, Bool.false_eq_true, Bool.true_eq_false, hg, map_zero, zero_add,
      add_zero]
  all_goals first | rfl | apply add_comm

/-- The downward signed-boundary recursion is preserved by coning. -/
theorem coneCell_signedPart (h : NormalizedSimplexIdentities) {m : ℕ}
    (x : h.object m) (p : ℕ)
    (hx : ∀ a, signedPart a (differential m p (x.table a (p + 1))) = x.table a p)
    (a : Bool) :
    signedPart a (differential (m + 1) (p + 1) ((coneCell h x).table a (p + 2))) =
      (coneCell h x).table a (p + 1) := by
  have hb : differential (m + 1) (p + 1) ((coneCell h x).table a (p + 2)) =
      (coneCell h x).table true (p + 1) - (coneCell h x).table false (p + 1) :=
    (coneCell h x).boundary a (p + 1)
  rw [hb]
  have hd : ∀ a, signedPart a (x.table true p - x.table false p) = x.table a p := by
    intro a
    rw [← x.boundary a p]
    exact hx a
  by_cases he : Even p
  · have heq : (coneCell h x).table true (p + 1) - (coneCell h x).table false (p + 1) =
        prism (coneInclusion m) (coneVertex m) (cone_le m) p
          (x.table true p - x.table false p) +
        mapChains (coneInclusion m) (p + 1) (x.table true (p + 1)) := by
      rw [coneCell_succ_table, coneCell_succ_table]
      simp only [he, decide_true, ↓reduceIte, map_sub]
      abel
    rw [heq, signedPart_cone_add_prefix a _ _ (x.positive true (p + 1)), hd]
    cases a <;> simp [coneCell_succ_table, he]
  · have heq : (coneCell h x).table true (p + 1) - (coneCell h x).table false (p + 1) =
        prism (coneInclusion m) (coneVertex m) (cone_le m) p
          (x.table true p - x.table false p) -
        mapChains (coneInclusion m) (p + 1) (x.table false (p + 1)) := by
      rw [coneCell_succ_table, coneCell_succ_table]
      simp only [he, decide_false, Bool.true_eq_false, ↓reduceIte, add_zero, map_sub]
      abel
    rw [heq, signedPart_cone_sub_prefix a _ _ (x.positive false (p + 1)), hd]
    cases a <;> simp [coneCell_succ_table, he]

end Thomason.Construction.SimplexComplex

end

section

/-!
# Relative prisms under changes of source and target ordinals

The target map need not be injective: repeated images normalize to zero.
These equalities compare whole chain maps and all strict cells, as required
when the finite target chains of different simplices are embedded in one
another during colimit assembly.
-/

namespace Thomason.Construction.SimplexComplex

open CategoryTheory _root_.OAI.Thomason.Construction.DirectedComplex

/-- Appending an upper endpoint commutes with every monotone target map. -/
theorem map_append {n k p : ℕ} (b : Fin (n + 1) →o Fin (k + 1))
    (f : Fin (p + 1) →o Fin (n + 1)) (v : Fin (n + 1)) (hv : f (Fin.last p) ≤ v) :
    b.comp (append f v hv) = append (b.comp f) (b v) (b.monotone hv) := by
  apply DFunLike.ext
  intro i
  induction i using Fin.lastCases with
  | last =>
    exact (congrArg b (append_last f v hv)).trans
      ((append_last (b.comp f) (b v) (b.monotone hv)).symm)
  | cast i =>
    exact (congrArg b (append_castSucc f v hv i)).trans
      ((append_castSucc (b.comp f) (b v) (b.monotone hv) i).symm)

theorem mapChains_rise {m n k : ℕ} (f g : Fin (m + 1) →o Fin (n + 1))
    (hfg : ∀ i, f i ≤ g i) (b : Fin (n + 1) →o Fin (k + 1)) :
    mapChains b (m + 1) (rise f g hfg) =
      rise (b.comp f) (b.comp g) (fun i => b.monotone (hfg i)) := by
  unfold rise
  rw [mapChains_tuple, map_append]
  rfl

/-- Every monotone map of target ordinals preserves the complete prism. -/
theorem prism_postcomp {m n k : ℕ} (f g : Fin (m + 1) →o Fin (n + 1))
    (hfg : ∀ i, f i ≤ g i) (b : Fin (n + 1) →o Fin (k + 1))
    (p : ℕ) (x : Chains m p) :
    mapChains b (p + 1) (prism f g hfg p x) =
      prism (b.comp f) (b.comp g) (fun i => b.monotone (hfg i)) p x := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | single s z =>
    rw [prism_single f g hfg p s z]
    have he := mapChains_rise (f.comp s.toOrderHom) (g.comp s.toOrderHom)
      (fun i => hfg (s i)) b
    have hp := prism_single (b.comp f) (b.comp g)
      (fun i => b.monotone (hfg i)) p s z
    exact (map_smul (mapChains b (p + 1)) z (prismBasis f g hfg p s)).trans
      ((congrArg (fun y => z • y) he).trans hp.symm)

variable (h : NormalizedSimplexIdentities) {m n : ℕ} {A : Set (Fin (m + 1))}
  (hA : IsLowerSet A) (f g : Fin (m + 1) →o Fin (n + 1))
  (hfg : ∀ i, f i ≤ g i) (hagree : ∀ i ∈ A, f i = g i)
  (hconstant : ∀ x ∉ A, ∀ y ∉ A, g x = g y)

/-- The complete strict prism is independent of the chosen enclosing
finite target chain. This also allows noninjective target maps. -/
theorem strictPrism_postcomp {k : ℕ} (b : Fin (n + 1) →o Fin (k + 1)) :
    strictPrism h hA f g hfg hagree hconstant ≫ h.map b =
      strictPrism h hA (b.comp f) (b.comp g) (fun i => b.monotone (hfg i))
        (fun i hi => congrArg b (hagree i hi))
        (fun x hx y hy => congrArg b (hconstant x hx y hy)) := by
  apply StrictOmegaCategory.Hom.ext
  funext x
  apply Cell.ext
  funext a p
  cases p with
  | zero =>
    change mapChains b 0 (mapChains f 0 (x.table a 0).1 + mapChains g 0 (x.table a 0).2) = _
    rw [map_add, mapChains_comp, mapChains_comp]
    rfl
  | succ p =>
    change mapChains b (p + 1) (mapChains f (p + 1) (x.table a (p + 1)).1 +
      mapChains g (p + 1) (x.table a (p + 1)).2.1 + prism f g hfg p (x.table a (p + 1)).2.2) = _
    rw [map_add, map_add, mapChains_comp, mapChains_comp, prism_postcomp]
    rfl

include hA in
/-- Pulling a lower set back along a monotone simplex operator preserves
exactly the relative-prism hypotheses. -/
theorem lowerSet_preimage {l : ℕ} (a : Fin (l + 1) →o Fin (m + 1)) :
    IsLowerSet (a ⁻¹' A) := by
  intro x y hxy hy
  exact hA (a.monotone hxy) hy

/-- Source naturality of the entire strict prism, not merely its top atoms. -/
theorem strictPrism_precomp {l : ℕ} (a : Fin (l + 1) →o Fin (m + 1)) :
    h.cylinderMap a ≫ strictPrism h hA f g hfg hagree hconstant =
      strictPrism h (lowerSet_preimage hA a) (f.comp a) (g.comp a)
        (fun i => hfg (a i)) (fun i hi => hagree (a i) hi)
        (fun x hx y hy => hconstant (a x) hx (a y) hy) := by
  apply StrictOmegaCategory.Hom.ext
  funext x
  apply Cell.ext
  funext b p
  cases p with
  | zero =>
    change mapChains f 0 (mapChains a 0 (x.table b 0).1) +
      mapChains g 0 (mapChains a 0 (x.table b 0).2) = _
    rw [mapChains_comp, mapChains_comp]
    rfl
  | succ p =>
    change mapChains f (p + 1) (mapChains a (p + 1) (x.table b (p + 1)).1) +
      mapChains g (p + 1) (mapChains a (p + 1) (x.table b (p + 1)).2.1) +
      prism f g hfg p (mapChains a p (x.table b (p + 1)).2.2) = _
    rw [mapChains_comp, mapChains_comp, prism_precomp]
    rfl

end Thomason.Construction.SimplexComplex

end

section

/-!
# Finite ordered targets of relative prisms in arbitrary posets

The union of the two vertex-image lists is a chain under the relative
sieve/constancy hypotheses. We construct this chain and ordinal models
whose transition maps preserve the actual vertices. This supplies the
finite targets in the simplexwise relative-prism construction.
-/

namespace Thomason.Construction

open PartialOrder

namespace RelativePrismImage

variable {E : Type} [PartialOrder E] {A : Set E} (hA : IsLowerSet A)
  (f g : E →o E) (hfg : ∀ x, f x ≤ g x)
  (hagree : ∀ x ∈ A, f x = g x)
  (hconstant : ∀ x ∉ A, ∀ y ∉ A, g x = g y)

include hA hfg hagree hconstant

/-- Every lower image is comparable with every upper image in a simplex. -/
theorem mixed_comparable {m : ℕ} (s : Fin (m + 1) →o E) (i j : Fin (m + 1)) :
    f (s i) ≤ g (s j) ∨ g (s j) ≤ f (s i) := by
  by_cases hij : i ≤ j
  · exact Or.inl ((f.monotone (s.monotone hij)).trans (hfg _))
  · have hji : j ≤ i := le_of_lt (lt_of_not_ge hij)
    by_cases hj : s j ∈ A
    · exact Or.inr ((hagree (s j) hj).symm ▸ f.monotone (s.monotone hji))
    · have hi : s i ∉ A := fun hi => hj (hA (s.monotone hji) hi)
      exact Or.inl ((hconstant (s i) hi (s j) hj) ▸ hfg (s i))

/-- The actual finite chain containing both endpoint vertex lists. -/
noncomputable def chain {m : ℕ} (s : Fin (m + 1) →o E) : NonemptyFiniteChains E := by
  classical
  refine ⟨Finset.univ.image (fun i => f (s i)) ∪ Finset.univ.image (fun i => g (s i)), ?_, ?_⟩
  · exact ⟨f (s 0), Finset.mem_union_left _ (Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩)⟩
  · rintro ⟨x, hx⟩ ⟨y, hy⟩
    change x ≤ y ∨ y ≤ x
    simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and] at hx hy
    rcases hx with ⟨i, rfl⟩ | ⟨i, rfl⟩ <;> rcases hy with ⟨j, rfl⟩ | ⟨j, rfl⟩
    · exact (le_total i j).imp (fun hij => f.monotone (s.monotone hij))
        (fun hji => f.monotone (s.monotone hji))
    · exact mixed_comparable hA f g hfg hagree hconstant s i j
    · exact (mixed_comparable hA f g hfg hagree hconstant s j i).symm
    · exact (le_total i j).imp (fun hij => g.monotone (s.monotone hij))
        (fun hji => g.monotone (s.monotone hji))

@[simp]
theorem mem_chain {m : ℕ} (s : Fin (m + 1) →o E) (x : E) :
    x ∈ (chain hA f g hfg hagree hconstant s).finset ↔
      (∃ i, f (s i) = x) ∨ (∃ i, g (s i) = x) := by
  classical
  simp [chain]

/-- Every simplex operator induces inclusion of the finite prism targets. -/
theorem chain_precomp_le {l m : ℕ} (s : Fin (m + 1) →o E)
    (a : Fin (l + 1) →o Fin (m + 1)) :
    chain hA f g hfg hagree hconstant (s.comp a) ≤ chain hA f g hfg hagree hconstant s := by
  intro x hx
  rw [mem_chain] at hx ⊢
  rcases hx with ⟨i, hi⟩ | ⟨i, hi⟩
  · exact Or.inl ⟨a i, hi⟩
  · exact Or.inr ⟨a i, hi⟩

end RelativePrismImage

/-- An ordinal enumeration of a nonempty finite chain in a poset. -/
structure ChainOrdinal {E : Type} [PartialOrder E] (S : NonemptyFiniteChains E) where
  dim : ℕ
  enum : Fin (dim + 1) ≃o S.finset

namespace ChainOrdinal

variable {E : Type} [PartialOrder E]

/-- Every nonempty finite chain has an increasing enumeration. -/
noncomputable def choose (S : NonemptyFiniteChains E) : ChainOrdinal S := by
  classical
  have hs : IsChain (· < ·) (S.finset : Set E) := by
    intro x hx y hy hne
    rcases S.comparable ⟨x, hx⟩ ⟨y, hy⟩ with hxy | hyx
    · exact Or.inl (lt_of_le_of_ne hxy hne)
    · exact Or.inr (lt_of_le_of_ne hyx hne.symm)
  letI : LinearOrder S.finset := hs.linearOrder
  refine ⟨S.finset.card - 1, Fintype.orderIsoFinOfCardEq S.finset ?_⟩
  rw [Fintype.card_coe]
  have hp := Finset.card_pos.mpr S.nonempty
  omega

variable {S T U : NonemptyFiniteChains E}

/-- Inclusion of the underlying finite chains, with no re-enumeration. -/
def inclusion (hST : S ≤ T) : S.finset →o T.finset where
  toFun x := ⟨x.val, hST x.property⟩
  monotone' := fun _ _ h => h

/-- The ordinal map encoding a chain inclusion under the chosen enumerations. -/
def map (s : ChainOrdinal S) (t : ChainOrdinal T) (hST : S ≤ T) :
    Fin (s.dim + 1) →o Fin (t.dim + 1) :=
  (OrderIso.toOrderEmbedding t.enum.symm).toOrderHom.comp ((inclusion hST).comp (OrderIso.toOrderEmbedding s.enum).toOrderHom)

@[simp]
theorem enum_map (s : ChainOrdinal S) (t : ChainOrdinal T) (hST : S ≤ T)
    (i : Fin (s.dim + 1)) : ((t.enum (map s t hST i)) : E) = ((s.enum i) : E) := by
  change ((t.enum (t.enum.symm (inclusion hST (s.enum i)))) : E) = _
  rw [OrderIso.apply_symm_apply]
  rfl

/-- The transition maps are coherent under nested target chains. -/
theorem map_comp (s : ChainOrdinal S) (t : ChainOrdinal T) (u : ChainOrdinal U)
    (hST : S ≤ T) (hTU : T ≤ U) :
    (map t u hTU).comp (map s t hST) = map s u (hST.trans hTU) := by
  apply DFunLike.ext
  intro i
  apply u.enum.injective
  apply Subtype.ext
  simp only [OrderHom.comp_coe, Function.comp_apply, enum_map]

@[simp]
theorem map_refl (s : ChainOrdinal S) : map s s le_rfl = OrderHom.id := by
  apply DFunLike.ext
  intro i
  apply s.enum.injective
  apply Subtype.ext
  exact enum_map s s le_rfl i

end ChainOrdinal
end Thomason.Construction

end

section

/-!
# Compatible finite models of a relative poset prism

The image of each simplex admits a finite ordinal model. Both endpoint
maps, their inequality, the relative hypotheses, and every simplex operator
are transported to these models. The resulting strict chain prisms agree
on all cells, so they can be assembled by a colimit universal property.
-/

namespace Thomason.Construction

open CategoryTheory PartialOrder

/-- The poset data used by the relative prism construction. -/
structure RelativePrismData (E : Type) [PartialOrder E] where
  old : Set E
  lower : IsLowerSet old
  first : E →o E
  last : E →o E
  le : ∀ x, first x ≤ last x
  agree : ∀ x ∈ old, first x = last x
  constant : ∀ x ∉ old, ∀ y ∉ old, last x = last y

namespace RelativePrismData

variable {E : Type} [PartialOrder E] (D : RelativePrismData E)

noncomputable def image {m : ℕ} (s : Fin (m + 1) →o E) : NonemptyFiniteChains E :=
  RelativePrismImage.chain D.lower D.first D.last D.le D.agree D.constant s

noncomputable def ordinal {m : ℕ} (s : Fin (m + 1) →o E) : ChainOrdinal (D.image s) :=
  ChainOrdinal.choose (D.image s)

noncomputable def evaluate {m : ℕ} (s : Fin (m + 1) →o E) :
    Fin ((D.ordinal s).dim + 1) →o E where
  toFun i := ((D.ordinal s).enum i).val
  monotone' := fun _ _ hij => (D.ordinal s).enum.monotone hij

noncomputable def firstIndex {m : ℕ} (s : Fin (m + 1) →o E) :
    Fin (m + 1) →o Fin ((D.ordinal s).dim + 1) where
  toFun i := (D.ordinal s).enum.symm ⟨D.first (s i),
    (RelativePrismImage.mem_chain D.lower D.first D.last D.le D.agree D.constant s _).mpr
      (Or.inl ⟨i, rfl⟩)⟩
  monotone' := fun _ _ hij => (D.ordinal s).enum.symm.monotone (D.first.monotone (s.monotone hij))

noncomputable def lastIndex {m : ℕ} (s : Fin (m + 1) →o E) :
    Fin (m + 1) →o Fin ((D.ordinal s).dim + 1) where
  toFun i := (D.ordinal s).enum.symm ⟨D.last (s i),
    (RelativePrismImage.mem_chain D.lower D.first D.last D.le D.agree D.constant s _).mpr
      (Or.inr ⟨i, rfl⟩)⟩
  monotone' := fun _ _ hij => (D.ordinal s).enum.symm.monotone (D.last.monotone (s.monotone hij))

@[simp]
theorem evaluate_firstIndex {m : ℕ} (s : Fin (m + 1) →o E) (i : Fin (m + 1)) :
    D.evaluate s (D.firstIndex s i) = D.first (s i) := by
  change ((D.ordinal s).enum ((D.ordinal s).enum.symm _) : E) = _
  rw [OrderIso.apply_symm_apply]

@[simp]
theorem evaluate_lastIndex {m : ℕ} (s : Fin (m + 1) →o E) (i : Fin (m + 1)) :
    D.evaluate s (D.lastIndex s i) = D.last (s i) := by
  change ((D.ordinal s).enum ((D.ordinal s).enum.symm _) : E) = _
  rw [OrderIso.apply_symm_apply]

theorem evaluate_injective {m : ℕ} (s : Fin (m + 1) →o E) :
    Function.Injective (D.evaluate s) := by
  intro i j hij
  apply (D.ordinal s).enum.injective
  exact Subtype.ext hij

theorem index_le {m : ℕ} (s : Fin (m + 1) →o E) (i : Fin (m + 1)) :
    D.firstIndex s i ≤ D.lastIndex s i :=
  (D.ordinal s).enum.symm.monotone (D.le (s i))

theorem index_agree {m : ℕ} (s : Fin (m + 1) →o E) (i : Fin (m + 1))
    (hi : i ∈ s ⁻¹' D.old) : D.firstIndex s i = D.lastIndex s i := by
  apply D.evaluate_injective s
  simpa only [evaluate_firstIndex, evaluate_lastIndex] using D.agree (s i) hi

theorem index_constant {m : ℕ} (s : Fin (m + 1) →o E) (i : Fin (m + 1))
    (hi : i ∉ s ⁻¹' D.old) (j : Fin (m + 1)) (hj : j ∉ s ⁻¹' D.old) :
    D.lastIndex s i = D.lastIndex s j := by
  apply D.evaluate_injective s
  simpa only [evaluate_lastIndex] using D.constant (s i) hi (s j) hj

theorem old_preimage_lower {m : ℕ} (s : Fin (m + 1) →o E) :
    IsLowerSet (s ⁻¹' D.old) :=
  fun _ _ hij hj => D.lower (s.monotone hij) hj

noncomputable def transition {l m : ℕ} (s : Fin (m + 1) →o E)
    (a : Fin (l + 1) →o Fin (m + 1)) :
    Fin ((D.ordinal (s.comp a)).dim + 1) →o Fin ((D.ordinal s).dim + 1) :=
  ChainOrdinal.map (D.ordinal (s.comp a)) (D.ordinal s)
    (RelativePrismImage.chain_precomp_le D.lower D.first D.last D.le D.agree D.constant s a)

@[simp]
theorem evaluate_transition {l m : ℕ} (s : Fin (m + 1) →o E)
    (a : Fin (l + 1) →o Fin (m + 1)) (i : Fin ((D.ordinal (s.comp a)).dim + 1)) :
    D.evaluate s (D.transition s a i) = D.evaluate (s.comp a) i :=
  ChainOrdinal.enum_map _ _ _ i

theorem transition_first {l m : ℕ} (s : Fin (m + 1) →o E)
    (a : Fin (l + 1) →o Fin (m + 1)) :
    (D.transition s a).comp (D.firstIndex (s.comp a)) = (D.firstIndex s).comp a := by
  apply DFunLike.ext
  intro i
  apply D.evaluate_injective s
  simp only [OrderHom.comp_coe, Function.comp_apply, evaluate_transition, evaluate_firstIndex]

theorem transition_last {l m : ℕ} (s : Fin (m + 1) →o E)
    (a : Fin (l + 1) →o Fin (m + 1)) :
    (D.transition s a).comp (D.lastIndex (s.comp a)) = (D.lastIndex s).comp a := by
  apply DFunLike.ext
  intro i
  apply D.evaluate_injective s
  simp only [OrderHom.comp_coe, Function.comp_apply, evaluate_transition, evaluate_lastIndex]

/-- The local strict prism takes values in the oriental of the finite image chain. -/
noncomputable def localPrism (h : NormalizedSimplexIdentities) {m : ℕ}
    (s : Fin (m + 1) →o E) : h.cylinderObject m ⟶ h.object (D.ordinal s).dim :=
  SimplexComplex.strictPrism h (D.old_preimage_lower s) (D.firstIndex s) (D.lastIndex s)
    (D.index_le s) (D.index_agree s) (D.index_constant s)

/-- The relative set certifies positivity; the actual map depends only on
its two endpoint lists. -/
theorem localPrism_congr (h : NormalizedSimplexIdentities) {m n : ℕ}
    {A B : Set (Fin (m + 1))} (hA : IsLowerSet A) (hB : IsLowerSet B)
    (f g f' g' : Fin (m + 1) →o Fin (n + 1))
    (hfg : ∀ i, f i ≤ g i) (hfg' : ∀ i, f' i ≤ g' i)
    (ha : ∀ i ∈ A, f i = g i) (ha' : ∀ i ∈ B, f' i = g' i)
    (hc : ∀ x ∉ A, ∀ y ∉ A, g x = g y)
    (hc' : ∀ x ∉ B, ∀ y ∉ B, g' x = g' y)
    (hf : f = f') (hg : g = g') :
    SimplexComplex.strictPrism h hA f g hfg ha hc =
      SimplexComplex.strictPrism h hB f' g' hfg' ha' hc' := by
  subst f'
  subst g'
  rfl

/-- All faces and degeneracies commute with the local strict prism, after
embedding its finite target chain in the larger target chain. -/
theorem localPrism_naturality (h : NormalizedSimplexIdentities) {l m : ℕ}
    (s : Fin (m + 1) →o E) (a : Fin (l + 1) →o Fin (m + 1)) :
    h.cylinderMap a ≫ D.localPrism h s =
      D.localPrism h (s.comp a) ≫ h.map (D.transition s a) := by
  have hsource := SimplexComplex.strictPrism_precomp h (D.old_preimage_lower s)
    (D.firstIndex s) (D.lastIndex s) (D.index_le s) (D.index_agree s)
    (D.index_constant s) a
  have htarget := SimplexComplex.strictPrism_postcomp h (D.old_preimage_lower (s.comp a))
    (D.firstIndex (s.comp a)) (D.lastIndex (s.comp a))
    (D.index_le (s.comp a)) (D.index_agree (s.comp a))
    (D.index_constant (s.comp a)) (D.transition s a)
  exact hsource.trans ((localPrism_congr h _ _ _ _ _ _ _ _ _ _ _ _
    (D.transition_first s a).symm (D.transition_last s a).symm).trans htarget.symm)

end RelativePrismData
end Thomason.Construction

end

section

/-!
# Assembly of the relative prism on a categorified poset nerve

The finite target chains and their transition maps are used to glue the
explicit chain prisms. This construction applies to arbitrary posets and
all their simplices, including degenerate ones.
-/

namespace Thomason.Construction.RelativePrismData

open CategoryTheory CategoryTheory.Limits Opposite NormalizedSimplexIdentities

variable {E : Type} [PartialOrder E] (D : RelativePrismData E)
  (h : NormalizedSimplexIdentities) [StrictColimitsInput]

/-- The finite local chain prism, now with values in the categorified nerve. -/
noncomputable def chainPiece {m : ℕ} (s : Fin (m + 1) →o E) :
    h.cylinderObject m ⟶ h.categorification.obj (nerve E) :=
  D.localPrism h s ≫ h.posetLeg (D.evaluate s)

/-- No choice of finite target is visible in the glued local maps. -/
theorem chainPiece_naturality {l m : ℕ} (s : Fin (m + 1) →o E)
    (a : Fin (l + 1) →o Fin (m + 1)) :
    h.cylinderMap a ≫ D.chainPiece h s = D.chainPiece h (s.comp a) := by
  have he : (D.evaluate s).comp (D.transition s a) = D.evaluate (s.comp a) := by
    apply DFunLike.ext
    exact D.evaluate_transition s a
  let p : h.cylinderObject m ⟶ h.object (D.ordinal s).dim := D.localPrism h s
  let q : h.cylinderObject l ⟶ h.object (D.ordinal (s.comp a)).dim := D.localPrism h (s.comp a)
  let b : h.object (D.ordinal (s.comp a)).dim ⟶ h.object (D.ordinal s).dim :=
    h.map (D.transition s a)
  let t := h.posetLeg (D.evaluate s)
  have hn : h.cylinderMap a ≫ p = q ≫ b := D.localPrism_naturality h s a
  have ht : b ≫ t = h.posetLeg (D.evaluate (s.comp a)) :=
    (h.posetLeg_precomp (D.evaluate s) (D.transition s a)).trans (congrArg h.posetLeg he)
  change h.cylinderMap a ≫ (p ≫ t) = q ≫ h.posetLeg (D.evaluate (s.comp a))
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun k => k ≫ t) hn).trans
      ((Category.assoc _ _ _).trans (congrArg (fun k => q ≫ k) ht)))

variable (G : RightGrayInput h)

/-- Transport of a local piece to the right Gray cylinder. -/
noncomputable def piece {m : ℕ} (s : Fin (m + 1) →o E) :
    G.cylinder.obj (h.object m) ⟶ h.categorification.obj (nerve E) :=
  G.simplexComparison.inv.app (.mk m) ≫ D.chainPiece h s

theorem piece_naturality {l m : ℕ} (s : Fin (m + 1) →o E)
    (a : Fin (l + 1) →o Fin (m + 1)) :
    G.cylinder.map (h.map a) ≫ D.piece h G s = D.piece h G (s.comp a) := by
  let il : G.cylinder.obj (h.object l) ⟶ h.cylinderObject l :=
    G.simplexComparison.inv.app (.mk l)
  let im : G.cylinder.obj (h.object m) ⟶ h.cylinderObject m :=
    G.simplexComparison.inv.app (.mk m)
  have hn : G.cylinder.map (h.map a) ≫ im = il ≫ h.cylinderMap a :=
    G.simplexComparison.inv.naturality (SimplexCategory.Hom.mk a)
  change G.cylinder.map (h.map a) ≫ (im ≫ D.chainPiece h s) =
    il ≫ D.chainPiece h (s.comp a)
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun k => k ≫ D.chainPiece h s) hn).trans
      ((Category.assoc _ _ _).trans
        (congrArg (fun k => il ≫ k) (D.chainPiece_naturality h s a))))

/-- The local maps form a cocone over the actual simplex presentation. -/
theorem pieces_compatible {i j : CostructuredArrow SSet.stdSimplex (nerve E)} (a : i ⟶ j) :
    G.cylinder.map (h.cosimplicial.map a.left) ≫
        D.piece h G (simplexOrder (SSet.yonedaEquiv j.hom)) =
      D.piece h G (simplexOrder (SSet.yonedaEquiv i.hom)) := by
  have he : (simplexOrder (SSet.yonedaEquiv j.hom)).comp a.left.toOrderHom =
      simplexOrder (SSet.yonedaEquiv i.hom) :=
    (simplexOrder_precomp j.hom a.left).symm.trans
      (congrArg (fun k => simplexOrder (SSet.yonedaEquiv k)) (CostructuredArrow.w a))
  exact (D.piece_naturality h G (simplexOrder (SSet.yonedaEquiv j.hom)) a.left.toOrderHom).trans
    (congrArg (D.piece h G) he)

/-- Existence and uniqueness of the assembled strict relative prism. -/
theorem exists_prism :
    ∃! P : G.cylinder.obj (h.categorification.obj (nerve E)) ⟶ h.categorification.obj (nerve E),
      ∀ s : CostructuredArrow SSet.stdSimplex (nerve E),
        G.cylinder.map (h.simplexLeg s.hom) ≫ P =
          D.piece h G (simplexOrder (SSet.yonedaEquiv s.hom)) := by
  exact G.assemble_cylinder (h.simplexCocone_isColimit (nerve E))
    (fun s => D.piece h G (simplexOrder (SSet.yonedaEquiv s.hom))) (fun a => D.pieces_compatible h G a)

/-- The strict cylinder is defined using the proved unique assembly. -/
noncomputable def prism :
    G.cylinder.obj (h.categorification.obj (nerve E)) ⟶ h.categorification.obj (nerve E) :=
  (D.exists_prism h G).choose

theorem prism_fac (s : CostructuredArrow SSet.stdSimplex (nerve E)) :
    G.cylinder.map (h.simplexLeg s.hom) ≫ D.prism h G =
      D.piece h G (simplexOrder (SSet.yonedaEquiv s.hom)) :=
  (D.exists_prism h G).choose_spec.1 s

end Thomason.Construction.RelativePrismData

end

section

/-!
# Endpoints of the assembled poset prism

The glued map is a strict cylinder between the two actual categorified
poset endomorphisms. The proof uses the entire simplex presentation.
-/

namespace Thomason.Construction.RelativePrismData

open CategoryTheory CategoryTheory.Limits Opposite NormalizedSimplexIdentities

variable {E : Type} [PartialOrder E] (D : RelativePrismData E)
  (h : NormalizedSimplexIdentities) [StrictColimitsInput] (G : RightGrayInput h)

/-- The local endpoint equation survives passage from the finite image
chain to the whole poset. -/
theorem piece_endpoint {m : ℕ} (s : Fin (m + 1) →o E) (a : Bool) :
    (G.endpoint a).app (h.object m) ≫ D.piece h G s =
      h.posetLeg ((if a then D.last else D.first).comp s) := by
  let p : G.cylinder.obj (h.object m) ⟶ h.object (D.ordinal s).dim :=
    G.prism (D.old_preimage_lower s) (D.firstIndex s) (D.lastIndex s)
      (D.index_le s) (D.index_agree s) (D.index_constant s)
  let v : h.object (D.ordinal s).dim ⟶ h.categorification.obj (nerve E) :=
    h.posetLeg (D.evaluate s)
  have hp : (G.endpoint a).app (h.object m) ≫ p =
      h.map (if a then D.lastIndex s else D.firstIndex s) :=
    G.prism_endpoint (D.old_preimage_lower s) (D.firstIndex s) (D.lastIndex s)
      (D.index_le s) (D.index_agree s) (D.index_constant s) a
  have he : (D.evaluate s).comp (if a then D.lastIndex s else D.firstIndex s) =
      (if a then D.last else D.first).comp s := by
    apply DFunLike.ext
    intro i
    cases a
    · exact D.evaluate_firstIndex s i
    · exact D.evaluate_lastIndex s i
  have hpiece : D.piece h G s = p ≫ v := (Category.assoc _ _ _).symm
  calc
    _ = (G.endpoint a).app (h.object m) ≫ (p ≫ v) := congrArg (fun k => _ ≫ k) hpiece
    _ = ((G.endpoint a).app (h.object m) ≫ p) ≫ v := (Category.assoc _ _ _).symm
    _ = h.map (if a then D.lastIndex s else D.firstIndex s) ≫ v := congrArg (fun k => k ≫ v) hp
    _ = h.posetLeg ((D.evaluate s).comp (if a then D.lastIndex s else D.firstIndex s)) :=
      h.posetLeg_precomp _ _
    _ = _ := congrArg h.posetLeg he

/-- The assembled prism restricts to the specified piece on every simplex. -/
theorem prism_fac_poset {m : ℕ} (s : Fin (m + 1) →o E) :
    G.cylinder.map (h.posetLeg s) ≫ D.prism h G = D.piece h G s := by
  have hf := D.prism_fac h G (CostructuredArrow.mk (SSet.yonedaEquiv.symm (orderSimplex s)))
  change G.cylinder.map (h.posetLeg s) ≫ D.prism h G =
    D.piece h G (simplexOrder (SSet.yonedaEquiv (SSet.yonedaEquiv.symm (orderSimplex s)))) at hf
  simpa only [Equiv.apply_symm_apply, simplexOrder_orderSimplex] using hf

/-- Both endpoints are the actual functors induced on categorifications. -/
theorem prism_endpoint (a : Bool) :
    (G.endpoint a).app (h.categorification.obj (nerve E)) ≫ D.prism h G =
      h.categorification.map (nerveMap (if a then D.last else D.first).monotone.functor) := by
  apply G.assembled_endpoint (h.simplexCocone_isColimit (nerve E))
  intro j
  let s := simplexOrder (SSet.yonedaEquiv j.hom)
  have hf : G.cylinder.map (h.posetLeg s) ≫ D.prism h G = D.piece h G s :=
    D.prism_fac_poset h G s
  have hj : h.posetLeg s = h.simplexLeg j.hom := h.posetLeg_simplexOrder j.hom
  change (G.endpoint a).app (h.object j.left.len) ≫
      G.cylinder.map (h.simplexLeg j.hom) ≫ D.prism h G =
    h.simplexLeg j.hom ≫ _
  calc
    _ = (G.endpoint a).app (h.object j.left.len) ≫
        (G.cylinder.map (h.posetLeg s) ≫ D.prism h G) := by rw [hj]
    _ = (G.endpoint a).app (h.object j.left.len) ≫ D.piece h G s := congrArg (fun k => _ ≫ k) hf
    _ = h.posetLeg ((if a then D.last else D.first).comp s) := D.piece_endpoint h G s a
    _ = h.posetLeg s ≫ h.categorification.map
        (nerveMap (if a then D.last else D.first).monotone.functor) :=
      (h.posetLeg_postcomp s (if a then D.last else D.first)).symm
    _ = _ := congrArg (fun k => k ≫ _) hj

end Thomason.Construction.RelativePrismData

end

end OAI
