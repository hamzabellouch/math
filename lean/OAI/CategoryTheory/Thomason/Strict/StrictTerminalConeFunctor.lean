import OAI.CategoryTheory.Thomason.Gray.CylinderAssembly
import OAI.CategoryTheory.Thomason.Simplicial.SimplicialSpanFactorization
import OAI.CategoryTheory.Thomason.Strict.StrictIsomorphisms
import OAI.CategoryTheory.Thomason.Strict.StrictTerminalConeCategory
import OAI.CategoryTheory.Thomason.Strict.UnderlyingCategory
import Mathlib.Order.Interval.Set.OrdConnected
import Mathlib.Order.UpperLower.Basic

namespace OAI

section

/-! # Constructed ordered vertex maps of strict oriental functors

The explicitly constructed interval cell supplies a cell between any two ordered vertices. No composition-generation theorem is needed.
Consequently a strict functor from an oriental to a poset is precisely its
monotone vertex map. This will detect full sieve fibres at the last vertex.
-/

namespace Thomason.Construction.NormalizedSimplexIdentities

open CategoryTheory StrictOmegaCategory

variable (h : NormalizedSimplexIdentities)

/-- The ordinal map selecting a possibly degenerate edge. -/
def edgeOrder {m : ℕ} (i j : Fin (m + 1)) (hij : i ≤ j) : Fin 2 →o Fin (m + 1) where
  toFun k := if k = 0 then i else j
  monotone' := by
    intro x y hxy
    dsimp
    split_ifs with hx hy hy
    · exact le_rfl
    · exact hij
    · have : x = 0 := by omega
      exact (hx this).elim
    · exact le_rfl

/-- An actual oriental cell from `i` to `j`. -/
noncomputable def edge {m : ℕ} (i j : Fin (m + 1)) (hij : i ≤ j) : h.object m :=
  (h.map (edgeOrder i j hij)).toFun (SimplexComplex.principalCell h 1)

theorem edge_source {m : ℕ} (i j : Fin (m + 1)) (hij : i ≤ j) :
    (h.object m).source 0 (h.edge i j hij) = SimplexComplex.vertex h i := by
  exact ((h.map (edgeOrder i j hij)).map_face false 0 (SimplexComplex.principalCell h 1)).symm.trans
    ((congrArg (h.map (edgeOrder i j hij)).toFun (SimplexComplex.principalCell_source h 1)).trans
      ((SimplexComplex.map_vertex h _ 0).trans (by rfl)))

theorem edge_target {m : ℕ} (i j : Fin (m + 1)) (hij : i ≤ j) :
    (h.object m).target 0 (h.edge i j hij) = SimplexComplex.vertex h j := by
  exact ((h.map (edgeOrder i j hij)).map_face true 0 (SimplexComplex.principalCell h 1)).symm.trans
    ((congrArg (h.map (edgeOrder i j hij)).toFun (SimplexComplex.principalCell_target h 1)).trans
      ((SimplexComplex.map_vertex h _ (Fin.last 1)).trans (by rfl)))

variable {E : Type} [Preorder E] {m : ℕ}

/-- Read the monotone vertex function of a strict functor into a poset. -/
noncomputable def vertexOrder (f : h.object m ⟶ StrictPoset.category E) :
    Fin (m + 1) →o E where
  toFun i := (f.toFun (SimplexComplex.vertex h i)).first
  monotone' := by
    intro i j hij
    have hs := (f.map_face false 0 (h.edge i j hij)).symm.trans
      (congrArg f.toFun (h.edge_source i j hij))
    have ht := (f.map_face true 0 (h.edge i j hij)).symm.trans
      (congrArg f.toFun (h.edge_target i j hij))
    have hsf := congrArg (fun z : StrictPoset.Cell E => z.first) hs
    have htf := congrArg (fun z : StrictPoset.Cell E => z.first) ht
    change (f.toFun (h.edge i j hij)).first = _ at hsf
    change (f.toFun (h.edge i j hij)).last = _ at htf
    exact hsf.symm.trans_le ((f.toFun (h.edge i j hij)).ordered.trans_eq htf)

/-- The label of a vertex is its identity cell, not just its first endpoint. -/
theorem vertexOrder_label (f : h.object m ⟶ StrictPoset.category E)
    (i : Fin (m + 1)) :
    f.toFun (SimplexComplex.vertex h i) = StrictPoset.identity (h.vertexOrder f i) := by
  have he := (f.map_face false 0 (SimplexComplex.vertex h i)).symm.trans
    (congrArg f.toFun (SimplexComplex.vertex_dimensionLE h i).1)
  exact he.symm

/-- Every strict poset label of an oriental factors through its ordinal label. -/
theorem eq_ordinalLabel_vertexOrder (f : h.object m ⟶ StrictPoset.category E) :
    f = h.ordinalLabel m ≫ StrictPoset.map (h.vertexOrder f) := by
  apply StrictOmegaCategory.hom_poset_ext
  intro x
  obtain ⟨i, hi⟩ := SimplexComplex.eq_vertex_of_dimensionLE h x.val x.property
  change f.toFun x.val = (StrictPoset.map (h.vertexOrder f)).toFun ((h.ordinalLabel m).toFun x.val)
  rw [hi, h.ordinalLabel_vertex]
  exact h.vertexOrder_label f i

include h

/-- A binary strict label vanishes on every cell exactly when it vanishes at the last vertex. -/
theorem label_zero_iff_last (f : h.object m ⟶ StrictPoset.category (Fin 2)) :
    (∀ x, f.toFun x = StrictPoset.identity 0) ↔
      f.toFun (SimplexComplex.vertex h (Fin.last m)) = StrictPoset.identity 0 := by
  constructor
  · exact fun hf => hf _
  · intro hf x
    have hl : h.vertexOrder f (Fin.last m) = 0 :=
      congrArg (fun z : StrictPoset.Cell (Fin 2) => z.first) hf
    have hv : ∀ i, h.vertexOrder f i = 0 := fun i =>
      le_antisymm (((h.vertexOrder f).monotone (Fin.le_last i)).trans_eq hl) (Fin.zero_le _)
    have he := congrArg (fun k : h.object m ⟶ StrictPoset.category (Fin 2) => k.toFun x)
      (h.eq_ordinalLabel_vertexOrder f)
    exact he.trans (StrictPoset.Cell.ext (hv _) (hv _))

/-- Dually the initial vertex detects the entire one-fibre. -/
theorem label_one_iff_first (f : h.object m ⟶ StrictPoset.category (Fin 2)) :
    (∀ x, f.toFun x = StrictPoset.identity 1) ↔
      f.toFun (SimplexComplex.vertex h 0) = StrictPoset.identity 1 := by
  constructor
  · exact fun hf => hf _
  · intro hf x
    have hl : h.vertexOrder f 0 = 1 :=
      congrArg (fun z : StrictPoset.Cell (Fin 2) => z.first) hf
    have hv : ∀ i, h.vertexOrder f i = 1 := by
      intro i
      apply le_antisymm
      · exact Fin.le_last _
      · exact hl ▸ (h.vertexOrder f).monotone (Fin.zero_le i)
    have he := congrArg (fun k : h.object m ⟶ StrictPoset.category (Fin 2) => k.toFun x)
      (h.eq_ordinalLabel_vertexOrder f)
    exact he.trans (StrictPoset.Cell.ext (hv _) (hv _))

end Thomason.Construction.NormalizedSimplexIdentities

end

section

/-!
# Positive finite dimensions and right-cylinder descent

The reflection adjunction is the one from
Ara--Maltsiniotis (2014), Section 5.8. The right-interval internal-hom
truncation is the specialization of Ara--Maltsiniotis (2020), Proposition
A.29. We derive the cylinder factorization and the finite Street-nerve
adjunctions from these inputs, on the actual full subcategories of strict
omega-categories. Here the finite dimension is `n + 1`.
-/

namespace Thomason.Construction

open CategoryTheory

/-- Intelligent truncation into positive finite dimension. -/
structure FiniteReflectionInput (n : ℕ) where
  reflect : StrictOmegaCategory.{0} ⥤ StrictOmegaCategory.Truncated.{0} (n + 1)
  adjunction : reflect ⊣ StrictOmegaCategory.inclusion (n + 1)

/-- Right-interval internal hom preserves the finite dimension bound. -/
structure GrayTruncationInput {h : NormalizedSimplexIdentities} (G : RightGrayInput h) : Prop where
  truncated (n : ℕ) (Y : StrictOmegaCategory.Truncated.{0} (n + 1)) :
    (G.internalHom.obj Y.val).IsTruncated (n + 1)

namespace FiniteReflectionInput

variable {n : ℕ} (r : FiniteReflectionInput n)
  (h : NormalizedSimplexIdentities) [StrictColimitsInput]

noncomputable def categorification : SSet.{0} ⥤ StrictOmegaCategory.Truncated.{0} (n + 1) :=
  h.categorification ⋙ r.reflect

noncomputable def categorificationAdjunction :
    r.categorification h ⊣ h.finiteStreetNerve (n + 1) :=
  h.categorificationAdjunction.comp r.adjunction

noncomputable def thomasonLeft : SSet.{0} ⥤ StrictOmegaCategory.Truncated.{0} (n + 1) :=
  (SSet.sd ⋙ SSet.sd) ⋙ r.categorification h

noncomputable def thomasonAdjunction : r.thomasonLeft h ⊣
    (h.finiteStreetNerve (n + 1) ⋙ SSet.ex ⋙ SSet.ex) :=
  (SSet.sdExAdjunction.comp SSet.sdExAdjunction).comp (r.categorificationAdjunction h)

end FiniteReflectionInput

namespace RightGrayInput

variable {h : NormalizedSimplexIdentities} (G : RightGrayInput h)
  (t : GrayTruncationInput G) {n : ℕ} (r : FiniteReflectionInput n)

/-- The adjunction chain giving restriction of cylinders along the reflection
unit. Its target is an actual finite-dimensional strict category. -/
noncomputable def cylinderRestrictionEquiv (X : StrictOmegaCategory.{0})
    (Y : StrictOmegaCategory.Truncated.{0} (n + 1)) :
    (G.cylinder.obj (r.reflect.obj X).val ⟶ Y.val) ≃ (G.cylinder.obj X ⟶ Y.val) :=
  (G.adjunction.homEquiv (r.reflect.obj X).val Y.val).trans
    ((r.adjunction.homEquiv X ⟨G.internalHom.obj Y.val, t.truncated n Y⟩).trans
      (G.adjunction.homEquiv X Y.val).symm)

/-- The abstract adjunction bijection is precisely precomposition with
`q_X ⊗ id`, not a different unidentified equivalence. -/
theorem cylinderRestrictionEquiv_apply (X : StrictOmegaCategory.{0})
    (Y : StrictOmegaCategory.Truncated.{0} (n + 1))
    (P : G.cylinder.obj (r.reflect.obj X).val ⟶ Y.val) :
    G.cylinderRestrictionEquiv t r X Y P = G.cylinder.map (r.adjunction.unit.app X) ≫ P := by
  let Z : StrictOmegaCategory := Y.val
  let R : StrictOmegaCategory := (r.reflect.obj X).val
  let H : StrictOmegaCategory.Truncated (n + 1) :=
    ⟨G.internalHom.obj Z, t.truncated n Y⟩
  let e₁ : (G.cylinder.obj R ⟶ Z) ≃ (R ⟶ H.val) := G.adjunction.homEquiv R Z
  let e₂ : (R ⟶ H.val) ≃ (X ⟶ H.val) := r.adjunction.homEquiv X H
  let e₃ : (G.cylinder.obj X ⟶ Z) ≃ (X ⟶ H.val) := G.adjunction.homEquiv X Z
  apply e₃.injective
  change e₃ (e₃.symm (e₂ (e₁ P))) = e₃ (G.cylinder.map (r.adjunction.unit.app X) ≫ P)
  calc
    _ = e₂ (e₁ P) := e₃.apply_symm_apply _
    _ = r.adjunction.unit.app X ≫ e₁ P := r.adjunction.homEquiv_apply X H (e₁ P)
    _ = _ := (G.adjunction.homEquiv_naturality_left (r.adjunction.unit.app X) P).symm

include t in
/-- Every cylinder into a finite-dimensional target descends uniquely through
finite reflection in its first factor. -/
theorem factor_cylinder (X : StrictOmegaCategory.{0})
    (Y : StrictOmegaCategory.Truncated.{0} (n + 1)) (P : G.cylinder.obj X ⟶ Y.val) :
    ∃! Q : G.cylinder.obj (r.reflect.obj X).val ⟶ Y.val,
      G.cylinder.map (r.adjunction.unit.app X) ≫ Q = P := by
  let e := G.cylinderRestrictionEquiv t r X Y
  refine ⟨e.symm P, ?_, ?_⟩
  · exact (G.cylinderRestrictionEquiv_apply t r X Y (e.symm P)).symm.trans
      (e.apply_symm_apply P)
  · intro Q hQ
    apply e.injective
    exact ((G.cylinderRestrictionEquiv_apply t r X Y Q).trans hQ).trans
      (e.apply_symm_apply P).symm

/-- Descent identifies both strict endpoints after reflection restriction. -/
theorem factor_cylinder_endpoint (X : StrictOmegaCategory.{0})
    (Y : StrictOmegaCategory.Truncated.{0} (n + 1))
    (P : G.cylinder.obj X ⟶ Y.val) (Q : G.cylinder.obj (r.reflect.obj X).val ⟶ Y.val)
    (hQ : G.cylinder.map (r.adjunction.unit.app X) ≫ Q = P) (a : Bool) :
    r.adjunction.unit.app X ≫ ((G.endpoint a).app (r.reflect.obj X).val ≫ Q) =
      (G.endpoint a).app X ≫ P := by
  let q : X ⟶ (r.reflect.obj X).val := r.adjunction.unit.app X
  have hn : q ≫ (G.endpoint a).app (r.reflect.obj X).val =
      (G.endpoint a).app X ≫ G.cylinder.map q := (G.endpoint a).naturality q
  calc
    _ = (q ≫ (G.endpoint a).app (r.reflect.obj X).val) ≫ Q := (Category.assoc _ _ _).symm
    _ = ((G.endpoint a).app X ≫ G.cylinder.map q) ≫ Q := congrArg (fun k => k ≫ Q) hn
    _ = (G.endpoint a).app X ≫ P := (Category.assoc _ _ _).trans
      (congrArg (fun k => (G.endpoint a).app X ≫ k) hQ)

end RightGrayInput
end Thomason.Construction

end

section

/-!
# Finite reflection leaves object sets unchanged

The proof uses Boolean labels into a codiscrete one-dimensional category.
The existing reflection adjunction makes precomposition with the unit a
bijection on those labels, which detects bijectivity of its object map.

-/

namespace Thomason.Construction.FiniteReflectionInput

open CategoryTheory StrictOmegaCategory

variable {n : ℕ} (r : FiniteReflectionInput n)

/-- The codiscrete target used to test object sets is already a finite category. -/
def finiteCodiscrete (E : Type) : Truncated (n + 1) :=
  ⟨codiscrete E, fun x => (codiscrete E).dimensionLE_mono (by omega)
    (StrictPoset.category_isTruncated (Indiscrete E) x)⟩

/-- The explicit object/codiscrete bijection, without bundling functions as arrows. -/
def objectLabelsEquiv (C : StrictOmegaCategory.{0}) (E : Type) :
    (Objects C → E) ≃ (C ⟶ codiscrete E) where
  toFun := codiscreteLift
  invFun := codiscreteLabel
  left_inv := codiscreteLabel_lift
  right_inv := codiscreteLift_label

/-- The unit induces a bijection on Boolean object labels. -/
noncomputable def unitLabelsEquiv (X : StrictOmegaCategory.{0}) :
    (Objects (r.reflect.obj X).val → Bool) ≃ (Objects X → Bool) :=
  (objectLabelsEquiv (r.reflect.obj X).val Bool).trans
    ((r.adjunction.homEquiv X (finiteCodiscrete Bool)).trans
      (objectLabelsEquiv X Bool).symm)

/-- This bijection is actual precomposition with the object map of the unit. -/
theorem unitLabelsEquiv_apply (X : StrictOmegaCategory.{0})
    (f : Objects (r.reflect.obj X).val → Bool) :
    r.unitLabelsEquiv X f = f ∘ (r.adjunction.unit.app X).toOneFunctor.obj := by
  change codiscreteLabel ((r.adjunction.homEquiv X (finiteCodiscrete Bool))
    (codiscreteLift f)) = _
  let Y : Truncated (n + 1) := finiteCodiscrete Bool
  let k : r.reflect.obj X ⟶ Y := codiscreteLift f
  have he := r.adjunction.homEquiv_apply X Y k
  have hl := congrArg (fun g : X ⟶ Y.val => codiscreteLabel g) he
  refine hl.trans ?_
  funext x
  change f ((r.reflect.obj X).val.boundaryObject false
    ((r.adjunction.unit.app X).toFun x.val)) = f ((r.adjunction.unit.app X).toOneFunctor.obj x)
  exact congrArg f ((r.reflect.obj X).val.boundaryObject_of_object false
    ((r.adjunction.unit.app X).toOneFunctor.obj x))

/-- Intelligent truncation preserves and reflects every object, as a consequence
of its adjunction alone. -/
theorem unit_objects_bijective (X : StrictOmegaCategory.{0}) :
    Function.Bijective (r.adjunction.unit.app X).toOneFunctor.obj := by
  have he : (fun f : Objects (r.reflect.obj X).val → Bool =>
      f ∘ (r.adjunction.unit.app X).toOneFunctor.obj) = r.unitLabelsEquiv X := by
    funext f
    exact (r.unitLabelsEquiv_apply X f).symm
  have hb : Function.Bijective (fun f : Objects (r.reflect.obj X).val → Bool =>
      f ∘ (r.adjunction.unit.app X).toOneFunctor.obj) := by
    rw [he]
    exact (r.unitLabelsEquiv X).bijective
  exact ⟨Function.surjective_comp_right_iff_injective.mp hb.2,
    Function.injective_comp_right_iff_surjective.mp hb.1⟩

/-- The resulting canonical equivalence of object sets. -/
noncomputable def unitObjectsEquiv (X : StrictOmegaCategory.{0}) :
    Objects X ≃ Objects (r.reflect.obj X).val :=
  Equiv.ofBijective (r.adjunction.unit.app X).toOneFunctor.obj (r.unit_objects_bijective X)

/-- The object equivalence commutes with every strict functor. -/
theorem unitObjectsEquiv_naturality {X Y : StrictOmegaCategory.{0}} (f : X ⟶ Y)
    (x : Objects X) :
    r.unitObjectsEquiv Y (f.toOneFunctor.obj x) =
      (r.reflect.map f).toOneFunctor.obj (r.unitObjectsEquiv X x) := by
  have he := r.adjunction.unit.naturality f
  exact congrArg (fun g : X ⟶ (r.reflect.obj Y).val => g.toOneFunctor.obj x) he

variable (h : NormalizedSimplexIdentities) [StrictColimitsInput]

/-- The objects of finite-dimensional categorification are the original vertices. -/
noncomputable def categorificationObjectsEquiv (K : SSet.{0}) :
    Objects ((r.categorification h).obj K).val ≃ K.obj (.op (.mk 0)) :=
  (r.unitObjectsEquiv (h.categorification.obj K)).symm.trans (h.categorificationObjectsEquiv K)

/-- The finite-dimensional vertex identification is natural. -/
theorem categorificationObjectsEquiv_naturality {K L : SSet.{0}} (f : K ⟶ L)
    (x : Objects ((r.categorification h).obj K).val) :
    r.categorificationObjectsEquiv h L (((r.categorification h).map f).toOneFunctor.obj x) =
      f.app _ (r.categorificationObjectsEquiv h K x) := by
  obtain ⟨x, rfl⟩ := r.unit_objects_bijective (h.categorification.obj K) |>.2 x
  have he := r.unitObjectsEquiv_naturality (h.categorification.map f) x
  change (h.categorificationObjectsEquiv L)
      ((r.unitObjectsEquiv (h.categorification.obj L)).symm
        ((r.reflect.map (h.categorification.map f)).toOneFunctor.obj
          (r.unitObjectsEquiv (h.categorification.obj K) x))) = _
  rw [← he, Equiv.symm_apply_apply]
  exact (h.categorificationObjectsEquiv_naturality f x).trans
    (congrArg (fun y => f.app _ ((h.categorificationObjectsEquiv K) y))
      ((r.unitObjectsEquiv (h.categorification.obj K)).symm_apply_apply x).symm)

end Thomason.Construction.FiniteReflectionInput

end

section

/-!
# Full convex pieces of orientals

Endpoint control reduces the full-segment proof to atom generation. Convexity is used to retain the middle
object of a zero-composition; positive compositions retain both endpoints.
-/

namespace Thomason.Construction.SimplexComplex

open CategoryTheory StrictOmegaCategory

/-- The vertex index of either object boundary of an oriental cell. -/
noncomputable def objectIndex (h : NormalizedSimplexIdentities) {m : ℕ}
    (a : Bool) (x : h.object m) : Fin (m + 1) :=
  objectsEquiv h m ((h.object m).boundaryObject a x)

@[simp]
theorem objectIndex_face_zero (h : NormalizedSimplexIdentities) {m : ℕ}
    (a b : Bool) (x : h.object m) :
    objectIndex h a ((h.object m).face b 0 x) = objectIndex h b x := by
  apply congrArg (objectsEquiv h m)
  apply Subtype.ext
  exact (h.object m).face_face_same a b 0 x

@[simp]
theorem objectIndex_face_succ (h : NormalizedSimplexIdentities) {m : ℕ}
    (a b : Bool) (n : ℕ) (x : h.object m) :
    objectIndex h a ((h.object m).face b (n + 1) x) = objectIndex h a x := by
  apply congrArg (objectsEquiv h m)
  apply Subtype.ext
  exact ((h.object m).globular a b 0 (n + 1) x).trans (ite_eq_left (Nat.zero_lt_succ n))

@[simp]
theorem objectIndex_comp_zero (h : NormalizedSimplexIdentities) {m : ℕ}
    (a : Bool) (x y : h.object m) (hxy : (h.object m).target 0 x = (h.object m).source 0 y) :
    objectIndex h a ((h.object m).comp 0 x y hxy) =
      if a then objectIndex h a y else objectIndex h a x := by
  cases a
  · apply congrArg (objectsEquiv h m)
    exact Subtype.ext ((h.object m).source_comp 0 x y hxy)
  · apply congrArg (objectsEquiv h m)
    exact Subtype.ext ((h.object m).target_comp 0 x y hxy)

@[simp]
theorem objectIndex_comp_succ (h : NormalizedSimplexIdentities) {m : ℕ}
    (a : Bool) (n : ℕ) (x y : h.object m)
    (hxy : (h.object m).target (n + 1) x = (h.object m).source (n + 1) y) :
    objectIndex h a ((h.object m).comp (n + 1) x y hxy) = objectIndex h a x := by
  apply congrArg (objectsEquiv h m)
  exact Subtype.ext ((h.object m).zero_face_comp_succ a n x y hxy)

/-- An actual cell whose two object boundaries are in the selected vertices. -/
def FullOnVertices (h : NormalizedSimplexIdentities) {m : ℕ}
    (I : Set (Fin (m + 1))) (x : h.object m) : Prop :=
  objectIndex h false x ∈ I ∧ objectIndex h true x ∈ I

/-- Both factors of a cell supported on a convex vertex set remain supported
on that set. This is the key step in induction on a composition expression. -/
theorem fullOnVertices_comp_factors (h : NormalizedSimplexIdentities) {m : ℕ}
    {I : Set (Fin (m + 1))} (hI : Set.OrdConnected I)
    (n : ℕ) (x y : h.object m) (hxy : (h.object m).target n x = (h.object m).source n y)
    (hc : FullOnVertices h I ((h.object m).comp n x y hxy)) :
    FullOnVertices h I x ∧ FullOnVertices h I y := by
  change objectIndex h false ((h.object m).comp n x y hxy) ∈ I ∧
    objectIndex h true ((h.object m).comp n x y hxy) ∈ I at hc
  cases n with
  | zero =>
    simp only [objectIndex_comp_zero, Bool.false_eq_true, ite_false, ite_true] at hc
    have hm : objectIndex h true x = objectIndex h false y :=
      (objectIndex_face_zero h false true x).symm.trans
        ((congrArg (objectIndex h false) hxy).trans (objectIndex_face_zero h false false y))
    have hx : objectIndex h false x ≤ objectIndex h true x := endpoints_ordered h x
    have hy : objectIndex h true x ≤ objectIndex h true y := by
      rw [hm]
      exact endpoints_ordered h y
    have hmI := hI.out hc.1 hc.2 ⟨hx, hy⟩
    exact ⟨⟨hc.1, hmI⟩, ⟨hm ▸ hmI, hc.2⟩⟩
  | succ n =>
    simp only [objectIndex_comp_succ] at hc
    have he (a : Bool) : objectIndex h a x = objectIndex h a y :=
      (objectIndex_face_succ h a true n x).symm.trans
        ((congrArg (objectIndex h a) hxy).trans (objectIndex_face_succ h a false n y))
    exact ⟨hc, ⟨he false ▸ hc.1, he true ▸ hc.2⟩⟩

/-- The source index of a simplex atom is its first tuple entry. -/
theorem objectIndex_atom_source {h : NormalizedSimplexIdentities} (a : SimplexAtomsInput h)
    {m p : ℕ} (b : Basis m p) : objectIndex h false (a.atom b) = b 0 := by
  have he : (h.object m).boundaryObject false (a.atom b) = (objectsEquiv h m).symm (b 0) :=
    Subtype.ext (a.atom_source b)
  exact (congrArg (objectsEquiv h m) he).trans ((objectsEquiv h m).apply_symm_apply _)

/-- The target index of a simplex atom is its last tuple entry. -/
theorem objectIndex_atom_target {h : NormalizedSimplexIdentities} (a : SimplexAtomsInput h)
    {m p : ℕ} (b : Basis m p) : objectIndex h true (a.atom b) = b (Fin.last p) := by
  have he : (h.object m).boundaryObject true (a.atom b) =
      (objectsEquiv h m).symm (b (Fin.last p)) := Subtype.ext (a.atom_target b)
  exact (congrArg (objectsEquiv h m) he).trans ((objectsEquiv h m).apply_symm_apply _)

/-- A split ordinal embedding gives an injective map on all oriental cells. -/
theorem map_injective_of_retraction (h : NormalizedSimplexIdentities) {q m : ℕ}
    (e : Fin (q + 1) →o Fin (m + 1)) (r : Fin (m + 1) →o Fin (q + 1))
    (hre : r.comp e = OrderHom.id) : Function.Injective (h.map e).toFun := by
  have he : h.map e ≫ h.map r = 𝟙 (h.object q) :=
    (h.map_comp e r).symm.trans ((congrArg (fun f => h.map f) hre).trans (h.map_id q))
  have hl (x : h.object q) : (h.map r).toFun ((h.map e).toFun x) = x :=
    congrArg (fun f : h.object q ⟶ h.object q => f.toFun x) he
  intro x y hxy
  exact (hl x).symm.trans ((congrArg (h.map r).toFun hxy).trans (hl y))

/-- The cell image of an injective strict functor is closed under composition. -/
theorem hom_range_comp {C D : StrictOmegaCategory.{0}} (f : C ⟶ D)
    (hf : Function.Injective f.toFun) (n : ℕ) {x y : D}
    (hxy : D.target n x = D.source n y)
    (hx : x ∈ Set.range f.toFun) (hy : y ∈ Set.range f.toFun) :
    D.comp n x y hxy ∈ Set.range f.toFun := by
  obtain ⟨x', rfl⟩ := hx
  obtain ⟨y', rfl⟩ := hy
  have he : C.target n x' = C.source n y' :=
    hf ((f.map_face true n x').trans (hxy.trans (f.map_face false n y').symm))
  exact ⟨C.comp n x' y' he, f.map_comp n x' y' he hxy⟩

/-- A tuple whose entries lie in an ordinal face factors monotonically through it. -/
noncomputable def factorThroughFace {q m p : ℕ} (e : Fin (q + 1) ↪o Fin (m + 1))
    (b : Basis m p) (hb : ∀ i, b i ∈ Set.range e) : Fin (p + 1) →o Fin (q + 1) where
  toFun i := (hb i).choose
  monotone' := by
    intro i j hij
    apply e.le_iff_le.mp
    rw [(hb i).choose_spec, (hb j).choose_spec]
    exact b.monotone hij

@[simp]
theorem factorThroughFace_fac {q m p : ℕ} (e : Fin (q + 1) ↪o Fin (m + 1))
    (b : Basis m p) (hb : ∀ i, b i ∈ Set.range e) :
    e.toOrderHom.comp (factorThroughFace e b hb) = b.toOrderHom := by
  apply DFunLike.ext
  intro i
  exact (hb i).choose_spec

/-- Atom generation implies the full-cell assertion for
any convex ordinal face with a monotone retraction. This is the needed
initial/final-segment statement at the level of actual cells. -/
theorem full_convex_face {h : NormalizedSimplexIdentities} (a : SimplexAtomsInput h)
    {q m : ℕ} (e : Fin (q + 1) ↪o Fin (m + 1))
    (r : Fin (m + 1) →o Fin (q + 1)) (hre : r.comp e.toOrderHom = OrderHom.id)
    (he : Set.OrdConnected (Set.range e)) :
    ∀ x : h.object m, FullOnVertices h (Set.range e) x →
      x ∈ Set.range (h.map e.toOrderHom).toFun := by
  apply a.generated m
  · intro p b hb
    change FullOnVertices h (Set.range e) (a.atom b) at hb
    change objectIndex h false (a.atom b) ∈ Set.range e ∧
      objectIndex h true (a.atom b) ∈ Set.range e at hb
    rw [objectIndex_atom_source, objectIndex_atom_target] at hb
    have hb' : ∀ i, b i ∈ Set.range e := fun i =>
      he.out hb.1 hb.2 ⟨b.monotone (Fin.zero_le i), b.monotone (Fin.le_last i)⟩
    refine ⟨(h.map (factorThroughFace e b hb')).toFun (a.principal p), ?_⟩
    have hf := h.map_comp (factorThroughFace e b hb') e.toOrderHom
    rw [factorThroughFace_fac] at hf
    exact (congrArg (fun f : h.object p ⟶ h.object m => f.toFun (a.principal p)) hf).symm
  · intro n x y hxy hx hy hc
    obtain ⟨hcx, hcy⟩ := fullOnVertices_comp_factors h he n x y hxy hc
    exact hom_range_comp (h.map e.toOrderHom) (map_injective_of_retraction h _ r hre)
      n hxy (hx hcx) (hy hcy)

/-- The endpoint index is natural for all monotone ordinal maps. -/
theorem objectIndex_map (h : NormalizedSimplexIdentities) {q m : ℕ}
    (f : Fin (q + 1) →o Fin (m + 1)) (a : Bool) (x : h.object q) :
    objectIndex h a ((h.map f).toFun x) = f (objectIndex h a x) := by
  have he : (h.object m).boundaryObject a ((h.map f).toFun x) =
      (h.map f).toOneFunctor.obj ((h.object q).boundaryObject a x) :=
    Subtype.ext ((h.map f).map_face a 0 x).symm
  exact (congrArg (objectsEquiv h m) he).trans
    (objectsEquiv_map h f ((h.object q).boundaryObject a x))

end Thomason.Construction.SimplexComplex

end

section

/-!
# Actual full subcategories of orientals on convex faces

This packages the cell-image theorem as a strict isomorphism commuting
with the original face inclusion. The selected sets are tested only on
zero-boundaries, as in the definition of a full strict subcategory.
-/

namespace Thomason.Construction.SimplexComplex

open CategoryTheory StrictOmegaCategory

/-- The full strict subcategory on the specified oriental vertices. -/
noncomputable def vertexFullSubcategory (h : NormalizedSimplexIdentities) {m : ℕ}
    (I : Set (Fin (m + 1))) : StrictOmegaCategory.{0} :=
  (h.object m).fullOn {x | objectIndex h false x ∈ I}

/-- Its all-cell membership is precisely membership of both object endpoints. -/
theorem fullCell_vertices_iff (h : NormalizedSimplexIdentities) {m : ℕ}
    (I : Set (Fin (m + 1))) (x : h.object m) :
    (h.object m).FullCell {x | objectIndex h false x ∈ I} x ↔ FullOnVertices h I x := by
  change (objectIndex h false ((h.object m).face false 0 x) ∈ I ∧
    objectIndex h false ((h.object m).face true 0 x) ∈ I) ↔ _
  simp only [objectIndex_face_zero, FullOnVertices]

/-- Any ordinal face lands in the actual full subcategory on its image vertices. -/
noncomputable def fullFaceMap (h : NormalizedSimplexIdentities) {q m : ℕ}
    (e : Fin (q + 1) ↪o Fin (m + 1)) :
    h.object q ⟶ vertexFullSubcategory h (Set.range e) where
  toFun x := ⟨(h.map e.toOrderHom).toFun x, (fullCell_vertices_iff h _ _).mpr
    ⟨⟨objectIndex h false x, (objectIndex_map h e.toOrderHom false x).symm⟩,
      ⟨objectIndex h true x, (objectIndex_map h e.toOrderHom true x).symm⟩⟩⟩
  map_face a n x := Subtype.ext ((h.map e.toOrderHom).map_face a n x)
  map_comp n x y hxy h' := Subtype.ext ((h.map e.toOrderHom).map_comp n x y hxy
    (congrArg Subtype.val h'))

/-- The smaller oriental is the full strict subcategory on a convex split face. -/
noncomputable def fullFaceIso {h : NormalizedSimplexIdentities} (a : SimplexAtomsInput h)
    {q m : ℕ} (e : Fin (q + 1) ↪o Fin (m + 1))
    (r : Fin (m + 1) →o Fin (q + 1)) (hre : r.comp e.toOrderHom = OrderHom.id)
    (he : Set.OrdConnected (Set.range e)) :
    h.object q ≅ vertexFullSubcategory h (Set.range e) :=
  StrictOmegaCategory.isoOfBijective (fullFaceMap h e)
    ⟨fun _ _ hxy => map_injective_of_retraction h e.toOrderHom r hre
      (congrArg Subtype.val hxy),
      fun y => by
        obtain ⟨x, hx⟩ := full_convex_face a e r hre he y.val
          ((fullCell_vertices_iff h _ _).mp y.property)
        exact ⟨x, Subtype.ext hx⟩⟩

/-- The isomorphism realizes the given ordinal face, not merely an abstract copy. -/
theorem fullFaceIso_hom_inclusion {h : NormalizedSimplexIdentities} (a : SimplexAtomsInput h)
    {q m : ℕ} (e : Fin (q + 1) ↪o Fin (m + 1))
    (r : Fin (m + 1) →o Fin (q + 1)) (hre : r.comp e.toOrderHom = OrderHom.id)
    (he : Set.OrdConnected (Set.range e)) :
    (fullFaceIso a e r hre he).hom ≫
      (h.object m).fullInclusion {x | objectIndex h false x ∈ Set.range e} = h.map e.toOrderHom := by
  apply StrictOmegaCategory.Hom.ext
  rfl

end Thomason.Construction.SimplexComplex

end

section

/-!
# Canonical ordered labels of categorified poset nerves

These maps are constructed on all oriental pieces and then descended
through the actual simplex colimit. Their effect on objects is the
canonical vertex identification.
-/

namespace Thomason.Construction.NormalizedSimplexIdentities

open CategoryTheory CategoryTheory.Limits Opposite StrictOmegaCategory

variable (h : NormalizedSimplexIdentities) [StrictColimitsInput]

/-- The ordered label on one oriental in the nerve of a poset. -/
noncomputable def simplexPosetLabel {E : Type} [PartialOrder E] {m : SimplexCategory}
    (s : SSet.stdSimplex.obj m ⟶ nerve E) : h.object m.len ⟶ StrictPoset.category E :=
  h.ordinalLabel m.len ≫ StrictPoset.map (simplexOrder (SSet.yonedaEquiv s))

omit [StrictColimitsInput] in
/-- Every simplex operator respects the ordered labels. -/
theorem simplexPosetLabel_precomp {E : Type} [PartialOrder E] {m n : SimplexCategory}
    (s : SSet.stdSimplex.obj n ⟶ nerve E) (a : m ⟶ n) :
    h.cosimplicial.map a ≫ h.simplexPosetLabel s =
      h.simplexPosetLabel (SSet.stdSimplex.map a ≫ s) := by
  change h.map a.toOrderHom ≫
    (h.ordinalLabel n.len ≫ StrictPoset.map (simplexOrder (SSet.yonedaEquiv s))) = _
  rw [← Category.assoc, h.ordinalLabel_naturality, Category.assoc]
  change _ = h.ordinalLabel m.len ≫
    StrictPoset.map (simplexOrder (SSet.yonedaEquiv (SSet.stdSimplex.map a ≫ s)))
  rw [simplexOrder_precomp]
  apply StrictOmegaCategory.Hom.ext
  funext x
  rfl

/-- The compatible ordered labels form a cocone on the oriental presentation. -/
noncomputable def posetLabelCocone (E : Type) [PartialOrder E] :
    Cocone (CostructuredArrow.proj SSet.stdSimplex (nerve E) ⋙ h.cosimplicial) where
  pt := StrictPoset.category E
  ι :=
    { app := fun s => h.simplexPosetLabel s.hom
      naturality := by
        intro s t a
        change h.cosimplicial.map a.left ≫ h.simplexPosetLabel t.hom = h.simplexPosetLabel s.hom
        exact (h.simplexPosetLabel_precomp t.hom a.left).trans
          (congrArg h.simplexPosetLabel (CostructuredArrow.w a)) }

/-- Evaluation of categorified poset cells in their underlying ordered labels. -/
noncomputable def posetEvaluation (E : Type) [PartialOrder E] :
    h.categorification.obj (nerve E) ⟶ StrictPoset.category E :=
  (h.simplexCocone_isColimit (nerve E)).desc (h.posetLabelCocone E)

/-- Evaluation on each actual colimit leg is the constructed ordered label. -/
theorem posetEvaluation_fac {E : Type} [PartialOrder E] {m : SimplexCategory}
    (s : SSet.stdSimplex.obj m ⟶ nerve E) :
    h.simplexLeg s ≫ h.posetEvaluation E = h.simplexPosetLabel s :=
  (h.simplexCocone_isColimit (nerve E)).fac (h.posetLabelCocone E) (CostructuredArrow.mk s)

/-- In degree zero the ordinary nerve of a poset is its set of elements. -/
def posetNerveZeroEquiv (E : Type) [PartialOrder E] :
    (nerve E).obj (op (.mk 0)) ≃ E where
  toFun s := s.obj 0
  invFun e := orderSimplex (OrderHom.const _ e)
  left_inv s := by
    apply nerve.ext_of_isThin
    funext i
    change Fin 1 at i
    have hi : i = 0 := by omega
    subst i
    rfl
  right_inv _ := rfl

/-- The object set of the actual categorified poset nerve is the original poset. -/
noncomputable def posetObjectsEquiv (E : Type) [PartialOrder E] :
    Objects (h.categorification.obj (nerve E)) ≃ E :=
  (h.categorificationObjectsEquiv (nerve E)).trans (posetNerveZeroEquiv E)

/-- The ordered evaluation agrees with this object identification. -/
theorem posetEvaluation_object {E : Type} [PartialOrder E]
    (x : Objects (h.categorification.obj (nerve E))) :
    (h.posetEvaluation E).toFun x.val = StrictPoset.identity (h.posetObjectsEquiv E x) := by
  obtain ⟨v, rfl⟩ := h.vertexObject_surjective (nerve E) x
  have he := congrArg (fun f : h.object 0 ⟶ StrictPoset.category E =>
    f.toFun (SimplexComplex.vertex h 0))
    (h.posetEvaluation_fac (SSet.yonedaEquiv.symm v))
  change (h.posetEvaluation E).toFun (h.vertexObject (nerve E) v).val = _ at he
  refine he.trans ?_
  change (StrictPoset.map (simplexOrder (SSet.yonedaEquiv (SSet.yonedaEquiv.symm v)))).toFun
    ((h.ordinalLabel 0).toFun (SimplexComplex.vertex h 0)) = _
  rw [ordinalLabel_vertex, Equiv.apply_symm_apply, StrictPoset.map_identity]
  change StrictPoset.identity (v.obj 0) = StrictPoset.identity
    ((posetNerveZeroEquiv E) (h.readVertex (nerve E) (h.vertexObject (nerve E) v)))
  rw [readVertex_vertexObject]
  rfl

/-- The poset object identification is natural for monotone maps. -/
theorem posetObjectsEquiv_naturality {E F : Type} [PartialOrder E] [PartialOrder F]
    (f : E →o F) (x : Objects (h.categorification.obj (nerve E))) :
    h.posetObjectsEquiv F ((h.posetMap f).toOneFunctor.obj x) =
      f (h.posetObjectsEquiv E x) := by
  have he := h.categorificationObjectsEquiv_naturality (nerveMap f.monotone.functor) x
  exact congrArg (fun v : (nerve F).obj (op (.mk 0)) => v.obj 0) he

/-- Strict evaluation of ordered labels is natural, on all cells. -/
theorem posetEvaluation_naturality {E F : Type} [PartialOrder E] [PartialOrder F]
    (f : E →o F) :
    h.posetMap f ≫ h.posetEvaluation F = h.posetEvaluation E ≫ StrictPoset.map f := by
  apply StrictOmegaCategory.hom_poset_ext
  intro x
  change (h.posetEvaluation F).toFun ((h.posetMap f).toFun x.val) =
    (StrictPoset.map f).toFun ((h.posetEvaluation E).toFun x.val)
  have he := h.posetEvaluation_object ((h.posetMap f).toOneFunctor.obj x)
  rw [h.posetObjectsEquiv_naturality f x] at he
  exact he.trans ((StrictPoset.map_identity f _).symm.trans
    (congrArg (StrictPoset.map f).toFun (h.posetEvaluation_object x).symm))

end Thomason.Construction.NormalizedSimplexIdentities

end

section

/-!
# Membership labels for sieves of categorified posets

The label is a strict functor to the walking arrow, constructed from the
actual oriental presentation. Its full zero-fiber has exactly the expected
object boundaries. Identifying this fiber with the categorification of the
sieve still requires the full-segment theorem.
-/

namespace Thomason.Construction

open CategoryTheory StrictOmegaCategory

/-- The monotone zero/one characteristic map of a downward-closed subset. -/
noncomputable def sieveCharacteristic {E : Type} [PartialOrder E]
    (A : Set E) (hA : IsLowerSet A) : E →o Fin 2 := by
  classical
  exact
    { toFun := fun e => if e ∈ A then 0 else 1
      monotone' := by
        intro a b hab
        by_cases ha : a ∈ A <;> by_cases hb : b ∈ A <;>
          simp only [ha, hb, ite_true, ite_false]
        all_goals first | decide | exact (ha (hA hab hb)).elim }

@[simp]
theorem sieveCharacteristic_zero_iff {E : Type} [PartialOrder E]
    (A : Set E) (hA : IsLowerSet A) (e : E) : sieveCharacteristic A hA e = 0 ↔ e ∈ A := by
  classical
  change (if e ∈ A then (0 : Fin 2) else 1) = 0 ↔ e ∈ A
  split_ifs <;> simp_all

namespace NormalizedSimplexIdentities

variable (h : NormalizedSimplexIdentities) [StrictColimitsInput]

/-- The actual strict walking-arrow label associated to a poset sieve. -/
noncomputable def membershipLabel {E : Type} [PartialOrder E] (A : Set E) (hA : IsLowerSet A) :
    h.categorification.obj (nerve E) ⟶ StrictPoset.category (Fin 2) :=
  h.posetEvaluation E ≫ StrictPoset.map (sieveCharacteristic A hA)

/-- Membership labelling on objects is the original poset characteristic map. -/
theorem membershipLabel_object {E : Type} [PartialOrder E] (A : Set E) (hA : IsLowerSet A)
    (x : Objects (h.categorification.obj (nerve E))) :
    (h.membershipLabel A hA).toFun x.val =
      StrictPoset.identity (sieveCharacteristic A hA (h.posetObjectsEquiv E x)) := by
  change (StrictPoset.map (sieveCharacteristic A hA)).toFun
    ((h.posetEvaluation E).toFun x.val) = _
  rw [h.posetEvaluation_object x, StrictPoset.map_identity]

/-- An object lies over zero precisely when its original vertex is in the sieve. -/
theorem membershipLabel_object_zero_iff {E : Type} [PartialOrder E]
    (A : Set E) (hA : IsLowerSet A) (x : Objects (h.categorification.obj (nerve E))) :
    (h.membershipLabel A hA).toFun x.val = StrictPoset.identity 0 ↔
      h.posetObjectsEquiv E x ∈ A := by
  rw [h.membershipLabel_object A hA x]
  constructor
  · intro he
    exact (sieveCharacteristic_zero_iff A hA _).mp
      (congrArg (fun z : StrictPoset.Cell (Fin 2) => z.first) he)
  · intro hx
    exact congrArg StrictPoset.identity ((sieveCharacteristic_zero_iff A hA _).mpr hx)

/-- The zero-fiber includes precisely all cells between sieve-labelled objects. -/
theorem membershipLabel_zero_iff {E : Type} [PartialOrder E]
    (A : Set E) (hA : IsLowerSet A) (x : h.categorification.obj (nerve E)) :
    (h.membershipLabel A hA).toFun x = StrictPoset.identity 0 ↔
      h.posetObjectsEquiv E ((h.categorification.obj (nerve E)).boundaryObject false x) ∈ A ∧
      h.posetObjectsEquiv E ((h.categorification.obj (nerve E)).boundaryObject true x) ∈ A := by
  exact (fullCell_label_iff (h.membershipLabel A hA) 0 x).symm.trans
    (and_congr
      (h.membershipLabel_object_zero_iff A hA
        ((h.categorification.obj (nerve E)).boundaryObject false x))
      (h.membershipLabel_object_zero_iff A hA
        ((h.categorification.obj (nerve E)).boundaryObject true x)))

end NormalizedSimplexIdentities
end Thomason.Construction

end

section

/-! # Street nerve covers detected by endpoint labels

Two full sieves, or two full cosieves, that cover the objects also cover
every simplex of the actual Street nerve. The proof applies directly to
arbitrary strict categories, hence also to the underlying categories of
every positive finite dimension.
-/

namespace Thomason.Construction.NormalizedSimplexIdentities

open CategoryTheory CategoryTheory.Limits Opposite StrictOmegaCategory

variable (h : NormalizedSimplexIdentities) {C : StrictOmegaCategory.{0}}

/-- The actual full-fibre Street subcomplex of a binary strict label. -/
def fiberStreetSubcomplex (p : C ⟶ StrictPoset.category (Fin 2)) (e : Fin 2) :
    (h.streetNerve.obj C).Subcomplex :=
  h.fullStreetSubcomplex C {x | p.toFun x = StrictPoset.identity e}

theorem mem_fiberStreetSubcomplex (p : C ⟶ StrictPoset.category (Fin 2)) (e : Fin 2)
    {m : SimplexCategory} (f : h.object m.len ⟶ C) :
    f ∈ (h.fiberStreetSubcomplex p e).obj (op m) ↔
      ∀ x, p.toFun (f.toFun x) = StrictPoset.identity e := by
  exact forall_congr' (fun x => fullCell_label_iff p e (f.toFun x))

/-- The last vertex detects membership in every full zero-fibre. -/
theorem mem_fiberStreetSubcomplex_zero_iff_last
    (p : C ⟶ StrictPoset.category (Fin 2)) {m : SimplexCategory}
    (f : h.object m.len ⟶ C) :
    f ∈ (h.fiberStreetSubcomplex p 0).obj (op m) ↔
      p.toFun (f.toFun (SimplexComplex.vertex h (Fin.last m.len))) = StrictPoset.identity 0 :=
  (h.mem_fiberStreetSubcomplex p 0 f).trans (h.label_zero_iff_last (f ≫ p))

/-- The first vertex detects membership in every full one-fibre. -/
theorem mem_fiberStreetSubcomplex_one_iff_first
    (p : C ⟶ StrictPoset.category (Fin 2)) {m : SimplexCategory}
    (f : h.object m.len ⟶ C) :
    f ∈ (h.fiberStreetSubcomplex p 1).obj (op m) ↔
      p.toFun (f.toFun (SimplexComplex.vertex h 0)) = StrictPoset.identity 1 :=
  (h.mem_fiberStreetSubcomplex p 1 f).trans (h.label_one_iff_first (f ≫ p))

/-- A cover of the objects by full sieves gives a cover of the actual Street nerve. -/
theorem sieve_street_cover
    (p q : C ⟶ StrictPoset.category (Fin 2))
    (hc : ∀ x : Objects C, p.toFun x.val = StrictPoset.identity 0 ∨
      q.toFun x.val = StrictPoset.identity 0) :
    h.fiberStreetSubcomplex p 0 ⊔ h.fiberStreetSubcomplex q 0 = ⊤ := by
  apply top_unique
  intro m f _
  let x : Objects C :=
    ⟨f.toFun (SimplexComplex.vertex h (Fin.last m.unop.len)),
      f.dimensionLE (SimplexComplex.vertex_dimensionLE h _)⟩
  exact (hc x).imp
    ((h.mem_fiberStreetSubcomplex_zero_iff_last p f).mpr)
    ((h.mem_fiberStreetSubcomplex_zero_iff_last q f).mpr)

/-- The dual assertion for full cosieves uses the initial vertex. -/
theorem cosieve_street_cover
    (p q : C ⟶ StrictPoset.category (Fin 2))
    (hc : ∀ x : Objects C, p.toFun x.val = StrictPoset.identity 1 ∨
      q.toFun x.val = StrictPoset.identity 1) :
    h.fiberStreetSubcomplex p 1 ⊔ h.fiberStreetSubcomplex q 1 = ⊤ := by
  apply top_unique
  intro m f _
  let x : Objects C :=
    ⟨f.toFun (SimplexComplex.vertex h 0),
      f.dimensionLE (SimplexComplex.vertex_dimensionLE h _)⟩
  exact (hc x).imp
    ((h.mem_fiberStreetSubcomplex_one_iff_first p f).mpr)
    ((h.mem_fiberStreetSubcomplex_one_iff_first q f).mpr)

/-- The resulting sieve-cover square is an ordinary simplicial pushout,
with the intersection formed on the original object labels. -/
theorem sieve_street_isPushout
    (p q : C ⟶ StrictPoset.category (Fin 2))
    (hc : ∀ x : Objects C, p.toFun x.val = StrictPoset.identity 0 ∨
      q.toFun x.val = StrictPoset.identity 0) :
    IsPushout
      (SSet.Subcomplex.homOfLE (show h.fullStreetSubcomplex C
        ({x | p.toFun x = StrictPoset.identity 0} ∩ {x | q.toFun x = StrictPoset.identity 0}) ≤
        h.fiberStreetSubcomplex p 0 from fun _ _ hf x => ⟨(hf x).1.1, (hf x).2.1⟩))
      (SSet.Subcomplex.homOfLE (show h.fullStreetSubcomplex C
        ({x | p.toFun x = StrictPoset.identity 0} ∩ {x | q.toFun x = StrictPoset.identity 0}) ≤
        h.fiberStreetSubcomplex q 0 from fun _ _ hf x => ⟨(hf x).1.2, (hf x).2.2⟩))
      (h.fiberStreetSubcomplex p 0).ι (h.fiberStreetSubcomplex q 0).ι :=
  h.fullStreetSubcomplex_isPushout C _ _ (h.sieve_street_cover p q hc)

end Thomason.Construction.NormalizedSimplexIdentities

end

section

/-! # The actual Street nerve of a strict poset is its ordinary nerve

The inverse uses the constructed ordinal labels of orientals.
-/

namespace Thomason.Construction.NormalizedSimplexIdentities

open CategoryTheory Opposite

noncomputable section

variable (h : NormalizedSimplexIdentities) (P : Type) [PartialOrder P]

def strictPosetSimplexEquiv (n : ℕ) :
    (h.object n ⟶ StrictPoset.category P) ≃ (nerve P).obj (.op (.mk n)) where
  toFun f := orderSimplex (h.vertexOrder f)
  invFun s := h.ordinalLabel n ≫ StrictPoset.map (simplexOrder s)
  left_inv f := (h.eq_ordinalLabel_vertexOrder f).symm
  right_inv s := by
    apply nerve.ext_of_isThin
    funext i
    change ((StrictPoset.map (simplexOrder s)).toFun
      ((h.ordinalLabel n).toFun (SimplexComplex.vertex h i))).first = s.obj i
    rw [h.ordinalLabel_vertex]
    rfl

def strictPosetNerveMap : h.streetNerve.obj (StrictPoset.category P) ⟶ nerve P where
  app n := ↾(h.strictPosetSimplexEquiv P n.unop.len)
  naturality n m a := by
    apply ConcreteCategory.hom_ext
    intro s
    apply nerve.ext_of_isThin
    funext i
    change (s.toFun ((h.map a.unop.toOrderHom).toFun (SimplexComplex.vertex h i))).first =
      (s.toFun (SimplexComplex.vertex h (a.unop.toOrderHom i))).first
    rw [SimplexComplex.map_vertex]

instance strictPosetNerveMap_isIso : IsIso (h.strictPosetNerveMap P) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro n
  apply (CategoryTheory.isIso_iff_bijective _).mpr
  exact (h.strictPosetSimplexEquiv P n.unop.len).bijective

/-- The canonical comparison is an isomorphism on the Street
    nerve, including every degenerate simplex and every ordinal map. -/
def strictPosetNerveIso : h.streetNerve.obj (StrictPoset.category P) ≅ nerve P :=
  asIso (h.strictPosetNerveMap P)

end

end Thomason.Construction.NormalizedSimplexIdentities

end

section

/-! # Functoriality of the strict terminal cone over the walking arrow -/

namespace Thomason.Construction.StrictOmegaCategory.TerminalCone

open CategoryTheory

variable {C D E : StrictOmegaCategory.{0}}

theorem map_boundaryObject (f : C ⟶ D) (a : Bool) (x : C) :
    f.toOneFunctor.obj (C.boundaryObject a x) = D.boundaryObject a (f.toFun x) :=
  Subtype.ext (f.map_face a 0 x)

def mapCell (f : C ⟶ D) : Cell C → Cell D
  | .old x => .old (f.toFun x)
  | .tip => .tip
  | .arrow x => .arrow (f.toOneFunctor.obj x)

def map (f : C ⟶ D) : category C ⟶ category D where
  toFun := mapCell f
  map_face a n x := by
    cases x with
    | old x => exact congrArg Cell.old (f.map_face a n x)
    | tip => rfl
    | arrow x => cases n <;> cases a <;> rfl
  map_comp n x y h h' := by
    have hh : face true n x = face false n y := h
    change mapCell f (comp n x y h) = comp n (mapCell f x) (mapCell f y) h'
    cases x <;> cases y <;> cases n <;>
      (simp [face] at hh <;> simp only [comp, mapCell])
    all_goals first
      | exact congrArg Cell.old (f.map_comp _ _ _ _ _)
      | exact congrArg Cell.arrow (map_boundaryObject f false _)

theorem map_id (C : StrictOmegaCategory.{0}) : map (𝟙 C) = 𝟙 (category C) := by
  apply Hom.ext
  funext x
  cases x <;> rfl

theorem map_comp (f : C ⟶ D) (g : D ⟶ E) : map (f ≫ g) = map f ≫ map g := by
  apply Hom.ext
  funext x
  cases x <;> rfl

theorem map_label (f : C ⟶ D) : map f ≫ label D = label C := by
  apply Hom.ext
  funext x
  cases x <;> rfl

/-- The cone construction as a functor to the actual slice over [1]. -/
def overFunctor : StrictOmegaCategory.{0} ⥤ Over (StrictPoset.category (Fin 2)) where
  obj C := Over.mk (label C)
  map f := Over.homMk (map f) (map_label f)
  map_id C := by
    ext : 1
    exact map_id C
  map_comp f g := by
    ext : 1
    exact map_comp f g

end Thomason.Construction.StrictOmegaCategory.TerminalCone

end

end OAI
