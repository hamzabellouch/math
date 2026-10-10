import OAI.CategoryTheory.Thomason.Strict.StrictIsomorphisms
import OAI.CategoryTheory.Thomason.Strict.UnderlyingCategory
import OAI.CategoryTheory.Thomason.Transfer.StrictPushoutGeneration
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.Types.Colimits
import Mathlib.CategoryTheory.Limits.Types.Pushouts
import Mathlib.Order.Fin.Basic

namespace OAI

section

/-!
# Objects of strict categories preserve colimits

The codiscrete strict category on a set is a right adjoint to the object
functor. The adjunction identifies the objects of simplex colimits.
-/

namespace Thomason.Construction.StrictOmegaCategory

open CategoryTheory CategoryTheory.Limits

universe u

/-- The actual zero-dimensional objects of a strict category. -/
def objectFunctor : StrictOmegaCategory.{u} ⥤ Type u := underlyingCategory ⋙ Cat.objects

/-- A type endowed with the indiscrete preorder, used only for endpoint labels. -/
def Indiscrete (E : Type u) := E

instance (E : Type u) : Preorder (Indiscrete E) where
  le _ _ := True
  le_refl _ := trivial
  le_trans _ _ _ _ _ := trivial

/-- There is a unique cell between each pair of labels, and only identities
above dimension one. -/
def codiscrete (E : Type u) : StrictOmegaCategory.{u} := StrictPoset.category (Indiscrete E)

/-- The object at either end of a cell. -/
def boundaryObject (C : StrictOmegaCategory.{u}) (a : Bool) (x : C) : Objects C :=
  ⟨C.face a 0 x, C.face_dimensionLE a 0 x⟩

@[simp]
theorem boundaryObject_of_object (C : StrictOmegaCategory.{u}) (a : Bool) (x : Objects C) :
    C.boundaryObject a x.val = x := by
  apply Subtype.ext
  cases a
  · exact x.property.1
  · exact x.property.2

/-- Any assignment of object labels extends to the codiscrete strict category. -/
def codiscreteLift {C : StrictOmegaCategory.{u}} {E : Type u} (f : Objects C → E) :
    C ⟶ codiscrete E where
  toFun x := ⟨f (C.boundaryObject false x), f (C.boundaryObject true x), trivial⟩
  map_face a n x := by
    cases n with
    | zero =>
      cases a <;> apply StrictPoset.Cell.ext
      all_goals
        change f _ = f _
        congr 1
        apply Subtype.ext
        exact C.face_face_same _ _ 0 x
    | succ n =>
      apply StrictPoset.Cell.ext
      all_goals
        change f _ = f _
        congr 1
        apply Subtype.ext
        exact (C.globular _ _ 0 (n + 1) x).trans (ite_eq_left (Nat.zero_lt_succ n))
  map_comp n x y hxy h' := by
    cases n with
    | zero =>
      apply StrictPoset.Cell.ext
      · change f _ = f _
        exact congrArg f (Subtype.ext (C.source_comp 0 x y hxy))
      · change f _ = f _
        exact congrArg f (Subtype.ext (C.target_comp 0 x y hxy))
    | succ n =>
      apply StrictPoset.Cell.ext
      all_goals
        change f _ = f _
        congr 1
        apply Subtype.ext
        exact C.zero_face_comp_succ _ n x y hxy

/-- Read the label of a zero-cell in a codiscrete target. -/
def codiscreteLabel {C : StrictOmegaCategory.{u}} {E : Type u} (f : C ⟶ codiscrete E) :
    Objects C → E := fun x => (f.toFun x.val).first

@[simp]
theorem codiscreteLabel_lift {C : StrictOmegaCategory.{u}} {E : Type u}
    (f : Objects C → E) : codiscreteLabel (codiscreteLift f) = f := by
  funext x
  exact congrArg f (C.boundaryObject_of_object false x)

/-- A functor into a codiscrete category is determined by its object labels. -/
@[simp]
theorem codiscreteLift_label {C : StrictOmegaCategory.{u}} {E : Type u}
    (f : C ⟶ codiscrete E) : codiscreteLift (codiscreteLabel f) = f := by
  apply Hom.ext
  funext x
  apply StrictPoset.Cell.ext
  · change (f.toFun (C.face false 0 x)).first = (f.toFun x).first
    have hf := congrArg (fun z : StrictPoset.Cell (Indiscrete E) => z.first) (f.map_face false 0 x)
    exact hf
  · change (f.toFun (C.face true 0 x)).first = (f.toFun x).last
    have hf := congrArg (fun z : StrictPoset.Cell (Indiscrete E) => z.first) (f.map_face true 0 x)
    exact hf

/-- Relabelling codiscrete categories is functorial. -/
def codiscreteFunctor : Type u ⥤ StrictOmegaCategory.{u} where
  obj := codiscrete
  map f := StrictPoset.map ⟨f, fun _ _ _ => trivial⟩
  map_id _ := by apply Hom.ext; rfl
  map_comp _ _ := by apply Hom.ext; rfl

/-- The object/codiscrete adjunction, proved from the explicit endpoint formula. -/
def objectAdjunction : objectFunctor.{u} ⊣ codiscreteFunctor.{u} :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun C E =>
        { toFun := fun f => codiscreteLift f
          invFun := fun f => ↾(codiscreteLabel f)
          left_inv := fun f => by
            apply ConcreteCategory.hom_ext
            exact congrFun (codiscreteLabel_lift f)
          right_inv := codiscreteLift_label }
      homEquiv_naturality_left_symm := by
        intro C D E f g
        rfl
      homEquiv_naturality_right := by
        intro C E F f g
        apply Hom.ext
        rfl }

/-- Object sets of arbitrary strict-category colimits are their set colimits. -/
instance objectFunctor_preservesColimits : PreservesColimitsOfSize.{u, u} objectFunctor.{u} :=
  objectAdjunction.leftAdjoint_preservesColimits

end Thomason.Construction.StrictOmegaCategory

end

section

/-! # Objects of positive finite strict categories preserve colimits

The codiscrete category is already one-dimensional, so the explicit
object/codiscrete adjunction restricts directly.
-/

namespace Thomason.Construction.StrictOmegaCategory

open CategoryTheory CategoryTheory.Limits

/-- The actual object functor on positive finite strict categories. -/
def finiteObjectFunctor (n : ℕ) : Truncated.{0} (n + 1) ⥤ Type :=
  inclusion (n + 1) ⋙ objectFunctor

/-- Codiscrete categories already satisfy every positive dimension bound. -/
def finiteCodiscreteFunctor (n : ℕ) : Type ⥤ Truncated.{0} (n + 1) where
  obj E := ⟨codiscrete E, fun x => (codiscrete E).dimensionLE_mono (by omega)
    (StrictPoset.category_isTruncated (Indiscrete E) x)⟩
  map f := codiscreteFunctor.map f
  map_id E := codiscreteFunctor.map_id E
  map_comp f g := codiscreteFunctor.map_comp f g

/-- The direct adjunction in the actual finite category. -/
def finiteObjectAdjunction (n : ℕ) : finiteObjectFunctor n ⊣ finiteCodiscreteFunctor n :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun C E =>
        { toFun := fun f => codiscreteLift f
          invFun := fun f => ↾(codiscreteLabel f)
          left_inv := fun f => by
            apply ConcreteCategory.hom_ext
            exact congrFun (codiscreteLabel_lift f)
          right_inv := codiscreteLift_label }
      homEquiv_naturality_left_symm := by
        intro C D E f g
        rfl
      homEquiv_naturality_right := by
        intro C E F f g
        apply Hom.ext
        rfl }

instance finiteObjectFunctor_preservesColimits (n : ℕ) :
    PreservesColimitsOfSize.{0, 0} (finiteObjectFunctor n) :=
  (finiteObjectAdjunction n).leftAdjoint_preservesColimits

/-- Every object of a finite-dimensional pushout comes from a summand. -/
theorem finite_pushout_objects_covered {n : ℕ} {A B X Y : Truncated.{0} (n + 1)}
    {i : A ⟶ B} {a : A ⟶ X} {b : B ⟶ Y} {j : X ⟶ Y}
    (hp : IsPushout i a b j) (y : Objects Y.val) :
    (∃ x : Objects B.val, b.toOneFunctor.obj x = y) ∨
      ∃ x : Objects X.val, j.toOneFunctor.obj x = y :=
  Types.eq_or_eq_of_isPushout (hp.map (finiteObjectFunctor n)) y

end Thomason.Construction.StrictOmegaCategory

end

section

/-!
# Vertices of the concrete oriental

The degree-zero positive chains of augmentation one are single vertices.
This starts the object and full-segment identification needed for labelled
pieces of categorified poset nerves.
-/

namespace Thomason.Construction.SimplexComplex

open scoped BigOperators

/-- The zero-simplex at a specified vertex. -/
def vertexBasis {m : ℕ} (i : Fin (m + 1)) : Basis m 0 :=
  OrderEmbedding.ofStrictMono (fun _ : Fin 1 => i) (by
    intro a b hab
    have he : a = b := by omega
    subst b
    exact (lt_irrefl _ hab).elim)

@[simp]
theorem vertexBasis_apply {m : ℕ} (i : Fin (m + 1)) (j : Fin 1) : vertexBasis i j = i := rfl

theorem basis_zero_eq_vertex {m : ℕ} (s : Basis m 0) : s = vertexBasis (s 0) := by
  apply DFunLike.ext
  intro j
  have he : j = 0 := by omega
  subst j
  rfl

/-- Positivity and augmentation force a degree-zero chain to be one vertex. -/
theorem positive_augmentation_one {m : ℕ} (x : Chains m 0)
    (hx : x ∈ positive m 0) (haug : augmentation m x = 1) :
    ∃ i : Fin (m + 1), x = Finsupp.single (vertexBasis i) 1 := by
  classical
  have hsum : ∑ s ∈ x.support, x s = 1 := by
    simpa [augmentation, Finsupp.linearCombination_apply, Finsupp.sum] using haug
  have hne : x ≠ 0 := by
    intro he
    simp [he] at hsum
  obtain ⟨s, hs⟩ := Finsupp.ne_iff.mp hne
  change x s ≠ 0 at hs
  have hsm : s ∈ x.support := Finsupp.mem_support_iff.mpr hs
  have hsle : x s ≤ 1 := by
    have ht := Finset.single_le_sum (fun t (_ : t ∈ x.support) => hx t) hsm
    exact ht.trans_eq hsum
  have hsone : x s = 1 := by have hp := hx s; omega
  have hrest : ∑ t ∈ x.support.erase s, x t = 0 := by
    have ht := Finset.sum_erase_add x.support (fun t => x t) hsm
    rw [hsum, hsone] at ht
    omega
  have hxs : x = Finsupp.single s 1 := by
    apply Finsupp.ext
    intro t
    by_cases hts : t = s
    · subst t
      simp [hsone]
    · rw [Finsupp.single_eq_of_ne hts]
      by_cases hzero : x t = 0
      · exact hzero
      · have htm : t ∈ x.support.erase s :=
          Finset.mem_erase.mpr ⟨hts, Finsupp.mem_support_iff.mpr hzero⟩
        have htle : x t ≤ 0 :=
          (Finset.single_le_sum (fun u (_ : u ∈ x.support.erase s) => hx u) htm).trans_eq hrest
        exact le_antisymm htle (hx t)
  exact ⟨s 0, hxs.trans (congrArg (fun t => Finsupp.single t (1 : ℤ)) (basis_zero_eq_vertex s))⟩

/-- The strict zero-cell at a vertex, as a full positive globular table. -/
noncomputable def vertex (h : NormalizedSimplexIdentities) {m : ℕ} (i : Fin (m + 1)) : h.object m where
  table _ n := match n with
    | 0 => Finsupp.single (vertexBasis i) 1
    | _ + 1 => 0
  positive a n := by
    cases n with
    | zero =>
      intro s
      classical
      simp only [Finsupp.single_apply]
      split_ifs <;> norm_num
    | succ n => exact (positive m (n + 1)).zero_mem
  augmentation a := augmentation_single m (vertexBasis i) 1
  boundary a n := by
    cases n <;> simp
  finite_support := ⟨0, fun n hn a => by cases n <;> first | omega | rfl⟩

/-- The constructed vertex is zero-dimensional. -/
theorem vertex_dimensionLE (h : NormalizedSimplexIdentities) {m : ℕ} (i : Fin (m + 1)) :
    (h.object m).DimensionLE 0 (vertex h i) := by
  constructor <;> apply DirectedComplex.Cell.ext <;> funext a n
  all_goals cases n <;> rfl

/-- Every zero-dimensional cell of an oriental is a vertex. -/
theorem eq_vertex_of_dimensionLE (h : NormalizedSimplexIdentities) {m : ℕ}
    (x : h.object m) (hx : (h.object m).DimensionLE 0 x) :
    ∃ i : Fin (m + 1), x = vertex h i := by
  obtain ⟨i, hi⟩ := positive_augmentation_one (x.table false 0) (x.positive false 0) (x.augmentation false)
  refine ⟨i, ?_⟩
  apply DirectedComplex.Cell.ext
  funext a n
  have hf := congrArg (fun y : h.object m => y.table a n) hx.1
  exact hf.symm.trans (by
    cases n with
    | zero => exact hi
    | succ n => rfl)

/-- Distinct vertices define distinct strict cells. -/
theorem vertex_injective (h : NormalizedSimplexIdentities) {m : ℕ} :
    Function.Injective (vertex h (m := m)) := by
  classical
  intro i j he
  have ht := congrArg (fun x : h.object m => x.table false 0 (vertexBasis i)) he
  by_contra hij
  have hb : vertexBasis i ≠ vertexBasis j := fun h => hij (congrArg (fun s : Basis m 0 => s 0) h)
  change (Finsupp.single (vertexBasis i) (1 : ℤ)) (vertexBasis i) =
    (Finsupp.single (vertexBasis j) (1 : ℤ)) (vertexBasis i) at ht
  simp only [Finsupp.single_eq_same, Finsupp.single_eq_of_ne hb] at ht
  norm_num at ht

/-- Normalized ordinal maps preserve the explicitly constructed vertices. -/
theorem map_vertex (h : NormalizedSimplexIdentities) {m n : ℕ}
    (f : Fin (m + 1) →o Fin (n + 1)) (i : Fin (m + 1)) :
    (h.map f).toFun (vertex h i) = vertex h (f i) := by
  have hmono : StrictMono (fun j : Fin 1 => f (vertexBasis i j)) := by
    intro a b hab
    have he : a = b := by omega
    subst b
    exact (lt_irrefl _ hab).elim
  have hb : mapBasis f 0 (vertexBasis i) = Finsupp.single (vertexBasis (f i)) 1 := by
    rw [mapBasis, dite_eq_left hmono]
    rfl
  apply DirectedComplex.Cell.ext
  funext a p
  cases p with
  | zero =>
    change mapChains f 0 (Finsupp.single (vertexBasis i) 1) = _
    exact (mapChains_single f 0 _ 1).trans ((one_smul ℤ _).trans hb)
  | succ p =>
    change mapChains f (p + 1) 0 = 0
    exact map_zero _

/-- The objects of the concrete oriental are canonically its ordered vertices. -/
noncomputable def objectsEquiv (h : NormalizedSimplexIdentities) (m : ℕ) :
    StrictOmegaCategory.Objects (h.object m) ≃ Fin (m + 1) where
  toFun x := (eq_vertex_of_dimensionLE h x.val x.property).choose
  invFun i := ⟨vertex h i, vertex_dimensionLE h i⟩
  left_inv x := Subtype.ext (eq_vertex_of_dimensionLE h x.val x.property).choose_spec.symm
  right_inv i := (vertex_injective h (eq_vertex_of_dimensionLE h (vertex h i)
    (vertex_dimensionLE h i)).choose_spec).symm

@[simp]
theorem objectsEquiv_symm_val (h : NormalizedSimplexIdentities) (m : ℕ) (i : Fin (m + 1)) :
    ((objectsEquiv h m).symm i).val = vertex h i := rfl

/-- The vertex classification is natural for every ordinal operator. -/
theorem objectsEquiv_map (h : NormalizedSimplexIdentities) {m n : ℕ}
    (f : Fin (m + 1) →o Fin (n + 1)) (x : StrictOmegaCategory.Objects (h.object m)) :
    objectsEquiv h n ((h.map f).toOneFunctor.obj x) = f (objectsEquiv h m x) := by
  apply (objectsEquiv h n).symm.injective
  apply Subtype.ext
  change vertex h _ = vertex h _
  have hx := (eq_vertex_of_dimensionLE h x.val x.property).choose_spec
  have hy := (eq_vertex_of_dimensionLE h ((h.map f).toFun x.val)
    ((h.map f).dimensionLE x.property)).choose_spec
  exact hy.symm.trans ((congrArg (h.map f).toFun hx).trans (map_vertex h f _))

end Thomason.Construction.SimplexComplex

end

section

/-!
# Objects in the oriental presentation

Every object of categorification is the image of a vertex of an oriental.
The canonical vertex maps and their compatibility use all simplex operators,
including degeneracies.
-/

namespace Thomason.Construction.NormalizedSimplexIdentities

open CategoryTheory CategoryTheory.Limits Opposite
open StrictOmegaCategory
open scoped Simplicial

variable (h : NormalizedSimplexIdentities) [StrictColimitsInput]

/-- A vertex of a simplicial set gives an object in its categorification. -/
noncomputable def vertexObject (K : SSet.{0}) (v : K _⦋0⦌) :
    Objects (h.categorification.obj K) :=
  (h.simplexLeg (SSet.yonedaEquiv.symm v)).toOneFunctor.obj
    ⟨SimplexComplex.vertex h 0, SimplexComplex.vertex_dimensionLE h 0⟩

/-- The image of any oriental vertex is already represented by its
zero-simplex in the simplicial set. -/
theorem simplexLeg_vertex {K : SSet.{0}} {m : SimplexCategory}
    (s : SSet.stdSimplex.obj m ⟶ K) (i : Fin (m.len + 1)) :
    (h.simplexLeg s).toFun (SimplexComplex.vertex h i) =
      (h.vertexObject K (K.map (SimplexCategory.const (.mk 0) m i).op
        (SSet.yonedaEquiv s))).val := by
  let a : SimplexCategory.mk 0 ⟶ m := SimplexCategory.const _ _ i
  have hn := h.simplexLeg_precomp s a
  have he : SSet.stdSimplex.map a ≫ s =
      SSet.yonedaEquiv.symm (K.map a.op (SSet.yonedaEquiv s)) := by
    apply SSet.yonedaEquiv.injective
    simpa only [Equiv.apply_symm_apply] using (SSet.yonedaEquiv_naturality a s).symm
  have hv := SimplexComplex.map_vertex h a.toOrderHom 0
  have hh := congrArg (fun f : h.object 0 ⟶ h.categorification.obj K =>
    f.toFun (SimplexComplex.vertex h 0)) hn
  change (h.simplexLeg s).toFun ((h.map a.toOrderHom).toFun (SimplexComplex.vertex h 0)) = _ at hh
  rw [hv, he] at hh
  exact hh

/-- Every object of categorification is represented by an original vertex. -/
theorem vertexObject_surjective (K : SSet.{0}) : Function.Surjective (h.vertexObject K) := by
  intro x
  have hc := isColimitOfPreserves objectFunctor (h.simplexCocone_isColimit K)
  obtain ⟨s, y, hy⟩ := Types.jointly_surjective_of_isColimit hc x
  obtain ⟨i, hi⟩ := SimplexComplex.eq_vertex_of_dimensionLE h y.val y.property
  refine ⟨K.map (SimplexCategory.const (.mk 0) s.left i).op
    (SSet.yonedaEquiv s.hom), ?_⟩
  apply Subtype.ext
  have hey : (h.simplexLeg s.hom).toFun y.val = x.val :=
    congrArg Subtype.val hy
  exact (h.simplexLeg_vertex s.hom i).symm.trans
    ((congrArg (h.simplexLeg s.hom).toFun hi).symm.trans hey)

/-- The vertex representation commutes with every simplicial map. -/
theorem vertexObject_naturality {K L : SSet.{0}} (f : K ⟶ L) (v : K _⦋0⦌) :
    (h.categorification.map f).toOneFunctor.obj (h.vertexObject K v) =
      h.vertexObject L (f.app _ v) := by
  apply Subtype.ext
  have he := h.simplexLeg_postcomp (SSet.yonedaEquiv.symm v) f
  have hy : SSet.yonedaEquiv.symm v ≫ f = SSet.yonedaEquiv.symm (f.app _ v) :=
    SSet.yonedaEquiv_symm_comp v f
  rw [hy] at he
  exact congrArg (fun g : h.object 0 ⟶ h.categorification.obj L =>
    g.toFun (SimplexComplex.vertex h 0)) he

/-- Read the original vertex carried by an object of one presentation simplex. -/
noncomputable def simplexVertex {K : SSet.{0}} {m : SimplexCategory}
    (s : SSet.stdSimplex.obj m ⟶ K) (x : Objects (h.object m.len)) : K _⦋0⦌ :=
  K.map (SimplexCategory.const (.mk 0) m (SimplexComplex.objectsEquiv h m.len x)).op
    (SSet.yonedaEquiv s)

omit [StrictColimitsInput] in
/-- Vertex readings respect every map in the simplex presentation. -/
theorem simplexVertex_precomp {K : SSet.{0}} {m n : SimplexCategory}
    (s : SSet.stdSimplex.obj n ⟶ K) (a : m ⟶ n) (x : Objects (h.object m.len)) :
    h.simplexVertex (SSet.stdSimplex.map a ≫ s) x =
      h.simplexVertex s ((h.map a.toOrderHom).toOneFunctor.obj x) := by
  unfold simplexVertex
  rw [SimplexComplex.objectsEquiv_map]
  have he : SSet.yonedaEquiv (SSet.stdSimplex.map a ≫ s) =
      K.map a.op (SSet.yonedaEquiv s) := (SSet.yonedaEquiv_naturality a s).symm
  rw [he, ← CategoryTheory.comp_apply, ← K.map_comp]
  rfl

/-- The compatible vertex readings form a cocone of sets. -/
noncomputable def vertexCocone (K : SSet.{0}) :
    Cocone ((CostructuredArrow.proj SSet.stdSimplex K ⋙ h.cosimplicial) ⋙ objectFunctor) where
  pt := K _⦋0⦌
  ι :=
    { app := fun s => ↾(h.simplexVertex s.hom)
      naturality := by
        intro s t a
        apply ConcreteCategory.hom_ext
        intro x
        change h.simplexVertex t.hom ((h.map a.left.toOrderHom).toOneFunctor.obj x) =
          h.simplexVertex s.hom x
        have he := h.simplexVertex_precomp t.hom a.left x
        rw [CostructuredArrow.w a] at he
        exact he.symm }

/-- The inverse reading of the vertices of categorification. -/
noncomputable def readVertex (K : SSet.{0}) : Objects (h.categorification.obj K) → K _⦋0⦌ :=
  (isColimitOfPreserves objectFunctor (h.simplexCocone_isColimit K)).desc (h.vertexCocone K)

/-- Reading a vertex on a presentation leg returns that simplex's vertex. -/
theorem readVertex_simplexLeg {K : SSet.{0}} {m : SimplexCategory}
    (s : SSet.stdSimplex.obj m ⟶ K) (x : Objects (h.object m.len)) :
    h.readVertex K ((h.simplexLeg s).toOneFunctor.obj x) = h.simplexVertex s x := by
  have he := (isColimitOfPreserves objectFunctor (h.simplexCocone_isColimit K)).fac
    (h.vertexCocone K) (CostructuredArrow.mk s)
  exact ConcreteCategory.congr_hom he x

@[simp]
theorem readVertex_vertexObject (K : SSet.{0}) (v : K _⦋0⦌) :
    h.readVertex K (h.vertexObject K v) = v := by
  let x : Objects (h.object 0) :=
    ⟨SimplexComplex.vertex h 0, SimplexComplex.vertex_dimensionLE h 0⟩
  have he := h.readVertex_simplexLeg (m := .mk 0) (SSet.yonedaEquiv.symm v) x
  refine he.trans ?_
  have hi : SimplexComplex.objectsEquiv h 0 x = 0 :=
    (SimplexComplex.objectsEquiv h 0).apply_symm_apply 0
  change K.map (SimplexCategory.const (.mk 0) (.mk 0)
    (SimplexComplex.objectsEquiv h 0 x)).op (SSet.yonedaEquiv (SSet.yonedaEquiv.symm v)) = v
  rw [hi, SimplexCategory.const_eq_id, op_id, K.map_id]
  exact SSet.yonedaEquiv.apply_symm_apply v

/-- Objects of categorification are exactly the original vertices. -/
noncomputable def categorificationObjectsEquiv (K : SSet.{0}) :
    Objects (h.categorification.obj K) ≃ K _⦋0⦌ where
  toFun := h.readVertex K
  invFun := h.vertexObject K
  left_inv x := by
    obtain ⟨v, rfl⟩ := h.vertexObject_surjective K x
    rw [readVertex_vertexObject]
  right_inv := h.readVertex_vertexObject K

/-- Reading vertices is natural for arbitrary simplicial maps. -/
theorem categorificationObjectsEquiv_naturality {K L : SSet.{0}} (f : K ⟶ L)
    (x : Objects (h.categorification.obj K)) :
    h.categorificationObjectsEquiv L ((h.categorification.map f).toOneFunctor.obj x) =
      f.app _ (h.categorificationObjectsEquiv K x) := by
  obtain ⟨v, rfl⟩ := h.vertexObject_surjective K x
  change h.readVertex L ((h.categorification.map f).toOneFunctor.obj (h.vertexObject K v)) =
    f.app _ (h.readVertex K (h.vertexObject K v))
  rw [h.vertexObject_naturality f v, readVertex_vertexObject, readVertex_vertexObject]

end Thomason.Construction.NormalizedSimplexIdentities

end

section

/-!
# The ordered endpoints of oriental cells

A cell of an oriental cannot have decreasing object endpoints. We reduce
this to positivity of the single edge of the first oriental, by a monotone
cut to [1]. The calculation uses the normalized differential.
-/

namespace Thomason.Construction.SimplexComplex

open CategoryTheory StrictOmegaCategory
open scoped BigOperators

/-- The unique top-dimensional basis edge of the first simplex. -/
def intervalEdge : Basis 1 1 := OrderEmbedding.ofStrictMono id strictMono_id

theorem interval_basis_eq (s : Basis 1 1) : s = intervalEdge := by
  have hh := s.strictMono (show (0 : Fin 2) < 1 by decide)
  have h0 : s 0 = 0 := by apply Fin.ext; change (s 0).val = 0; omega
  have h1 : s 1 = 1 := by apply Fin.ext; change (s 1).val = 1; omega
  apply DFunLike.ext
  intro i
  have hi : i = 0 ∨ i = 1 := by omega
  rcases hi with rfl | rfl
  · exact h0
  · exact h1

theorem interval_chain_eq (x : Chains 1 1) : x = Finsupp.single intervalEdge (x intervalEdge) := by
  apply Finsupp.ext
  intro s
  rw [interval_basis_eq s, Finsupp.single_eq_same]

theorem interval_differential (z : ℤ) :
    differential 1 0 (Finsupp.single intervalEdge z) =
      Finsupp.single (vertexBasis 1) z - Finsupp.single (vertexBasis 0) z := by
  have h0 : deleteVertex intervalEdge 0 = vertexBasis 1 := by
    apply DFunLike.ext
    intro i
    have hi : i = 0 := by omega
    subst i
    rfl
  have h1 : deleteVertex intervalEdge 1 = vertexBasis 0 := by
    apply DFunLike.ext
    intro i
    have hi : i = 0 := by omega
    subst i
    rfl
  rw [differential_single]
  simp [differentialBasis, Fin.sum_univ_succ, h0, h1, sub_eq_add_neg]

/-- Positivity rules out a cell from vertex one to vertex zero in O[1]. -/
theorem interval_no_backward (h : NormalizedSimplexIdentities) (x : h.object 1)
    (hs : (h.object 1).source 0 x = vertex h 1)
    (ht : (h.object 1).target 0 x = vertex h 0) : False := by
  have hs0 := congrArg (fun y : h.object 1 => y.table false 0) hs
  have ht0 := congrArg (fun y : h.object 1 => y.table true 0) ht
  change x.table false 0 = Finsupp.single (vertexBasis 1) 1 at hs0
  change x.table true 0 = Finsupp.single (vertexBasis 0) 1 at ht0
  have hb := x.boundary false 0
  change differential 1 0 (x.table false 1) = x.table true 0 - x.table false 0 at hb
  rw [interval_chain_eq (x.table false 1), interval_differential, hs0, ht0] at hb
  have hz := congrArg (fun z : Chains 1 0 => z (vertexBasis 0)) hb
  have hv : vertexBasis (0 : Fin 2) ≠ vertexBasis 1 := by
    intro he
    have hh := congrArg (fun s : Basis 1 0 => s 0) he
    exact (by decide : (0 : Fin 2) ≠ 1) hh
  simp only [Finsupp.sub_apply, Finsupp.single_eq_same, Finsupp.single_eq_of_ne hv] at hz
  have hp := x.positive false 1 intervalEdge
  omega

/-- Any oriental cell has nondecreasing zero-dimensional endpoints. -/
theorem endpoints_ordered (h : NormalizedSimplexIdentities) {m : ℕ} (x : h.object m) :
    objectsEquiv h m ((h.object m).boundaryObject false x) ≤
      objectsEquiv h m ((h.object m).boundaryObject true x) := by
  classical
  let s := objectsEquiv h m ((h.object m).boundaryObject false x)
  let t := objectsEquiv h m ((h.object m).boundaryObject true x)
  change s ≤ t
  by_contra hst
  let cut : Fin (m + 1) →o Fin 2 :=
    { toFun := fun i => if i ≤ t then 0 else 1
      monotone' := by
        intro a b hab
        dsimp
        by_cases ha : a ≤ t <;> by_cases hb : b ≤ t <;>
          simp only [ha, hb, ite_true, ite_false]
        all_goals first | decide | exact (ha (hab.trans hb)).elim }
  have hcuts : cut s = 1 := ite_eq_right hst
  have hcutt : cut t = 0 := ite_eq_left le_rfl
  have hs : (h.object m).source 0 x = vertex h s :=
    (objectsEquiv h m).symm_apply_apply ((h.object m).boundaryObject false x) |>.symm |>
      congrArg Subtype.val
  have ht : (h.object m).target 0 x = vertex h t :=
    (objectsEquiv h m).symm_apply_apply ((h.object m).boundaryObject true x) |>.symm |>
      congrArg Subtype.val
  apply interval_no_backward h ((h.map cut).toFun x)
  · exact ((h.map cut).map_face false 0 x).symm.trans
      ((congrArg (h.map cut).toFun hs).trans ((map_vertex h cut s).trans (congrArg (vertex h) hcuts)))
  · exact ((h.map cut).map_face true 0 x).symm.trans
      ((congrArg (h.map cut).toFun ht).trans ((map_vertex h cut t).trans (congrArg (vertex h) hcutt)))

end Thomason.Construction.SimplexComplex

end

section

/-! # Composition generation by the cell images of a strict colimit

Faces do not require additional generators because each cocone leg preserves
them. The proof uses the colimit universal property and the generated strict
subcategory, without any assertion that underlying sets preserve colimits.
-/

namespace Thomason.Construction.StrictOmegaCategory.ColimitGeneration

open CategoryTheory CategoryTheory.Limits

noncomputable section

variable {J : Type} [Category.{0} J] {F : J ⥤ StrictOmegaCategory.{0}} (s : Cocone F)

abbrev Index := Σ j, F.obj j

def generators (i : Index (F := F)) : s.pt := (s.ι.app i.1).toFun i.2

private theorem generators_face (i : Index (F := F)) (a : Bool) (n : ℕ) :
    Nonempty (CompositionExpression s.pt (generators s)
      (s.pt.face a n (generators s i))) := by
  rcases i with ⟨j, x⟩
  change Nonempty (CompositionExpression _ _ (s.pt.face a n ((s.ι.app j).toFun x)))
  have he : s.pt.face a n ((s.ι.app j).toFun x) =
      (s.ι.app j).toFun ((F.obj j).face a n x) := (s.ι.app j).map_face a n x |>.symm
  rw [he]
  exact ⟨CompositionExpression.generator (C := s.pt) (g := generators s)
    ⟨j, (F.obj j).face a n x⟩⟩

private def generated : StrictOmegaCategory.{0} where
  Cell := {x : s.pt // Nonempty (CompositionExpression s.pt (generators s) x)}
  face a n x := ⟨s.pt.face a n x.val, by
    obtain ⟨t⟩ := x.property
    exact t.face (generators_face s) a n⟩
  comp n x y h := ⟨s.pt.comp n x.val y.val (congrArg Subtype.val h), by
    obtain ⟨tx⟩ := x.property
    obtain ⟨ty⟩ := y.property
    exact ⟨.comp n (congrArg Subtype.val h) tx ty⟩⟩
  globular a b m n x := by
    apply Subtype.ext
    exact (s.pt.globular a b m n x.val).trans (by split_ifs <;> rfl)
  source_comp n x y h := Subtype.ext (s.pt.source_comp n x.val y.val _)
  target_comp n x y h := Subtype.ext (s.pt.target_comp n x.val y.val _)
  face_comp a m n hnm x y h h' :=
    Subtype.ext (s.pt.face_comp a m n hnm x.val y.val _ _)
  left_unit n x h := Subtype.ext (s.pt.left_unit n x.val _)
  right_unit n x h := Subtype.ext (s.pt.right_unit n x.val _)
  assoc n x y z hxy hyz hl hr := Subtype.ext (s.pt.assoc n x.val y.val z.val _ _ _ _)
  interchange m n hmn a b c d hab hcd hac hbd hl hr :=
    Subtype.ext (s.pt.interchange m n hmn a.val b.val c.val d.val _ _ _ _ _ _)
  finite_dimension x := by
    obtain ⟨n, hn⟩ := s.pt.finite_dimension x.val
    exact ⟨n, Subtype.ext hn.1, Subtype.ext hn.2⟩

private def inclusion : generated s ⟶ s.pt where
  toFun := Subtype.val
  map_face _ _ _ := rfl
  map_comp _ _ _ _ _ := rfl

private def leg (j : J) : F.obj j ⟶ generated s where
  toFun x := ⟨(s.ι.app j).toFun x,
    ⟨CompositionExpression.generator (C := s.pt) (g := generators s) ⟨j, x⟩⟩⟩
  map_face a n x := Subtype.ext ((s.ι.app j).map_face a n x)
  map_comp n x y h h' := Subtype.ext ((s.ι.app j).map_comp n x y h
    (congrArg Subtype.val h'))

private def cocone : Cocone F where
  pt := generated s
  ι := {
    app := leg s
    naturality j k f := by
      apply Hom.ext
      funext x
      apply Subtype.ext
      exact congrArg (fun h : F.obj j ⟶ s.pt => h.toFun x) (s.w f) }

theorem generated_by_pieces (hs : IsColimit s) (x : s.pt) :
    Nonempty (CompositionExpression s.pt (generators s) x) := by
  let lift : s.pt ⟶ generated s := hs.desc (cocone s)
  have he : lift ≫ inclusion s = 𝟙 s.pt := by
    apply hs.hom_ext
    intro j
    rw [← Category.assoc]
    have hf : s.ι.app j ≫ lift = leg s j := hs.fac (cocone s) j
    rw [hf]
    apply Hom.ext
    rfl
  have hx : (lift.toFun x).val = x :=
    congrArg (fun h : s.pt ⟶ s.pt => h.toFun x) he
  exact hx ▸ (lift.toFun x).property

end
end Thomason.Construction.StrictOmegaCategory.ColimitGeneration

end

section

/-! # A strict terminal cone for the endpoint-fibre adjunction

Adjoin a terminal object to a strict omega-category, with a unique arrow
from each old object to the new one and no nonidentity higher cells over
those arrows. This is the concrete construction needed for the right
adjoint of the zero-fibre functor.
-/

namespace Thomason.Construction.StrictOmegaCategory.TerminalCone

open CategoryTheory

inductive Cell (C : StrictOmegaCategory.{0})
  | old (x : C)
  | tip
  | arrow (x : Objects C)

variable {C : StrictOmegaCategory.{0}}

def face (a : Bool) (n : ℕ) : Cell C → Cell C
  | .old x => .old (C.face a n x)
  | .tip => .tip
  | .arrow x => match n with
    | 0 => if a then .tip else .old x.val
    | _ + 1 => .arrow x

theorem object_face (a : Bool) (n : ℕ) (x : Objects C) : C.face a n x.val = x.val := by
  have hx := C.dimensionLE_mono (Nat.zero_le n) x.property
  cases a
  · exact hx.1
  · exact hx.2

theorem globular (a b : Bool) (m n : ℕ) (x : Cell C) :
    face a m (face b n x) = if m < n then face a m x else face b n x := by
  cases x with
  | old x =>
    change Cell.old (C.face a m (C.face b n x)) = _
    rw [C.globular]
    split_ifs <;> rfl
  | tip => simp [face]
  | arrow x =>
    cases m <;> cases n <;> cases a <;> cases b <;> simp [face, object_face]

def comp (n : ℕ) : (x y : Cell C) → face true n x = face false n y → Cell C
  | .old x, .old y, h => .old (C.comp n x y (Cell.old.inj h))
  | .old x, _, _ => .arrow (C.boundaryObject false x)
  | .tip, _, _ => .tip
  | .arrow x, _, _ => .arrow x

theorem source_comp (n : ℕ) (x y : Cell C) (h : face true n x = face false n y) :
    face false n (comp n x y h) = face false n x := by
  cases x <;> cases y <;> cases n <;>
    (have hh := h; simp [face] at hh <;> simp_all [face, comp, C.source_comp, boundaryObject])

theorem target_comp (n : ℕ) (x y : Cell C) (h : face true n x = face false n y) :
    face true n (comp n x y h) = face true n y := by
  cases x <;> cases y <;> cases n <;>
    (have hh := h; simp [face] at hh <;> simp_all [face, comp, C.target_comp, boundaryObject])

theorem left_unit (n : ℕ) (x : Cell C)
    (h : face true n (face false n x) = face false n x) :
    comp n (face false n x) x h = x := by
  cases x <;> cases n <;> simp_all [face, comp, C.left_unit, boundaryObject_of_object]

theorem right_unit (n : ℕ) (x : Cell C)
    (h : face true n x = face false n (face true n x)) :
    comp n x (face true n x) h = x := by
  cases x <;> cases n <;> simp_all [face, comp, C.right_unit]

end Thomason.Construction.StrictOmegaCategory.TerminalCone

end

section

/-! # Associativity and interchange for the strict terminal cone -/

namespace Thomason.Construction.StrictOmegaCategory.TerminalCone

variable {C : StrictOmegaCategory.{0}}

@[simp]
theorem boundaryObject_face_succ (a b : Bool) (n : ℕ) (x : C) :
    C.boundaryObject a (C.face b (n + 1) x) = C.boundaryObject a x := by
  apply Subtype.ext
  exact (C.globular a b 0 (n + 1) x).trans (ite_eq_left (Nat.zero_lt_succ n))

@[simp]
theorem boundaryObject_comp (n : ℕ) (x y : C) (h : C.target n x = C.source n y) :
    C.boundaryObject false (C.comp n x y h) = C.boundaryObject false x := by
  apply Subtype.ext
  cases n with
  | zero => exact C.source_comp 0 x y h
  | succ n => exact C.zero_face_comp_succ false n x y h

theorem face_comp (a : Bool) (m n : ℕ) (hnm : n < m) (x y : Cell C)
    (h : face true n x = face false n y)
    (h' : face true n (face a m x) = face false n (face a m y)) :
    face a m (comp n x y h) = comp n (face a m x) (face a m y) h' := by
  cases m with
  | zero => omega
  | succ m =>
    cases x <;> cases y <;> cases n <;>
      (have hh := h; simp [face] at hh <;>
        simp_all [face, comp])
    all_goals exact C.face_comp a _ _ (by omega) _ _ _ _

theorem assoc (n : ℕ) (x y z : Cell C)
    (hxy : face true n x = face false n y)
    (hyz : face true n y = face false n z)
    (hl : face true n (comp n x y hxy) = face false n z)
    (hr : face true n x = face false n (comp n y z hyz)) :
    comp n (comp n x y hxy) z hl = comp n x (comp n y z hyz) hr := by
  cases x <;> cases y <;> cases z <;> cases n <;>
    (have hh := hxy; have hk := hyz; simp [face] at hh hk <;>
      simp_all [comp])
  all_goals exact C.assoc _ _ _ _ _ _ _ _

theorem interchange (m n : ℕ) (hmn : m < n) (a b c d : Cell C)
    (hab : face true m a = face false m b)
    (hcd : face true m c = face false m d)
    (hac : face true n a = face false n c)
    (hbd : face true n b = face false n d)
    (hl : face true n (comp m a b hab) = face false n (comp m c d hcd))
    (hr : face true m (comp n a c hac) = face false m (comp n b d hbd)) :
    comp n (comp m a b hab) (comp m c d hcd) hl =
      comp m (comp n a c hac) (comp n b d hbd) hr := by
  cases n with
  | zero => omega
  | succ n =>
    cases a <;> cases c <;>
      (have hh := hac; simp [face] at hh <;>
        cases b <;> cases d <;>
          (have hk := hbd; simp [face] at hk <;>
            cases m <;>
              (have h₁ := hab; have h₂ := hcd; simp [face] at h₁ h₂ <;>
                simp_all [comp])))
    all_goals exact C.interchange _ _ (by omega) _ _ _ _ _ _ _ _ _ _

end Thomason.Construction.StrictOmegaCategory.TerminalCone

end

section

/-! # The actual strict terminal cone and its full zero-fibre -/

namespace Thomason.Construction.StrictOmegaCategory.TerminalCone

open CategoryTheory

/-- Adjoin a terminal vertex and one arrow from each original object. -/
def category (C : StrictOmegaCategory.{0}) : StrictOmegaCategory.{0} where
  Cell := Cell C
  face := face
  globular := globular
  comp := comp
  source_comp := source_comp
  target_comp := target_comp
  face_comp := face_comp
  left_unit := left_unit
  right_unit := right_unit
  assoc := assoc
  interchange := interchange
  finite_dimension x := by
    cases x with
    | old x =>
      obtain ⟨n, hs, ht⟩ := C.finite_dimension x
      exact ⟨n, congrArg Cell.old hs, congrArg Cell.old ht⟩
    | tip => exact ⟨0, rfl, rfl⟩
    | arrow x => exact ⟨1, rfl, rfl⟩

def inclusion (C : StrictOmegaCategory.{0}) : C ⟶ category C where
  toFun := Cell.old
  map_face _ _ _ := rfl
  map_comp _ _ _ _ _ := rfl

variable {C : StrictOmegaCategory.{0}}

def labelCell : Cell C → StrictPoset.Cell (Fin 2)
  | .old _ => StrictPoset.identity 0
  | .tip => StrictPoset.identity 1
  | .arrow _ => ⟨0, 1, by decide⟩

/-- The cone is canonically a strict category over the walking arrow. -/
def label (C : StrictOmegaCategory.{0}) : category C ⟶ StrictPoset.category (Fin 2) where
  toFun := labelCell
  map_face a n x := by
    cases x <;> cases n <;> cases a <;> rfl
  map_comp n x y h h' := by
    have hh : face true n x = face false n y := h
    cases x <;> cases y <;> cases n <;>
      (simp [face] at hh <;> apply StrictPoset.Cell.ext <;> rfl)

theorem inclusion_label (C : StrictOmegaCategory.{0}) (x : C) :
    (label C).toFun ((inclusion C).toFun x) = StrictPoset.identity 0 := rfl

/-- The old category is the actual full zero-fibre of the cone label. -/
def zeroFiberInclusion (C : StrictOmegaCategory.{0}) : C ⟶ labelFiber (label C) 0 where
  toFun x := ⟨Cell.old x, (fullCell_label_iff (label C) 0 _).mpr rfl⟩
  map_face _ _ _ := Subtype.ext rfl
  map_comp _ _ _ _ _ := Subtype.ext rfl

theorem zeroFiberInclusion_bijective (C : StrictOmegaCategory.{0}) :
    Function.Bijective (zeroFiberInclusion C).toFun := by
  constructor
  · intro x y he
    exact Cell.old.inj (congrArg Subtype.val he)
  · rintro ⟨x, hx⟩
    have hz := (fullCell_label_iff (label C) 0 x).mp hx
    change labelCell x = StrictPoset.identity 0 at hz
    cases x with
    | old x => exact ⟨x, Subtype.ext rfl⟩
    | tip =>
      have he := congrArg StrictPoset.Cell.first hz
      exact (by decide : (1 : Fin 2) ≠ 0) he |>.elim
    | arrow x =>
      have he := congrArg StrictPoset.Cell.last hz
      exact (by decide : (1 : Fin 2) ≠ 0) he |>.elim

noncomputable def zeroFiberIso (C : StrictOmegaCategory.{0}) : C ≅ labelFiber (label C) 0 :=
  isoOfBijective (zeroFiberInclusion C) (zeroFiberInclusion_bijective C)

/-- Positive finite dimension is preserved by adjoining the terminal cone. -/
theorem isTruncated {n : ℕ} (hn : 1 ≤ n) (hC : C.IsTruncated n) :
    (category C).IsTruncated n := by
  intro x
  cases x with
  | old x => exact ⟨congrArg Cell.old (hC x).1, congrArg Cell.old (hC x).2⟩
  | tip => exact ⟨rfl, rfl⟩
  | arrow x =>
    cases n with
    | zero => omega
    | succ n => exact ⟨rfl, rfl⟩

end Thomason.Construction.StrictOmegaCategory.TerminalCone

end

end OAI
