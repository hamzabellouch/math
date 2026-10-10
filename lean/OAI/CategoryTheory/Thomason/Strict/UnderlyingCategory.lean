import OAI.CategoryTheory.Thomason.Simplicial.FaceSimplexLift
import OAI.CategoryTheory.Thomason.Strict.StrictCompositeListReplacement
import OAI.CategoryTheory.Thomason.Strict.StrictIsomorphisms
import OAI.CategoryTheory.Thomason.Transfer.WeakFactorizationRecognition
import Mathlib.AlgebraicTopology.SimplicialSet.SubcomplexColimits
import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.CategoryTheory.Equivalence
import Mathlib.CategoryTheory.Limits.Cones
import Mathlib.CategoryTheory.Limits.Presheaf
import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits
import Mathlib.Order.Hom.Basic
import Mathlib.Tactic

namespace OAI

section

/-!
# Categorification adjoint to the constructed Street nerve

Categorification uses cocompleteness of strict omega-categories: Ara--Maltsiniotis (2014), Section 5, before Proposition 5.1
(arXiv:1305.5086v3, p. 25). We construct the left adjoint by the pointwise
left Kan extension of the actual oriental diagram.
-/

namespace Thomason.Construction

open CategoryTheory CategoryTheory.Limits

/-- The small-colimit specialization of local presentability of strict
omega-categories. -/
class StrictColimitsInput : Prop where
  colimits : HasColimitsOfSize.{0, 0} StrictOmegaCategory.{0}

namespace NormalizedSimplexIdentities

variable (h : NormalizedSimplexIdentities) [c : StrictColimitsInput]

instance : HasColimitsOfSize.{0, 0} StrictOmegaCategory.{0} := c.colimits

/-- Categorification is the colimit of orientals indexed by all simplices. -/
noncomputable def categorification : SSet.{0} ⥤ StrictOmegaCategory.{0} :=
  uliftYoneda.{0}.leftKanExtension h.cosimplicial

/-- Removing the harmless universe lift identifies the restricted Yoneda
functor of the Kan-extension theorem with the actual Street nerve. -/
noncomputable def restrictedYonedaIso :
    Presheaf.restrictedULiftYoneda.{0} h.cosimplicial ≅ h.streetNerve :=
  Functor.isoWhiskerRight uliftYonedaIsoYoneda ((Functor.whiskeringLeft _ _ _).obj h.cosimplicial.op)

/-- The defining adjunction, derived from the colimit universal property. -/
noncomputable def categorificationAdjunction : h.categorification ⊣ h.streetNerve :=
  (Presheaf.uliftYonedaAdjunction.{0} (uliftYoneda.{0}.leftKanExtension h.cosimplicial)
    (uliftYoneda.{0}.leftKanExtensionUnit h.cosimplicial)).ofNatIsoRight h.restrictedYonedaIso

/-- On standard simplices, categorification is naturally the given oriental. -/
noncomputable def categorificationSimplexIso :
    SSet.stdSimplex ⋙ h.categorification ≅ h.cosimplicial :=
  Presheaf.isExtensionAlongULiftYoneda h.cosimplicial

/-- An explicit identification with the simplex colimit, including degeneracies. -/
noncomputable def categorificationObjIsoColimit (K : SSet.{0}) :
    (h.categorification).obj K ≅
      colimit (CostructuredArrow.proj SSet.stdSimplex K ⋙ h.cosimplicial) :=
  SSet.stdSimplex.leftKanExtensionObjIsoColimit h.cosimplicial K

/-- The left adjoint in the stated Thomason adjunction. -/
noncomputable def thomasonLeft : SSet.{0} ⥤ StrictOmegaCategory.{0} :=
  (SSet.sd ⋙ SSet.sd) ⋙ h.categorification

/-- Twice subdivision followed by categorification is genuinely adjoint to
Ex² of the constructed Street nerve. No strict-category model structure is used. -/
noncomputable def thomasonAdjunction : h.thomasonLeft ⊣ h.thomasonRight :=
  (SSet.sdExAdjunction.comp SSet.sdExAdjunction).comp (h.categorificationAdjunction)

/-- The colimit formula also provides every colimit-preservation fact needed
when assembling a simplexwise relative prism. -/
theorem categorification_preservesColimits :
    PreservesColimitsOfSize.{0, 0} (h.categorification) :=
  (h.categorificationAdjunction).leftAdjoint_preservesColimits

end NormalizedSimplexIdentities
end Thomason.Construction

end

section

/-! # Small colimits of strict omega-categories

The carrier is a small quotient of finite formal diagram expressions.
Matching-boundary composition, finite dimension, every strict law and the
colimit universal property were proved directly. This supplies precisely
the cocompleteness needed for the actual categorification adjunction.
-/

namespace Thomason.Construction

open CategoryTheory CategoryTheory.Limits

/-- Every small diagram of small strict omega-categories has the constructed colimit. -/
theorem strictOmegaHasSmallColimits : HasColimitsOfSize.{0,0} StrictOmegaCategory.{0} where
  has_colimits_of_shape _J _ :=
    { has_colimit := fun F =>
        ⟨⟨⟨StrictOmegaCategory.ColimitConstruction.cocone F,
          StrictOmegaCategory.ColimitConstruction.isColimit F⟩⟩⟩ }

/-- Strict omega-categories admit small colimits. -/
instance constructedStrictColimitsInput : StrictColimitsInput where
  colimits := strictOmegaHasSmallColimits

end Thomason.Construction

end

section

/-!
# Canonical oriental presentation of categorified simplicial sets

The legs and their equations are expressed using the actual simplex maps.
The colimit and its compatibilities follow from the Kan extension construction.
-/

namespace Thomason.Construction.NormalizedSimplexIdentities

open CategoryTheory CategoryTheory.Limits Opposite

variable (h : NormalizedSimplexIdentities) [StrictColimitsInput]

/-- The canonical oriental attached to a simplex of a simplicial set. -/
noncomputable def simplexLeg {K : SSet.{0}} {m : SimplexCategory}
    (s : SSet.stdSimplex.obj m ⟶ K) : h.object m.len ⟶ h.categorification.obj K :=
  h.categorificationSimplexIso.inv.app m ≫ h.categorification.map s

/-- The oriental presentation, including degenerate simplices. -/
noncomputable def simplexCocone (K : SSet.{0}) :
    Cocone (CostructuredArrow.proj SSet.stdSimplex K ⋙ h.cosimplicial) :=
  (Cocone.precompose
    (Functor.isoWhiskerLeft (CostructuredArrow.proj SSet.stdSimplex K)
      h.categorificationSimplexIso).inv).obj
    (h.categorification.mapCocone (Presheaf.tautologicalCocone'.{0} K))

/-- This is the actual colimit presentation of categorification. -/
noncomputable def simplexCocone_isColimit (K : SSet.{0}) : IsColimit (h.simplexCocone K) := by
  let p : PreservesColimit
      (CostructuredArrow.proj uliftYoneda.{0} K ⋙ uliftYoneda.{0}) h.categorification :=
    PreservesColimitsOfShape.preservesColimit (self :=
      h.categorificationAdjunction.leftAdjoint_preservesColimits.preservesColimitsOfShape)
  exact (IsColimit.precomposeInvEquiv
    (Functor.isoWhiskerLeft (CostructuredArrow.proj SSet.stdSimplex K)
      h.categorificationSimplexIso) _).symm
    (@isColimitOfPreserves _ _ _ _ _ _ _ h.categorification _
      (Presheaf.isColimitTautologicalCocone'.{0} K) p)

@[simp]
theorem simplexCocone_leg (K : SSet.{0}) (s : CostructuredArrow SSet.stdSimplex K) :
    (h.simplexCocone K).ι.app s = h.simplexLeg s.hom := rfl

/-- Source naturality of a presentation leg. -/
theorem simplexLeg_precomp {K : SSet.{0}} {m n : SimplexCategory}
    (s : SSet.stdSimplex.obj n ⟶ K) (a : m ⟶ n) :
    h.cosimplicial.map a ≫ h.simplexLeg s =
      h.simplexLeg (SSet.stdSimplex.map a ≫ s) := by
  let u : h.object m.len ⟶ h.categorification.obj (SSet.stdSimplex.obj m) :=
    h.categorificationSimplexIso.inv.app m
  let v : h.object n.len ⟶ h.categorification.obj (SSet.stdSimplex.obj n) :=
    h.categorificationSimplexIso.inv.app n
  have hn : h.cosimplicial.map a ≫ v = u ≫ h.categorification.map (SSet.stdSimplex.map a) :=
    h.categorificationSimplexIso.inv.naturality a
  change h.cosimplicial.map a ≫ (v ≫ h.categorification.map s) =
    u ≫ h.categorification.map (SSet.stdSimplex.map a ≫ s)
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun k => k ≫ h.categorification.map s) hn).trans
      ((Category.assoc _ _ _).trans
        (congrArg (fun k => u ≫ k) (h.categorification.map_comp _ _).symm)))

/-- Target naturality of a presentation leg. -/
theorem simplexLeg_postcomp {K L : SSet.{0}} {m : SimplexCategory}
    (s : SSet.stdSimplex.obj m ⟶ K) (f : K ⟶ L) :
    h.simplexLeg s ≫ h.categorification.map f = h.simplexLeg (s ≫ f) := by
  let u : h.object m.len ⟶ h.categorification.obj (SSet.stdSimplex.obj m) :=
    h.categorificationSimplexIso.inv.app m
  change (u ≫ h.categorification.map s) ≫ h.categorification.map f =
    u ≫ h.categorification.map (s ≫ f)
  exact (Category.assoc _ _ _).trans
    (congrArg (fun k => u ≫ k) (h.categorification.map_comp s f).symm)

/-- A poset simplex as its monotone list of vertices. -/
def simplexOrder {E : Type} [PartialOrder E] {m : SimplexCategory}
    (s : (nerve E).obj (op m)) : Fin (m.len + 1) →o E where
  toFun := s.obj
  monotone' := fun _ _ hij => leOfHom (s.map (homOfLE hij))

/-- The corresponding simplex of the ordinary nerve. -/
def orderSimplex {E : Type} [PartialOrder E] {m : ℕ}
    (s : Fin (m + 1) →o E) : (nerve E).obj (op (.mk m)) :=
  s.monotone.functor

omit [StrictColimitsInput] in
@[simp]
theorem simplexOrder_orderSimplex {E : Type} [PartialOrder E] {m : ℕ}
    (s : Fin (m + 1) →o E) : simplexOrder (orderSimplex s) = s := rfl

/-- The oriental map specified by a monotone list of vertices in a poset. -/
noncomputable def posetLeg {E : Type} [PartialOrder E] {m : ℕ}
    (s : Fin (m + 1) →o E) : h.object m ⟶ h.categorification.obj (nerve E) :=
  h.simplexLeg (SSet.yonedaEquiv.symm (orderSimplex s))

/-- All ordinal operators, including degeneracies, act on these canonical legs. -/
theorem posetLeg_precomp {E : Type} [PartialOrder E] {l m : ℕ}
    (s : Fin (m + 1) →o E) (a : Fin (l + 1) →o Fin (m + 1)) :
    h.map a ≫ h.posetLeg s = h.posetLeg (s.comp a) := by
  have he : SSet.stdSimplex.map (SimplexCategory.Hom.mk a) ≫
      SSet.yonedaEquiv.symm (orderSimplex s) =
      SSet.yonedaEquiv.symm (orderSimplex (s.comp a)) := by
    apply SSet.yonedaEquiv.injective
    rfl
  exact (h.simplexLeg_precomp (SSet.yonedaEquiv.symm (orderSimplex s))
    (SimplexCategory.Hom.mk a)).trans (congrArg (h.simplexLeg) he)

omit [StrictColimitsInput] in
/-- Recover a nerve simplex from its monotone vertex map. -/
@[simp]
theorem orderSimplex_simplexOrder {E : Type} [PartialOrder E] {m : SimplexCategory}
    (s : (nerve E).obj (op m)) : orderSimplex (simplexOrder s) = s :=
  nerve.ext_of_isThin rfl

/-- Replacing a simplex by its vertex map does not change its presentation leg. -/
theorem posetLeg_simplexOrder {E : Type} [PartialOrder E] {m : SimplexCategory}
    (s : SSet.stdSimplex.obj m ⟶ nerve E) :
    h.posetLeg (simplexOrder (SSet.yonedaEquiv s)) = h.simplexLeg s := by
  unfold posetLeg
  rw [orderSimplex_simplexOrder, Equiv.symm_apply_apply]

omit [StrictColimitsInput] in
/-- The vertex map of a simplex operator is ordinary precomposition. -/
theorem simplexOrder_precomp {E : Type} [PartialOrder E] {m n : SimplexCategory}
    (s : SSet.stdSimplex.obj n ⟶ nerve E) (a : m ⟶ n) :
    simplexOrder (SSet.yonedaEquiv (SSet.stdSimplex.map a ≫ s)) =
      (simplexOrder (SSet.yonedaEquiv s)).comp a.toOrderHom := by
  have hn := uliftYonedaEquiv_naturality s a.op
  have he : SSet.yonedaEquiv (SSet.stdSimplex.map a ≫ s) =
      (nerve E).map a.op (SSet.yonedaEquiv s) := hn.symm
  exact (congrArg simplexOrder he).trans (by rfl)

/-- Postcomposition by a monotone poset map is natural on canonical legs. -/
theorem posetLeg_postcomp {E F : Type} [PartialOrder E] [PartialOrder F] {m : ℕ}
    (s : Fin (m + 1) →o E) (b : E →o F) :
    h.posetLeg s ≫ h.categorification.map (nerveMap b.monotone.functor) =
      h.posetLeg (b.comp s) := by
  exact (h.simplexLeg_postcomp (SSet.yonedaEquiv.symm (orderSimplex s))
    (nerveMap b.monotone.functor)).trans
      (congrArg h.simplexLeg (SSet.yonedaEquiv_symm_comp _ _))

end Thomason.Construction.NormalizedSimplexIdentities

end

section

/-! # Functorial maps of categorified poset nerves -/

namespace Thomason.Construction

open CategoryTheory

/-- The monotone inclusion of a full subposet. -/
def subposetInclusion {E : Type} [PartialOrder E] (A : Set E) : A →o E where
  toFun := Subtype.val
  monotone' := fun _ _ h => h

namespace NormalizedSimplexIdentities

variable (h : NormalizedSimplexIdentities) [StrictColimitsInput]

noncomputable def posetMap {E F : Type} [PartialOrder E] [PartialOrder F] (f : E →o F) :
    h.categorification.obj (nerve E) ⟶ h.categorification.obj (nerve F) :=
  h.categorification.map (nerveMap f.monotone.functor)

theorem posetMap_id (E : Type) [PartialOrder E] :
    h.posetMap (OrderHom.id : E →o E) = 𝟙 (h.categorification.obj (nerve E)) := by
  have hn : nerveMap (OrderHom.id : E →o E).monotone.functor = 𝟙 (nerve E) := by
    apply NatTrans.ext
    funext m
    apply ConcreteCategory.hom_ext
    intro s
    exact nerve.ext_of_isThin rfl
  exact (congrArg h.categorification.map hn).trans (h.categorification.map_id _)

theorem posetMap_comp {E F H : Type} [PartialOrder E] [PartialOrder F] [PartialOrder H]
    (f : E →o F) (g : F →o H) :
    h.posetMap (g.comp f) = h.posetMap f ≫ h.posetMap g := by
  have hn : nerveMap (g.comp f).monotone.functor =
      nerveMap f.monotone.functor ≫ nerveMap g.monotone.functor := by
    apply NatTrans.ext
    funext m
    apply ConcreteCategory.hom_ext
    intro s
    exact nerve.ext_of_isThin rfl
  exact (congrArg h.categorification.map hn).trans (h.categorification.map_comp _ _)

end NormalizedSimplexIdentities
end Thomason.Construction

end

section

/-! # Compatible bounded cell families for strict limits

A compatible family is a strict cell when its dimensions have a common
finite bound. Cone maps automatically provide that bound. This is the
cell construction used for the finite limits in the model axioms.
-/

namespace Thomason.Construction.StrictOmegaCategory.LimitConstruction

open CategoryTheory CategoryTheory.Limits

variable {J : Type} [Category.{0} J] (F : J ⥤ StrictOmegaCategory.{0})

/-- Compatible diagram cells sharing a finite dimension bound. -/
structure Cell where
  val : ∀ j, F.obj j
  natural {i j : J} (f : i ⟶ j) : (F.map f).toFun (val i) = val j
  bounded : ∃ n, ∀ j, (F.obj j).DimensionLE n (val j)

namespace Cell

variable {F}

@[ext] theorem ext {x y : Cell F} (he : ∀ j, x.val j = y.val j) : x = y := by
  cases x
  cases y
  congr
  exact funext he

def face (a : Bool) (n : ℕ) (x : Cell F) : Cell F where
  val j := (F.obj j).face a n (x.val j)
  natural f := ((F.map f).map_face a n _).trans (congrArg ((F.obj _).face a n) (x.natural f))
  bounded := ⟨n, fun j => (F.obj j).face_dimensionLE a n _⟩

/-- Matching families can be composed componentwise. -/
def comp (n : ℕ) (x y : Cell F) (he : face true n x = face false n y) : Cell F where
  val j := (F.obj j).comp n (x.val j) (y.val j) (congrArg (fun z => z.val j) he)
  natural {i j} f := by
    have hi := congrArg (fun z => z.val i) he
    have hj := congrArg (fun z => z.val j) he
    have hn : (F.obj j).target n ((F.map f).toFun (x.val i)) =
        (F.obj j).source n ((F.map f).toFun (y.val i)) := by
      rw [x.natural f, y.natural f]
      exact hj
    change (F.map f).toFun ((F.obj i).comp n (x.val i) (y.val i) hi) = _
    rw [(F.map f).map_comp n _ _ hi hn]
    simp only [x.natural f, y.natural f]
  bounded := by
    obtain ⟨p, hp⟩ := x.bounded
    obtain ⟨q, hq⟩ := y.bounded
    refine ⟨max (n+1) (max p q), fun j => ?_⟩
    exact (F.obj j).dimensionLE_comp (by omega)
      ((F.obj j).dimensionLE_mono (by omega) (hp j))
      ((F.obj j).dimensionLE_mono (by omega) (hq j)) _

end Cell

/-- The compatible bounded families satisfy all strict laws componentwise. -/
def category : StrictOmegaCategory.{0} where
  Cell := Cell F
  face := Cell.face
  comp := Cell.comp
  globular a b m n x := by
    apply Cell.ext
    intro j
    have he := (F.obj j).globular a b m n (x.val j)
    split_ifs with hmn
    · exact he.trans (ite_eq_left hmn)
    · exact he.trans (ite_eq_right hmn)
  source_comp n x y he := by
    apply Cell.ext
    intro j
    exact (F.obj j).source_comp n (x.val j) (y.val j) _
  target_comp n x y he := by
    apply Cell.ext
    intro j
    exact (F.obj j).target_comp n (x.val j) (y.val j) _
  face_comp a m n hnm x y he he' := by
    apply Cell.ext
    intro j
    exact (F.obj j).face_comp a m n hnm (x.val j) (y.val j) _ _
  left_unit n x he := by
    apply Cell.ext
    intro j
    exact (F.obj j).left_unit n (x.val j) _
  right_unit n x he := by
    apply Cell.ext
    intro j
    exact (F.obj j).right_unit n (x.val j) _
  assoc n x y z hxy hyz hl hr := by
    apply Cell.ext
    intro j
    exact (F.obj j).assoc n (x.val j) (y.val j) (z.val j) _ _ _ _
  interchange m n hmn a b c d hab hcd hac hbd hl hr := by
    apply Cell.ext
    intro j
    exact (F.obj j).interchange m n hmn (a.val j) (b.val j) (c.val j) (d.val j) _ _ _ _ _ _
  finite_dimension x := by
    obtain ⟨n, hn⟩ := x.bounded
    exact ⟨n, Cell.ext (fun j => (hn j).1), Cell.ext (fun j => (hn j).2)⟩

end Thomason.Construction.StrictOmegaCategory.LimitConstruction

end

section

/-! # Constructing the finite strict limits required by the model axioms -/

namespace Thomason.Construction.StrictOmegaCategory.LimitConstruction

open CategoryTheory CategoryTheory.Limits

variable {J : Type} [Category.{0} J] (F : J ⥤ StrictOmegaCategory.{0})

/-- Projection to an original diagram component. -/
def projection (j : J) : category F ⟶ F.obj j where
  toFun x := x.val j
  map_face _ _ _ := rfl
  map_comp _ _ _ _ _ := rfl

/-- The bounded compatible families form a cone on the original diagram. -/
def cone : Cone F where
  pt := category F
  π :=
    { app := projection F
      naturality := by
        intro i j f
        apply Hom.ext
        funext x
        exact (x.natural f).symm }

/-- An original cone gives bounded families because each input cell has
one dimension bound preserved by all the projection functors. -/
def lift (s : Cone F) : s.pt ⟶ category F where
  toFun x :=
    { val j := (s.π.app j).toFun x
      natural f := (congrArg (fun k => k.toFun x) (s.π.naturality f)).symm
      bounded := by
        obtain ⟨n, hn⟩ := s.pt.finite_dimension x
        exact ⟨n, fun j => (s.π.app j).dimensionLE hn⟩ }
  map_face a n x := Cell.ext (fun j => (s.π.app j).map_face a n x)
  map_comp n x y he _ := Cell.ext (fun j => (s.π.app j).map_comp n x y he _)

/-- Its projections are exactly those of the given cone. -/
theorem lift_fac (s : Cone F) (j : J) : lift F s ≫ projection F j = s.π.app j := by
  apply Hom.ext
  rfl

/-- Every map is determined by its diagram projections. -/
theorem hom_ext {D : StrictOmegaCategory.{0}} (f g : D ⟶ category F)
    (he : ∀ j, f ≫ projection F j = g ≫ projection F j) : f = g := by
  apply Hom.ext
  funext x
  apply Cell.ext
  intro j
  exact congrArg (fun k => k.toFun x) (he j)

/-- This is the actual strict limit universal property. -/
def isLimit : IsLimit (cone F) where
  lift := lift F
  fac := lift_fac F
  uniq s m hm := hom_ext F m (lift F s) (fun j => (hm j).trans (lift_fac F s j).symm)

end Thomason.Construction.StrictOmegaCategory.LimitConstruction

namespace Thomason.Construction

open CategoryTheory CategoryTheory.Limits

/-- Strict omega-categories admit finite limits. -/
instance strictOmegaHasFiniteLimits : HasFiniteLimits StrictOmegaCategory.{0} where
  out _J _ _ :=
    { has_limit := fun F =>
        ⟨⟨⟨StrictOmegaCategory.LimitConstruction.cone F,
          StrictOmegaCategory.LimitConstruction.isLimit F⟩⟩⟩ }

end Thomason.Construction

end

section

/-! # Reversing every strict globular direction

The all-directions opposite is an involutive equivalence. It is used to
transport the already constructed source-fibre colimit calculations to
target fibres, which occur in the subdivided attachment comparisons.
-/

namespace Thomason.Construction.StrictOmegaCategory

open CategoryTheory

/-- Reverse both boundaries and the order of every strict composition. -/
def opposite (C : StrictOmegaCategory.{0}) : StrictOmegaCategory.{0} where
  Cell := C
  face a n x := C.face (!a) n x
  globular a b m n x := C.globular (!a) (!b) m n x
  comp n x y h := C.comp n y x h.symm
  source_comp n x y h := C.target_comp n y x h.symm
  target_comp n x y h := C.source_comp n y x h.symm
  face_comp a m n hnm x y h h' := C.face_comp (!a) m n hnm y x h.symm h'.symm
  left_unit n x h := C.right_unit n x h.symm
  right_unit n x h := C.left_unit n x h.symm
  assoc n x y z hxy hyz hl hr := (C.assoc n z y x hyz.symm hxy.symm hr.symm hl.symm).symm
  interchange m n hmn a b c d hab hcd hac hbd hl hr :=
    C.interchange m n hmn d c b a hcd.symm hab.symm hbd.symm hac.symm hl.symm hr.symm
  finite_dimension x := by
    obtain ⟨n, hs, ht⟩ := C.finite_dimension x
    exact ⟨n, ht, hs⟩

/-- Reversing all directions retains the underlying strict functor. -/
def oppositeMap {C D : StrictOmegaCategory.{0}} (f : C ⟶ D) : opposite C ⟶ opposite D where
  toFun := f.toFun
  map_face a n x := f.map_face (!a) n x
  map_comp n x y h h' := f.map_comp n y x h.symm h'.symm

/-- Opposite is functorial without a change of universe. -/
def oppositeFunctor : StrictOmegaCategory.{0} ⥤ StrictOmegaCategory.{0} where
  obj := opposite
  map := oppositeMap
  map_id C := by apply Hom.ext; rfl
  map_comp f g := by apply Hom.ext; rfl

/-- The double opposite has exactly the original strict cells. -/
def doubleOppositeIso (C : StrictOmegaCategory.{0}) : opposite (opposite C) ≅ C where
  hom := {
    toFun := id
    map_face a n x := by cases a <;> rfl
    map_comp n x y h h' := rfl }
  inv := {
    toFun := id
    map_face a n x := by cases a <;> rfl
    map_comp n x y h h' := rfl }
  hom_inv_id := by apply Hom.ext; rfl
  inv_hom_id := by apply Hom.ext; rfl

/-- Reversal is a genuine equivalence, allowing colimits to be transported. -/
def oppositeEquivalence : StrictOmegaCategory.{0} ≌ StrictOmegaCategory.{0} where
  functor := oppositeFunctor
  inverse := oppositeFunctor
  unitIso := NatIso.ofComponents (fun C => (doubleOppositeIso C).symm) (by
    intro C D f
    apply Hom.ext
    rfl)
  counitIso := NatIso.ofComponents doubleOppositeIso (by
    intro C D f
    apply Hom.ext
    rfl)
  functor_unitIso_comp C := by apply Hom.ext; rfl

end Thomason.Construction.StrictOmegaCategory

end

section

/-!
# Posets as strict omega-categories

An interval is the unique arrow between comparable vertices. Above degree
one only identity extensions remain. This supplies the actual ordered
label categories for sieve and cosieve fibers.
-/

namespace Thomason.Construction

open CategoryTheory

namespace StrictPoset

universe u v

structure Cell (E : Type u) [Preorder E] where
  first : E
  last : E
  ordered : first ≤ last

@[ext]
theorem Cell.ext {E : Type u} [Preorder E] {x y : Cell E}
    (hfirst : x.first = y.first) (hlast : x.last = y.last) : x = y := by
  cases x
  cases y
  cases hfirst
  cases hlast
  rfl

variable {E : Type u} [Preorder E]

def identity (e : E) : Cell E := ⟨e, e, le_rfl⟩

def face (a : Bool) : ℕ → Cell E → Cell E
  | 0, x => identity (if a then x.last else x.first)
  | _ + 1, x => x

theorem last_eq_first {x y : Cell E} (hxy : face true 0 x = face false 0 y) :
    x.last = y.first := congrArg Cell.first hxy

def comp : (n : ℕ) → (x y : Cell E) → (face true n x = face false n y) → Cell E
  | 0, x, y, hxy =>
    ⟨x.first, y.last, x.ordered.trans ((last_eq_first hxy).symm ▸ y.ordered)⟩
  | _ + 1, x, _, _ => x

/-- The strict omega-category associated to a poset, truncated in dimension one. -/
def category (E : Type u) [Preorder E] : StrictOmegaCategory.{u} where
  Cell := Cell E
  face := face
  globular a b m n x := by
    cases m <;> cases n <;> cases a <;> cases b <;> simp [face, identity]
  comp := comp
  source_comp n x y hxy := by cases n <;> rfl
  target_comp n x y hxy := by
    cases n with
    | zero => rfl
    | succ n => exact hxy
  face_comp a m n hnm x y hxy h' := by
    cases m with
    | zero => omega
    | succ m => rfl
  left_unit n x hxy := by
    cases n with
    | zero => apply Cell.ext <;> rfl
    | succ n => rfl
  right_unit n x hxy := by
    cases n with
    | zero => apply Cell.ext <;> rfl
    | succ n => rfl
  assoc n x y z hxy hyz hl hr := by
    cases n with
    | zero => apply Cell.ext <;> rfl
    | succ n => rfl
  interchange m n hmn a b c d hab hcd hac hbd hl hr := by
    cases n with
    | zero => omega
    | succ n => rfl
  finite_dimension x := ⟨1, rfl, rfl⟩

theorem category_isTruncated (E : Type u) [Preorder E] : (category E).IsTruncated 1 :=
  fun _ => ⟨rfl, rfl⟩

/-- A monotone map induces the unique functor on the associated thin categories. -/
def map {F : Type v} [Preorder F] (f : E →o F) : (category E).Hom (category F) where
  toFun x := ⟨f x.first, f x.last, f.monotone x.ordered⟩
  map_face a n x := by cases n <;> cases a <;> rfl
  map_comp n x y hxy h' := by cases n <;> rfl

@[simp]
theorem map_identity {F : Type v} [Preorder F] (f : E →o F) (e : E) :
    map f (identity e) = identity (f e) := rfl

theorem map_id : map (OrderHom.id : E →o E) = 𝟙 (category E) := by
  apply StrictOmegaCategory.Hom.ext
  funext x
  apply Cell.ext <;> rfl

theorem map_comp {F : Type u} [Preorder F] {H : Type u} [Preorder H]
    (f : E →o F) (g : F →o H) : map (g.comp f) = StrictOmegaCategory.Hom.comp (map f) (map g) := by
  apply StrictOmegaCategory.Hom.ext
  funext x
  rfl

end StrictPoset
end Thomason.Construction

end

section

/-!
# Full fibers of ordered labels

These are actual strict subcategories and functors out of the slice over
an ordered label category. No pushout-fiber assertion is assumed here.
-/

namespace Thomason.Construction

open CategoryTheory

namespace StrictOmegaCategory

variable {E : Type} [Preorder E] {C D : StrictOmegaCategory.{0}}

/-- The full subcategory on objects labelled by a fixed value. -/
def labelFiber (p : Hom C (StrictPoset.category E)) (e : E) : StrictOmegaCategory.{0} :=
  C.fullOn {x | p x = StrictPoset.identity e}

/-- The full object fiber is precisely the fiber on all strict cells. -/
theorem fullCell_label_iff (p : Hom C (StrictPoset.category E)) (e : E) (x : C) :
    C.FullCell {z | p z = StrictPoset.identity e} x ↔ p x = StrictPoset.identity e := by
  change (p (C.face false 0 x) = StrictPoset.identity e ∧
    p (C.face true 0 x) = StrictPoset.identity e) ↔ _
  constructor
  · rintro ⟨hs, ht⟩
    apply StrictPoset.Cell.ext
    · have he := congrArg (fun y : StrictPoset.Cell E => y.first)
        ((p.map_face false 0 x).symm.trans hs)
      exact he
    · have he := congrArg (fun y : StrictPoset.Cell E => y.last)
        ((p.map_face true 0 x).symm.trans ht)
      exact he
  · intro he
    constructor
    · exact (p.map_face false 0 x).trans
        ((congrArg ((StrictPoset.category E).face false 0) he).trans rfl)
    · exact (p.map_face true 0 x).trans
        ((congrArg ((StrictPoset.category E).face true 0) he).trans rfl)

/-- The inclusion of a label fiber in its ambient strict category. -/
def labelFiberInclusion (p : Hom C (StrictPoset.category E)) (e : E) : labelFiber p e ⟶ C :=
  C.fullInclusion {x | p x = StrictPoset.identity e}

instance labelFiberInclusion_mono (p : Hom C (StrictPoset.category E)) (e : E) :
    Mono (labelFiberInclusion p e) :=
  inferInstanceAs (Mono (C.fullInclusion {x | p x = StrictPoset.identity e}))

/-- Every functor over the ordered label restricts to every fiber. -/
def labelFiberMap (p : Hom C (StrictPoset.category E)) (q : Hom D (StrictPoset.category E))
    (e : E) (f : Hom C D) (hf : Hom.comp f q = p) : labelFiber p e ⟶ labelFiber q e :=
  C.fullMap {x | p x = StrictPoset.identity e} {x | q x = StrictPoset.identity e} f
    (fun x hx => (congrArg (fun k : Hom C (StrictPoset.category E) => k x) hf).trans hx)

/-- Fiber formation is functorial on the actual slice category. -/
def labelFiberFunctor (E : Type) [Preorder E] (e : E) :
    Over (StrictPoset.category E) ⥤ StrictOmegaCategory.{0} where
  obj X := labelFiber X.hom e
  map {X Y} f := labelFiberMap X.hom Y.hom e f.left (Over.w f)
  map_id X := by
    apply Hom.ext
    funext x
    rfl
  map_comp f g := by
    apply Hom.ext
    funext x
    rfl

/-- Fibers have no higher cells than the ambient category. -/
theorem labelFiber_isTruncated (p : Hom C (StrictPoset.category E)) (e : E)
    {n : ℕ} (hC : C.IsTruncated n) : (labelFiber p e).IsTruncated n :=
  C.fullOn_isTruncated _ hC

end StrictOmegaCategory
end Thomason.Construction

end

section

/-! # Full subcategories as actual Street subcomplexes

This identifies their Street nerves with explicit subcomplexes and proves
the intersection and pushout equations used for covers.
-/

namespace Thomason.Construction.NormalizedSimplexIdentities

open CategoryTheory CategoryTheory.Limits Opposite StrictOmegaCategory

variable (h : NormalizedSimplexIdentities) (C : StrictOmegaCategory.{0})

/-- A simplex is in the full subcomplex when all its cells are in the full subcategory. -/
def fullStreetSubcomplex (S : Set C) : (h.streetNerve.obj C).Subcomplex where
  obj _ := {f | ∀ x, C.FullCell S (f.toFun x)}
  map g _f hf x := hf ((h.cosimplicial.map g.unop).toFun x)

/-- Lift a simplex all of whose cells belong to a full subcategory. -/
def liftFullSimplex (S : Set C) {m : SimplexCategory}
    (f : h.object m.len ⟶ C) (hf : ∀ x, C.FullCell S (f.toFun x)) :
    h.object m.len ⟶ C.fullOn S where
  toFun x := ⟨f.toFun x, hf x⟩
  map_face a n x := Subtype.ext (f.map_face a n x)
  map_comp n x y hxy _h' := Subtype.ext (f.map_comp n x y hxy _)

/-- The full subcomplex is exactly the image of the original full inclusion. -/
theorem fullStreetSubcomplex_eq_range (S : Set C) :
    h.fullStreetSubcomplex C S =
      SSet.Subcomplex.range (h.streetNerve.map (C.fullInclusion S)) := by
  ext m f
  constructor
  · intro hf
    exact ⟨h.liftFullSimplex C S f hf, rfl⟩
  · rintro ⟨f, rfl⟩ x
    exact (f.toFun x).property

/-- Full inclusions are injective on every Street simplex. -/
instance streetNerve_fullInclusion_mono (S : Set C) :
    Mono (h.streetNerve.map (C.fullInclusion S)) := by
  rw [NatTrans.mono_iff_mono_app]
  intro m
  apply (CategoryTheory.mono_iff_injective _).mpr
  intro f g he
  apply StrictOmegaCategory.Hom.ext
  funext x
  apply Subtype.ext
  exact congrArg (fun k : h.object m.unop.len ⟶ C => k.toFun x) he

instance streetNerve_labelFiberInclusion_mono
    (p : C ⟶ StrictPoset.category (Fin 2)) (e : Fin 2) :
    Mono (h.streetNerve.map (labelFiberInclusion p e)) :=
  inferInstanceAs (Mono (h.streetNerve.map (C.fullInclusion {x | p.toFun x = StrictPoset.identity e})))

/-- The nerve of a full subcategory is isomorphic to this actual subcomplex. -/
noncomputable def fullStreetIso (S : Set C) :
    h.streetNerve.obj (C.fullOn S) ≅ (h.fullStreetSubcomplex C S).toSSet :=
  asIso (SSet.Subcomplex.toRange (h.streetNerve.map (C.fullInclusion S))) ≪≫
    (SSet.Subcomplex.eqToIso (h.fullStreetSubcomplex_eq_range C S)).symm

/-- This isomorphism commutes with the original inclusion, without changing its image. -/
theorem fullStreetIso_hom_ι (S : Set C) :
    (h.fullStreetIso C S).hom ≫ (h.fullStreetSubcomplex C S).ι =
      h.streetNerve.map (C.fullInclusion S) := by
  simp [fullStreetIso]

/-- Intersections of full subcategories are computed on the actual Street subcomplexes. -/
theorem fullStreetSubcomplex_inter (S T : Set C) :
    h.fullStreetSubcomplex C (S ∩ T) =
      h.fullStreetSubcomplex C S ⊓ h.fullStreetSubcomplex C T := by
  ext m f
  constructor
  · intro hf
    exact ⟨fun x => ⟨(hf x).1.1, (hf x).2.1⟩,
      fun x => ⟨(hf x).1.2, (hf x).2.2⟩⟩
  · rintro ⟨hs, ht⟩ x
    exact ⟨⟨(hs x).1, (ht x).1⟩, ⟨(hs x).2, (ht x).2⟩⟩

/-- A cover by full Street subcomplexes gives its genuine simplicial pushout. -/
theorem fullStreetSubcomplex_isPushout (S T : Set C)
    (hc : h.fullStreetSubcomplex C S ⊔ h.fullStreetSubcomplex C T = ⊤) :
    IsPushout
      (SSet.Subcomplex.homOfLE (show h.fullStreetSubcomplex C (S ∩ T) ≤
        h.fullStreetSubcomplex C S from fun _ _ hf x => ⟨(hf x).1.1, (hf x).2.1⟩))
      (SSet.Subcomplex.homOfLE (show h.fullStreetSubcomplex C (S ∩ T) ≤
        h.fullStreetSubcomplex C T from fun _ _ hf x => ⟨(hf x).1.2, (hf x).2.2⟩))
      (h.fullStreetSubcomplex C S).ι (h.fullStreetSubcomplex C T).ι := by
  have sq : SSet.Subcomplex.BicartSq (h.fullStreetSubcomplex C (S ∩ T))
      (h.fullStreetSubcomplex C S) (h.fullStreetSubcomplex C T) ⊤ :=
    ⟨hc, (h.fullStreetSubcomplex_inter C S T).symm⟩
  exact sq.isPushout.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (SSet.Subcomplex.topIso (h.streetNerve.obj C))
    (by simp) (by simp) (by simp) (by simp)

end Thomason.Construction.NormalizedSimplexIdentities

end

section

/-!
# The ordinary category of objects and 1-cells

This constructs, from the actual globular operations, the ordinary category
underlying a strict omega-category. The proof checks that composition of
1-cells remains 1-dimensional, and that strict functors induce functors.
-/

namespace Thomason.Construction.StrictOmegaCategory

open CategoryTheory

universe u

def Objects (C : StrictOmegaCategory.{u}) := {x : C // C.DimensionLE 0 x}

def OneArrow {C : StrictOmegaCategory} (a b : Objects C) :=
  {x : C // C.DimensionLE 1 x ∧ C.source 0 x = a.val ∧ C.target 0 x = b.val}

namespace OneArrow

def id {C : StrictOmegaCategory} (a : Objects C) : OneArrow a a :=
  ⟨a.val, C.dimensionLE_mono (by decide : 0 ≤ 1) a.property,
    a.property.1, a.property.2⟩

def comp {C : StrictOmegaCategory} {a b c : Objects C}
    (f : OneArrow a b) (g : OneArrow b c) : OneArrow a c :=
  let h := f.property.2.2.trans g.property.2.1.symm
  ⟨C.comp 0 f.val g.val h,
    C.dimensionLE_comp (by decide : 0 < 1) f.property.1 g.property.1 h,
    (C.source_comp 0 f.val g.val h).trans f.property.2.1,
    (C.target_comp 0 f.val g.val h).trans g.property.2.2⟩

theorem id_comp {C : StrictOmegaCategory} {a b : Objects C} (f : OneArrow a b) :
    comp (id a) f = f := by
  apply Subtype.ext
  change C.comp 0 a.val f.val _ = f.val
  have ha : C.face false 0 f.val = a.val := f.property.2.1
  have hu := C.left_unit 0 f.val (C.face_face_same true false 0 f.val)
  simpa only [ha] using hu

theorem comp_id {C : StrictOmegaCategory} {a b : Objects C} (f : OneArrow a b) :
    comp f (id b) = f := by
  apply Subtype.ext
  change C.comp 0 f.val b.val _ = f.val
  have hb : C.face true 0 f.val = b.val := f.property.2.2
  have hu := C.right_unit 0 f.val (C.face_face_same false true 0 f.val).symm
  simpa only [hb] using hu

theorem assoc {C : StrictOmegaCategory} {a b c d : Objects C}
    (f : OneArrow a b) (g : OneArrow b c) (h : OneArrow c d) :
    comp (comp f g) h = comp f (comp g h) := by
  apply Subtype.ext
  exact C.assoc 0 f.val g.val h.val _ _ _ _

end OneArrow

instance (C : StrictOmegaCategory) : Category (Objects C) where
  Hom := OneArrow
  id := OneArrow.id
  comp := OneArrow.comp
  id_comp := OneArrow.id_comp
  comp_id := OneArrow.comp_id
  assoc := OneArrow.assoc

/-- The object and 1-cell action of a strict functor is an ordinary functor. -/
def Hom.toOneFunctor {C D : StrictOmegaCategory} (f : Hom C D) : Objects C ⥤ Objects D where
  obj a := ⟨f a.val, f.dimensionLE a.property⟩
  map {a b} g :=
    ⟨f g.val, f.dimensionLE g.property.1,
      (f.map_face false 0 g.val).symm.trans (congrArg f.toFun g.property.2.1),
      (f.map_face true 0 g.val).symm.trans (congrArg f.toFun g.property.2.2)⟩
  map_id _ := rfl
  map_comp g h := by
    apply Subtype.ext
    exact f.map_comp 0 g.val h.val _ _

/-- Recovering objects and 1-cells is functorial in strict omega-categories. -/
def underlyingCategory : StrictOmegaCategory.{u} ⥤ Cat.{u, u} where
  obj C := Cat.of (Objects C)
  map f := f.toOneFunctor.toCatHom
  map_id _ := rfl
  map_comp _ _ := rfl

end Thomason.Construction.StrictOmegaCategory

end

end OAI
