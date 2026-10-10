import OAI.CategoryTheory.Thomason.SubdivisionMaps
import Mathlib.AlgebraicTopology.SimplexCategory.SemiSimplexCategory
import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
import Mathlib.AlgebraicTopology.SimplicialSet.Nonsingular
import Mathlib.AlgebraicTopology.SimplicialSet.SubcomplexColimits
import Mathlib.AlgebraicTopology.SimplicialSet.Subdivision
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Category.Cat.Op
import Mathlib.CategoryTheory.Elements
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import Mathlib.CategoryTheory.Limits.Types.Coproducts
import Mathlib.CategoryTheory.Whiskering
import Mathlib.Data.Finset.Max
import Mathlib.Order.UpperLower.Basic

namespace OAI

section

/-! # Canonical coproduct cocones for arbitrary discrete diagrams -/

namespace Thomason.Construction

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u v

variable {C : Type u} [Category.{v} C] {α : Type} (F : Discrete α ⥤ C)
  [HasCoproduct (fun a => F.obj ⟨a⟩)]

/-- The chosen coproduct also presents a discrete diagram not syntactically
written as `Discrete.functor`. -/
def discreteCoproductCocone : Cocone F where
  pt := ∐ fun a => F.obj ⟨a⟩
  ι := Discrete.natTrans (fun a => Sigma.ι (fun a => F.obj ⟨a⟩) a.as)

/-- Its universal property follows directly from the coproduct universal property. -/
def discreteCoproductIsColimit : IsColimit (discreteCoproductCocone F) where
  desc c := Sigma.desc (fun a => c.ι.app ⟨a⟩)
  fac c a := Sigma.ι_comp_desc _ a.as
  uniq c m hm := by
    apply Sigma.hom_ext
    intro a
    exact (hm ⟨a⟩).trans (Sigma.ι_comp_desc (fun a => c.ι.app ⟨a⟩) a).symm

/-- Comparison from the chosen coproduct to any colimit of the same diagram. -/
def discreteCoproductIso {c : Cocone F} (hc : IsColimit c) :
    (∐ fun a => F.obj ⟨a⟩) ≅ c.pt :=
  (discreteCoproductIsColimit F).coconePointUniqueUpToIso hc

@[reassoc]
theorem discreteCoproductIso_fac {c : Cocone F} (hc : IsColimit c) (a : α) :
    Sigma.ι (fun a => F.obj ⟨a⟩) a ≫ (discreteCoproductIso F hc).hom = c.ι.app ⟨a⟩ :=
  (discreteCoproductIsColimit F).comp_coconePointUniqueUpToIso_hom hc ⟨a⟩

end

end Thomason.Construction

end

section

/-!
# The last-vertex map for simplicial subdivision

The map sends a nonempty finite chain of vertices to its greatest vertex,
then extends the resulting map of cosimplicial objects by the defining
left Kan extension of `SSet.sd`.
-/

open CategoryTheory

namespace Thomason.Construction

universe u

open PartialOrder

/-- The greatest vertex of a finite nonempty chain in a linear order. -/
noncomputable def chainMaximum {X : Type*} [LinearOrder X]
    (A : NonemptyFiniteChains X) : X := A.finset.max' A.nonempty

theorem chainMaximum_monotone {X : Type*} [LinearOrder X] :
    Monotone (chainMaximum (X := X)) := by
  intro A B h
  apply Finset.max'_le
  intro x hx
  exact Finset.le_max' _ _ (h hx)

/-- The finite maximum agrees with the greatest element of the chain. -/
theorem chainMaximum_eq_chainGreatest {X : Type*} [LinearOrder X]
    (A : NonemptyFiniteChains X) :
    chainMaximum A = Thomason.Subdivision.chainGreatest A := by
  apply le_antisymm
  · apply Finset.max'_le
    intro x hx
    exact Thomason.Subdivision.le_chainGreatest A hx
  · exact Finset.le_max' _ _ (Thomason.Subdivision.chainGreatest_mem A)

/-- Greatest vertex as an order-preserving map. -/
noncomputable def chainMaximumHom {X : Type*} [LinearOrder X] :
    NonemptyFiniteChains X →o X :=
  ⟨chainMaximum, chainMaximum_monotone⟩

/-- Monotone maps commute with the greatest-vertex operation. -/
theorem chainMaximum_map {X Y : Type*} [LinearOrder X] [LinearOrder Y]
    (f : X →o Y) (A : NonemptyFiniteChains X) :
    chainMaximum (A.map f) = f (chainMaximum A) := by
  apply le_antisymm
  · apply Finset.max'_le
    intro y hy
    obtain ⟨x, hx, rfl⟩ := (NonemptyFiniteChains.mem_map_iff A f y).mp hy
    exact f.monotone (Finset.le_max' _ _ hx)
  · apply Finset.le_max'
    exact (NonemptyFiniteChains.mem_map_iff A f _).mpr
      ⟨_, Finset.max'_mem A.finset A.nonempty, rfl⟩

/-- Greatest vertex as a natural transformation on the finite ordered sets
indexing simplicial sets. -/
noncomputable def simplexChainMaximum :
    (SimplexCategory.toPartOrd.{u} ⋙ PartOrd.nonemptyFiniteChainsFunctor) ⟶
      SimplexCategory.toPartOrd.{u} where
  app n := PartOrd.ofHom (chainMaximumHom (X := ULift.{u} (Fin (n.len + 1))))
  naturality n m f := by
    apply PartOrd.ext
    intro A
    let F : ULift.{u} (Fin (n.len + 1)) →o ULift.{u} (Fin (m.len + 1)) :=
      { toFun x := ULift.up (f.toOrderHom x.down)
        monotone' := fun _ _ h => f.toOrderHom.monotone h }
    exact chainMaximum_map F A

/-- The simplex maximum is the restriction of the greatest-chain transformation. -/
theorem simplexChainMaximum_eq :
    simplexChainMaximum.{u} = Functor.whiskerLeft SimplexCategory.toPartOrd
      Thomason.Subdivision.chainLastNat := by
  apply NatTrans.ext
  funext n
  apply PartOrd.ext
  intro A
  exact chainMaximum_eq_chainGreatest (X := ULift.{u} (Fin (n.len + 1))) A

/-- The standard cosimplicial simplex is the nerve of its ordered vertex set. -/
def simplexNerveIso :
    SSet.stdSimplex.{u} ≅ SimplexCategory.toPartOrd.{u} ⋙ PartOrd.nerveFunctor :=
  NatIso.ofComponents (fun n => SSet.stdSimplex.isoNerve n.len) (by
    intro n m f
    ext d x
    rfl)

/-- The last-vertex map on the subdivisions of the standard simplices. -/
noncomputable def simplexLastVertex : SimplexCategory.sd.{u} ⟶ SSet.stdSimplex.{u} :=
  Functor.whiskerRight simplexChainMaximum PartOrd.nerveFunctor ≫ simplexNerveIso.inv

/-- The simplex comparison agrees with the greatest-chain construction. -/
theorem simplexLastVertex_eq :
    simplexLastVertex.{u} = Thomason.Subdivision.simplexLastVertex := by
  unfold simplexLastVertex Thomason.Subdivision.simplexLastVertex
  rw [simplexChainMaximum_eq]
  rfl

/-- The last-vertex map `Sd K ⟶ K`, defined for every simplicial set. -/
noncomputable def lastVertex : SSet.sd.{u} ⟶ 𝟭 SSet.{u} :=
  SSet.sd.descOfIsLeftKanExtension SSet.stdSimplex.sdIso.inv (𝟭 _) simplexLastVertex

/-- Both greatest-vertex constructions extend to the same subdivision map. -/
theorem lastVertex_eq : lastVertex.{u} = Thomason.Subdivision.lastVertex := by
  unfold lastVertex Thomason.Subdivision.lastVertex
  rw [simplexLastVertex_eq]

/-- On a standard simplex the last-vertex map is induced by greatest vertex. -/
theorem lastVertex_on_standard_simplex (n : SimplexCategory) :
    SSet.stdSimplex.sdIso.inv.app n ≫ lastVertex.app (SSet.stdSimplex.obj n) =
      simplexLastVertex.app n :=
  SSet.sd.descOfIsLeftKanExtension_fac_app SSet.stdSimplex.sdIso.inv
    (𝟭 _) simplexLastVertex n

end Thomason.Construction

end

section

/-! # The face-simplex resolution of an arbitrary simplicial set

All simplices, including degenerate ones, are retained as objects. Only
injective ordinal operators are morphisms. This keeps repeated face
occurrences while giving a category directed by simplex dimension.
-/

namespace Thomason.Construction.FaceSimplexResolution

open CategoryTheory Opposite
open scoped Simplicial

noncomputable section

def restriction : SSet.{0} ⥤ (SemiSimplexCategoryᵒᵖ ⥤ Type) :=
  (Functor.whiskeringLeft SemiSimplexCategoryᵒᵖ SimplexCategoryᵒᵖ (Type)).obj
    SemiSimplexCategory.toSimplexCategory.op

abbrev Face (X : SSet.{0}) := ((restriction.obj X).Elements)ᵒᵖ

def projection (X : SSet.{0}) : Face X ⥤ SimplexCategory :=
  (Functor.Elements.π (restriction.obj X)).leftOp ⋙ SemiSimplexCategory.toSimplexCategory

def functor : SSet.{0} ⥤ SSet.{0} :=
  restriction ⋙ Functor.elementsFunctor ⋙ Cat.opFunctor ⋙ nerveFunctor

def cell {X : SSet.{0}} (a : Face X) : X.obj (.op ((projection X).obj a)) := a.unop.val

theorem cell_map {X : SSet.{0}} {a b : Face X} (f : a ⟶ b) :
    X.map ((projection X).map f).op (cell b) = cell a := f.unop.map_val

instance {X : SSet.{0}} {a b : Face X} (f : a ⟶ b) :
    Mono ((projection X).map f) := by
  change Mono (SemiSimplexCategory.toSimplexCategory.map f.unop.hom.unop)
  infer_instance

def vertex {X : SSet.{0}} {n : SimplexCategory}
    (s : (nerve (Face X)).obj (.op n)) (i : Fin (n.len+1)) :
    Fin (((projection X).obj (s.obj (Fin.last n.len))).len+1) :=
  ((projection X).map (s.map (homOfLE (Fin.le_last i)))).toOrderHom
    (Fin.last ((projection X).obj (s.obj i)).len)

theorem vertex_monotone {X : SSet.{0}} {n : SimplexCategory}
    (s : (nerve (Face X)).obj (.op n)) : Monotone (vertex s) := by
  intro i j hij
  let d := s ⋙ projection X
  have he : d.map (homOfLE hij) ≫ d.map (homOfLE (Fin.le_last j)) =
      d.map (homOfLE (Fin.le_last i)) := by
    rw [← Functor.map_comp]
    rfl
  have hv := congrArg (fun f => f.toOrderHom (Fin.last ((projection X).obj (s.obj i)).len)) he
  change (d.map (homOfLE (Fin.le_last j))).toOrderHom
    ((d.map (homOfLE hij)).toOrderHom (Fin.last ((projection X).obj (s.obj i)).len)) =
      vertex s i at hv
  rw [← hv]
  exact (d.map (homOfLE (Fin.le_last j))).toOrderHom.monotone (Fin.le_last _)

def ordinal {X : SSet.{0}} {n : SimplexCategory}
    (s : (nerve (Face X)).obj (.op n)) :
    n ⟶ (projection X).obj (s.obj (Fin.last n.len)) :=
  SimplexCategory.Hom.mk ⟨vertex s, vertex_monotone s⟩

def simplex {X : SSet.{0}} {n : SimplexCategory}
    (s : (nerve (Face X)).obj (.op n)) : X.obj (.op n) :=
  X.map (ordinal s).op (cell (s.obj (Fin.last n.len)))

theorem ordinal_naturality {X : SSet.{0}} {m n : SimplexCategory} (a : m ⟶ n)
    (s : (nerve (Face X)).obj (.op n)) :
    a ≫ ordinal s = ordinal ((nerve (Face X)).map a.op s) ≫
      (projection X).map (s.map (homOfLE (Fin.le_last (a.toOrderHom (Fin.last m.len))))) := by
  apply SimplexCategory.Hom.ext
  apply DFunLike.ext
  intro i
  let d := s ⋙ projection X
  have he : d.map (homOfLE (a.toOrderHom.monotone (Fin.le_last i))) ≫
      d.map (homOfLE (Fin.le_last (a.toOrderHom (Fin.last m.len)))) =
        d.map (homOfLE (Fin.le_last (a.toOrderHom i))) := by
    rw [← Functor.map_comp]
    rfl
  exact (congrArg (fun f => f.toOrderHom
    (Fin.last ((projection X).obj (s.obj (a.toOrderHom i))).len)) he).symm

theorem simplex_naturality {X : SSet.{0}} {m n : SimplexCategory} (a : m ⟶ n)
    (s : (nerve (Face X)).obj (.op n)) :
    X.map a.op (simplex s) = simplex ((nerve (Face X)).map a.op s) := by
  unfold simplex
  rw [← Functor.map_comp_apply, ← op_comp, ordinal_naturality, op_comp,
    Functor.map_comp_apply]
  exact congrArg (X.map (ordinal ((nerve (Face X)).map a.op s)).op)
    (cell_map (s.map (homOfLE (Fin.le_last (a.toOrderHom (Fin.last m.len))))))

def augmentation (X : SSet.{0}) : functor.obj X ⟶ X where
  app d := ↾fun s => simplex s
  naturality _ _ a := by
    apply ConcreteCategory.hom_ext
    intro s
    exact (simplex_naturality a.unop s).symm

/-- The augmentation has the original simplicial set as its natural codomain. -/
theorem augmentation_naturality {X Y : SSet.{0}} (f : X ⟶ Y) :
    functor.map f ≫ augmentation Y = augmentation X ≫ f := by
  apply NatTrans.ext
  funext d
  apply ConcreteCategory.hom_ext
  intro s
  change Y.map (ordinal s).op (f.app _ (cell (s.obj (Fin.last d.unop.len)))) =
    f.app _ (X.map (ordinal s).op (cell (s.obj (Fin.last d.unop.len))))
  exact (f.naturality_apply (ordinal s).op _).symm

def augmentationNatTrans : functor ⟶ 𝟭 SSet.{0} where
  app := augmentation
  naturality _ _ f := augmentation_naturality f

end

end Thomason.Construction.FaceSimplexResolution

end

section

/-! # A face-resolution simplex is an ordinal shape and one final simplex

The face operators determine all earlier simplices from the last one.
This description retains repeated and degenerate simplices and is natural
in the original simplicial set.
-/

namespace Thomason.Construction.FaceSimplexResolution

open CategoryTheory Opposite
open scoped Simplicial

noncomputable section

def semiProjection (X : SSet.{0}) : Face X ⥤ SemiSimplexCategory :=
  (Functor.Elements.π (restriction.obj X)).leftOp

instance (X : SSet.{0}) : (semiProjection X).Faithful where
  map_injective h := by
    apply Quiver.Hom.unop_inj
    apply Functor.Elements.hom_ext
    exact congrArg Quiver.Hom.op h

abbrev Shape (n : ℕ) := Fin (n+1) ⥤ SemiSimplexCategory

def ofShape {X : SSet.{0}} {n : ℕ} (s : Shape n)
    (x : X.obj (.op (SemiSimplexCategory.toSimplexCategory.obj
      (s.obj (Fin.last n))))) : (nerve (Face X)) _⦋n⦌ where
  obj i := .op
    { obj := .op (s.obj i)
      val := X.map (SemiSimplexCategory.toSimplexCategory.map
        (s.map (homOfLE (Fin.le_last i)))).op x }
  map {i j} f := Quiver.Hom.op
    { hom := (s.map f).op
      map_val := by
        change X.map (SemiSimplexCategory.toSimplexCategory.map (s.map f)).op
          (X.map (SemiSimplexCategory.toSimplexCategory.map
            (s.map (homOfLE (Fin.le_last j)))).op x) = _
        rw [← Functor.map_comp_apply, ← op_comp, ← Functor.map_comp, ← Functor.map_comp]
        rfl }
  map_id i := by
    apply Quiver.Hom.unop_inj
    apply Functor.Elements.hom_ext
    change (s.map (𝟙 i)).op = (𝟙 (s.obj i)).op
    rw [s.map_id]
  map_comp f g := by
    apply Quiver.Hom.unop_inj
    apply Functor.Elements.hom_ext
    change (s.map (f ≫ g)).op = (s.map f ≫ s.map g).op
    rw [s.map_comp]

theorem ofShape_projection {X : SSet.{0}} {n : ℕ} (s : Shape n) (x) :
    ofShape (X := X) s x ⋙ semiProjection X = s := rfl

theorem ofShape_cell {X : SSet.{0}} {n : ℕ} (s : Shape n) (x) :
    cell ((ofShape (X := X) s x).obj (Fin.last n)) = x := by
  change X.map (SemiSimplexCategory.toSimplexCategory.map
    (s.map (homOfLE (Fin.le_last (Fin.last n))))).op x = x
  have he : homOfLE (Fin.le_last (Fin.last n)) = 𝟙 (Fin.last n) := rfl
  rw [he, s.map_id, SemiSimplexCategory.toSimplexCategory.map_id, op_id, X.map_id]
  rfl

theorem ofShape_reconstruct {X : SSet.{0}} {n : ℕ}
    (s : (nerve (Face X)) _⦋n⦌) :
    ofShape (s ⋙ semiProjection X) (cell (s.obj (Fin.last n))) = s := by
  refine CategoryTheory.Functor.ext (fun i => ?_) (fun i j f => ?_)
  ·
    apply unop_injective
    refine Functor.Elements.ext (F := restriction.obj X)
      ((ofShape (s ⋙ semiProjection X) (cell (s.obj (Fin.last n)))).obj i).unop
      (s.obj i).unop rfl ?_
    change (restriction.obj X).map (𝟙 _) _ = _
    rw [(restriction.obj X).map_id]
    exact cell_map (s.map (homOfLE (Fin.le_last i)))
  ·
    apply (semiProjection X).map_injective
    simp only [CategoryTheory.Functor.map_comp, CategoryTheory.eqToHom_map]
    change (s ⋙ semiProjection X).map f =
      (𝟙 _) ≫ (s ⋙ semiProjection X).map f ≫ (𝟙 _)
    simp only [Category.id_comp, Category.comp_id]

/-- In each degree the resolution is a disjoint union of evaluations of `X`. -/
def shapeEquiv (X : SSet.{0}) (n : ℕ) :
    (functor.obj X) _⦋n⦌ ≃
      Σ s : Shape n, X.obj (.op (SemiSimplexCategory.toSimplexCategory.obj
        (s.obj (Fin.last n)))) where
  toFun s := ⟨s ⋙ semiProjection X, cell (s.obj (Fin.last n))⟩
  invFun p := ofShape p.1 p.2
  left_inv := ofShape_reconstruct
  right_inv := by
    rintro ⟨s, x⟩
    exact Sigma.ext rfl (heq_of_eq (ofShape_cell s x))

/-- The shape is unchanged by a map of simplicial sets; only the final
simplex is mapped. -/
theorem shapeEquiv_naturality {X Y : SSet.{0}} (f : X ⟶ Y) (n : ℕ)
    (s : (functor.obj X) _⦋n⦌) :
    shapeEquiv Y n ((functor.map f).app _ s) =
      ⟨(shapeEquiv X n s).1, f.app _ (shapeEquiv X n s).2⟩ := rfl

theorem ofShape_naturality {X Y : SSet.{0}} (f : X ⟶ Y) {n : ℕ}
    (s : Shape n) (x : X.obj (.op (SemiSimplexCategory.toSimplexCategory.obj
      (s.obj (Fin.last n))))) :
    (functor.map f).app _ (ofShape s x) = ofShape s (f.app _ x) := by
  apply (shapeEquiv Y n).injective
  change shapeEquiv Y n ((functor.map f).app _ ((shapeEquiv X n).symm ⟨s, x⟩)) =
    shapeEquiv Y n ((shapeEquiv Y n).symm ⟨s, f.app _ x⟩)
  rw [shapeEquiv_naturality, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

instance map_mono {X Y : SSet.{0}} (f : X ⟶ Y) [Mono f] : Mono (functor.map f) := by
  rw [NatTrans.mono_iff_mono_app]
  rintro ⟨⟨n⟩⟩
  rw [mono_iff_injective]
  intro s t h
  apply (shapeEquiv X n).injective
  have he := congrArg (shapeEquiv Y n) h
  rw [shapeEquiv_naturality, shapeEquiv_naturality] at he
  generalize hs : shapeEquiv X n s = a at *
  generalize ht : shapeEquiv X n t = b at *
  obtain ⟨ss, x⟩ := a
  obtain ⟨tt, y⟩ := b
  have hshape := congrArg Sigma.fst he
  change ss = tt at hshape
  subst tt
  have hx := eq_of_heq (Sigma.mk.inj_iff.mp he).2
  exact congrArg (Sigma.mk ss) (injective_of_mono (f.app _) hx)

end

end Thomason.Construction.FaceSimplexResolution

end

section

/-! # The face-simplex resolution preserves colimits

In a fixed degree it is the coproduct, over ordinal shapes, of evaluation
functors. Thus it preserves the actual cell-attachment pushouts.
-/

namespace Thomason.Construction.FaceSimplexResolution

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

noncomputable section

abbrev shapeEvaluation (n : ℕ) (s : Shape n) : SSet.{0} ⥤ Type :=
  SSet.evaluation.obj (.op (SemiSimplexCategory.toSimplexCategory.obj
    (s.obj (Fin.last n))))

instance (n : ℕ) (s : Shape n) : PreservesColimits (shapeEvaluation n s) := by
  unfold shapeEvaluation
  infer_instance

def shapeDiagram (n : ℕ) : SSet.{0} ⥤ (Discrete (Shape n) ⥤ Type) where
  obj X := Discrete.functor (fun s => (shapeEvaluation n s).obj X)
  map f := Discrete.natTrans (fun s => (shapeEvaluation n s.as).map f)

instance (n : ℕ) : PreservesColimits (shapeDiagram n) :=
  preservesColimits_of_evaluation _ (fun s =>
    preservesColimits_of_natIso
      (show shapeEvaluation n s.as ≅ shapeDiagram n ⋙
        (evaluation (Discrete (Shape n)) (Type)).obj s from Iso.refl _))

def degreeCoproductIso (n : ℕ) :
    shapeDiagram n ⋙ colim ≅ functor ⋙ SSet.evaluation.obj (.op ⦋n⦌) :=
  NatIso.ofComponents
    (fun X => Types.coproductIso (fun s => (shapeEvaluation n s).obj X) ≪≫
      (shapeEquiv X n).symm.toIso)
    (by
      intro X Y f
      apply Sigma.hom_ext
      intro s
      change colimit.ι ((shapeDiagram n).obj X) ⟨s⟩ ≫
        ((colim.map ((shapeDiagram n).map f)) ≫
        (Types.coproductIso (fun s => (shapeEvaluation n s).obj Y)).hom ≫
        (shapeEquiv Y n).symm.toIso.hom) = _
      rw [colimit.ι_map_assoc]
      change f.app _ ≫
        (Sigma.ι (fun s => (shapeEvaluation n s).obj Y) s ≫
          (Types.coproductIso (fun s => (shapeEvaluation n s).obj Y)).hom ≫
            (shapeEquiv Y n).symm.toIso.hom) =
        Sigma.ι (fun s => (shapeEvaluation n s).obj X) s ≫
          ((Types.coproductIso (fun s => (shapeEvaluation n s).obj X)).hom ≫
            (shapeEquiv X n).symm.toIso.hom ≫ (functor.map f).app _)
      rw [← Category.assoc (Sigma.ι (fun s => (shapeEvaluation n s).obj Y) s),
        Types.coproductIso_ι_comp_hom,
        ← Category.assoc (Sigma.ι (fun s => (shapeEvaluation n s).obj X) s),
        Types.coproductIso_ι_comp_hom]
      apply ConcreteCategory.hom_ext
      intro x
      change ofShape s (f.app _ x) = (functor.map f).app _ (ofShape s x)
      exact (ofShape_naturality f s x).symm)

instance : PreservesColimits functor := by
  apply preservesColimits_of_evaluation
  rintro ⟨⟨n⟩⟩
  exact preservesColimits_of_natIso (degreeCoproductIso n)

end

end Thomason.Construction.FaceSimplexResolution

end

section

/-! # The face-simplex resolution is nonsingular

Dimension strictly increases along each nonidentity face arrow. Repeated
dimensions in a nerve flag therefore give an actual simplicial degeneracy.
-/

namespace Thomason.Construction.FaceSimplexResolution

open CategoryTheory Opposite
open scoped Simplicial

noncomputable section

def dimension {X : SSet.{0}} (a : Face X) : ℕ := ((projection X).obj a).len

theorem dimension_le {X : SSet.{0}} {a b : Face X} (f : a ⟶ b) :
    dimension a ≤ dimension b := SimplexCategory.len_le_of_mono ((projection X).map f)

private theorem simplex_mono_eqToHom {a b : SimplexCategory} (f : a ⟶ b) [Mono f]
    (h : a = b) : f = eqToHom h := by
  subst b
  exact SimplexCategory.eq_id_of_mono f

theorem face_eq_of_dimension_eq {X : SSet.{0}} {a b : Face X} (f : a ⟶ b)
    (h : dimension a = dimension b) : a = b := by
  have hb : a.unop.obj = b.unop.obj := by
    apply unop_injective
    apply SemiSimplexCategory.ext
    exact h
  have hf : f.unop.hom = eqToHom hb.symm := by
    apply Quiver.Hom.unop_inj
    apply SemiSimplexCategory.toSimplexCategory.map_injective
    rw [eqToHom_unop, eqToHom_map]
    exact simplex_mono_eqToHom _ _
  apply unop_injective
  symm
  refine Functor.Elements.ext b.unop a.unop hb.symm ?_
  rw [← hf]
  exact f.unop.map_val

theorem face_endomorphism_eq_id {X : SSet.{0}} {a : Face X} (f : a ⟶ a) :
    f = 𝟙 a := by
  apply (semiProjection X).map_injective
  apply SemiSimplexCategory.toSimplexCategory.map_injective
  change (projection X).map f = (projection X).map (𝟙 a)
  rw [(projection X).map_id]
  exact SimplexCategory.eq_id_of_mono _

theorem face_map_eqToHom {X : SSet.{0}} {a b : Face X} (f : a ⟶ b)
    (h : a = b) : f = eqToHom h := by
  subst b
  exact face_endomorphism_eq_id f

private def repeatDeletion {n : ℕ} (i : Fin (n+1)) : Fin (n+2) →o Fin (n+2) :=
  (SimplexCategory.σ i ≫ SimplexCategory.δ i.castSucc).toOrderHom

private theorem repeatDeletion_apply {n : ℕ} (i : Fin (n+1)) (j : Fin (n+2)) :
    repeatDeletion i j = if j = i.castSucc then i.succ else j := by
  classical
  change i.castSucc.succAbove (i.predAbove j) = _
  by_cases h : j = i.castSucc
  · subst j
    simp
  · simp only [ite_eq_right h]
    exact Fin.succAbove_predAbove h

private theorem le_repeatDeletion {n : ℕ} (i : Fin (n+1)) (j : Fin (n+2)) :
    j ≤ repeatDeletion i j := by
  classical
  rw [repeatDeletion_apply]
  split_ifs with h
  · subst j
    exact i.castSucc_le_succ
  · exact le_rfl

/-- Equal consecutive dimensions give the actual simplicial degeneracy,
including all arrows of the flag. -/
theorem degenerate_of_dimension_eq {X : SSet.{0}} {n : ℕ}
    (s : (nerve (Face X)) _⦋n+1⦌) (i : Fin (n+1))
    (h : dimension (s.obj i.castSucc) = dimension (s.obj i.succ)) :
    s ∈ (nerve (Face X)).degenerate (n+1) := by
  classical
  let q := repeatDeletion i
  let t := q.monotone.functor ⋙ s
  have ho (j : Fin (n+2)) : s.obj j = t.obj j := by
    change s.obj j = s.obj (repeatDeletion i j)
    rw [repeatDeletion_apply]
    split_ifs with hj
    · subst j
      exact face_eq_of_dimension_eq (s.map (homOfLE i.castSucc_le_succ)) h
    · rfl
  let α : s ⟶ t :=
    { app j := s.map (homOfLE (le_repeatDeletion i j))
      naturality j k f := by
        change s.map f ≫ s.map (homOfLE (le_repeatDeletion i k)) =
          s.map (homOfLE (le_repeatDeletion i j)) ≫
            s.map (homOfLE (q.monotone (leOfHom f)))
        rw [← s.map_comp, ← s.map_comp]
        rfl }
  have ha (j : Fin (n+2)) : α.app j = eqToHom (ho j) :=
    face_map_eqToHom _ _
  have he : s = t := by
    refine CategoryTheory.Functor.ext ho (fun j k f => ?_)
    have hh := α.naturality f
    rw [ha, ha] at hh
    apply (cancel_mono (eqToHom (ho k))).mp
    simpa only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id] using hh
  have ht : t = (nerve (Face X)).σ i ((nerve (Face X)).δ i.castSucc s) := rfl
  rw [he, ht]
  exact (nerve (Face X)).σ_mem_degenerate i _

theorem nondegenerate_dimension_strictMono {X : SSet.{0}} {n : ℕ}
    (s : (nerve (Face X)) _⦋n⦌) (hs : s ∈ (nerve (Face X)).nonDegenerate n) :
    StrictMono (fun i => dimension (s.obj i)) := by
  cases n with
  | zero =>
    change StrictMono (fun i : Fin 1 => dimension (s.obj i))
    exact Subsingleton.strictMono _
  | succ n =>
    rw [Fin.strictMono_iff_lt_succ]
    intro i
    have hl := dimension_le (s.map (homOfLE i.castSucc_le_succ))
    refine lt_of_le_of_ne hl ?_
    intro he
    exact hs (degenerate_of_dimension_eq s i he)

instance (X : SSet.{0}) : (functor.obj X).Nonsingular where
  mono := by
    intro n ⟨s, hs⟩
    have hi : Function.Injective s.obj := by
      intro i j hij
      exact (nondegenerate_dimension_strictMono s hs).injective (congrArg dimension hij)
    simp only [NatTrans.mono_iff_mono_app, mono_iff_injective]
    intro ⟨⟨k⟩⟩ i j hij
    ext l : 1
    exact hi (CategoryTheory.Functor.congr_obj hij l)

end

end Thomason.Construction.FaceSimplexResolution

end

section

/-!
# Covers of ordinary nerves by sieves and cosieves

This proves the ordinary-poset specialization of Lemma `nerve-cover` in
*Thomason Model Structures in Every Strict Higher Dimension*. A simplex in
the nerve lies in a full sieve as soon as its last vertex lies there. Dually,
its first vertex detects membership in a full cosieve. Consequently two
such subposets covering the objects cover the actual nerve as subcomplexes.
-/

open CategoryTheory

namespace Thomason.Construction

universe u

variable {E : Type u} [PartialOrder E]

/-- The full subcomplex of the ordinary nerve on a set of vertices. -/
def fullSubposetComplex (A : Set E) : (nerve E).Subcomplex where
  obj _Δ := {s | ∀ i, s.obj i ∈ A}
  map f _s hs i := hs ((SimplexCategory.toCat.map f.unop).toFunctor.obj i)

@[simp]
theorem mem_fullSubposetComplex (A : Set E) {Δ : SimplexCategoryᵒᵖ}
    (s : (nerve E).obj Δ) :
    s ∈ (fullSubposetComplex A).obj Δ ↔ ∀ i, s.obj i ∈ A := Iff.rfl

/-- The ordinary functor including the full induced subposet. -/
def fullSubposetInclusion (A : Set E) : A ⥤ E :=
  (show Monotone (fun a : A => (a : E)) from fun _ _ h => h).functor

/-- Every simplex whose vertices lie in `A` lifts to the nerve of `A`. -/
def liftSimplexToSubposet (A : Set E) {Δ : SimplexCategoryᵒᵖ}
    (s : (nerve E).obj Δ) (hs : ∀ i, s.obj i ∈ A) : (nerve A).obj Δ where
  obj i := ⟨s.obj i, hs i⟩
  map f := homOfLE (leOfHom (s.map f))

@[simp]
theorem nerveMap_liftSimplexToSubposet (A : Set E) {Δ : SimplexCategoryᵒᵖ}
    (s : (nerve E).obj Δ) (hs : ∀ i, s.obj i ∈ A) :
    (nerveMap (fullSubposetInclusion A)).app Δ (liftSimplexToSubposet A s hs) = s :=
  nerve.ext_of_isThin rfl

/-- The vertex-defined subcomplex is the actual image of the nerve of the
full induced subposet. -/
theorem fullSubposetComplex_eq_range (A : Set E) :
    fullSubposetComplex A = SSet.Subcomplex.range (nerveMap (fullSubposetInclusion A)) := by
  ext Δ s
  constructor
  · intro hs
    exact ⟨liftSimplexToSubposet A s hs, nerveMap_liftSimplexToSubposet A s hs⟩
  · rintro ⟨t, rfl⟩ i
    exact (t.obj i).property

/-- The intersection of full subposet nerves is the nerve of the intersection. -/
theorem fullSubposetComplex_inter (A B : Set E) :
    fullSubposetComplex (A ∩ B) = fullSubposetComplex A ⊓ fullSubposetComplex B := by
  ext Δ s
  constructor
  · intro h
    exact ⟨fun i => (h i).1, fun i => (h i).2⟩
  · rintro ⟨ha, hb⟩ i
    exact ⟨ha i, hb i⟩

/-- A cover of the ordinary nerve by full subcomplexes is an ordinary
pushout along the common full subcomplex. -/
theorem fullSubposetComplex_isPushout (A B : Set E)
    (hcover : fullSubposetComplex A ⊔ fullSubposetComplex B = ⊤) :
    IsPushout
      (SSet.Subcomplex.homOfLE (show fullSubposetComplex (A ∩ B) ≤
        fullSubposetComplex A from fun _ _ h i => (h i).1))
      (SSet.Subcomplex.homOfLE (show fullSubposetComplex (A ∩ B) ≤
        fullSubposetComplex B from fun _ _ h i => (h i).2))
      (fullSubposetComplex A).ι (fullSubposetComplex B).ι := by
  have sq : SSet.Subcomplex.BicartSq (fullSubposetComplex (A ∩ B))
      (fullSubposetComplex A) (fullSubposetComplex B) ⊤ :=
    ⟨hcover, (fullSubposetComplex_inter A B).symm⟩
  exact sq.isPushout.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (SSet.Subcomplex.topIso (nerve E))
    (by simp) (by simp) (by simp) (by simp)

/-- A sieve containing the final vertex contains every vertex of a simplex. -/
theorem vertex_mem_of_last_mem {A : Set E} (hA : IsLowerSet A)
    {Δ : SimplexCategoryᵒᵖ} (s : (nerve E).obj Δ)
    (hlast : s.obj (Fin.last Δ.unop.len) ∈ A)
    (i : Fin (Δ.unop.len + 1)) : s.obj i ∈ A :=
  hA (leOfHom (s.map (homOfLE (Fin.le_last i)))) hlast

/-- Membership in a full sieve nerve is detected at the final vertex. -/
theorem mem_fullSubposetComplex_iff_last {A : Set E} (hA : IsLowerSet A)
    {Δ : SimplexCategoryᵒᵖ} (s : (nerve E).obj Δ) :
    s ∈ (fullSubposetComplex A).obj Δ ↔ s.obj (Fin.last Δ.unop.len) ∈ A :=
  ⟨fun h => h _, fun h => vertex_mem_of_last_mem hA s h⟩

/-- Two sieves covering the vertices cover every simplex of the ordinary nerve. -/
theorem simplex_mem_of_sieve_cover {A B : Set E}
    (hA : IsLowerSet A) (hB : IsLowerSet B) (hcover : ∀ e, e ∈ A ∨ e ∈ B)
    {Δ : SimplexCategoryᵒᵖ} (s : (nerve E).obj Δ) :
    s ∈ (fullSubposetComplex A).obj Δ ∨ s ∈ (fullSubposetComplex B).obj Δ :=
  (hcover (s.obj (Fin.last Δ.unop.len))).imp
    (vertex_mem_of_last_mem hA s) (vertex_mem_of_last_mem hB s)

/-- The actual ordinary nerve is the union of the nerves of two covering sieves. -/
theorem sieve_nerve_cover {A B : Set E}
    (hA : IsLowerSet A) (hB : IsLowerSet B) (hcover : ∀ e, e ∈ A ∨ e ∈ B) :
    fullSubposetComplex A ⊔ fullSubposetComplex B = ⊤ := by
  apply top_unique
  intro Δ s _
  exact simplex_mem_of_sieve_cover hA hB hcover s

/-- The two covering sieve nerves and their intersection form an actual
pushout square in simplicial sets. -/
theorem sieve_nerve_isPushout {A B : Set E}
    (hA : IsLowerSet A) (hB : IsLowerSet B) (hcover : ∀ e, e ∈ A ∨ e ∈ B) :
    IsPushout
      (SSet.Subcomplex.homOfLE (show fullSubposetComplex (A ∩ B) ≤
        fullSubposetComplex A from fun _ _ h i => (h i).1))
      (SSet.Subcomplex.homOfLE (show fullSubposetComplex (A ∩ B) ≤
        fullSubposetComplex B from fun _ _ h i => (h i).2))
      (fullSubposetComplex A).ι (fullSubposetComplex B).ι :=
  fullSubposetComplex_isPushout A B (sieve_nerve_cover hA hB hcover)

/-- A cosieve containing the initial vertex contains every simplex vertex. -/
theorem vertex_mem_of_first_mem {A : Set E} (hA : IsUpperSet A)
    {Δ : SimplexCategoryᵒᵖ} (s : (nerve E).obj Δ)
    (hfirst : s.obj 0 ∈ A) (i : Fin (Δ.unop.len + 1)) : s.obj i ∈ A :=
  hA (leOfHom (s.map (homOfLE (Fin.zero_le i)))) hfirst

/-- Membership in a full cosieve nerve is detected at the initial vertex. -/
theorem mem_fullSubposetComplex_iff_first {A : Set E} (hA : IsUpperSet A)
    {Δ : SimplexCategoryᵒᵖ} (s : (nerve E).obj Δ) :
    s ∈ (fullSubposetComplex A).obj Δ ↔ s.obj 0 ∈ A :=
  ⟨fun h => h _, fun h => vertex_mem_of_first_mem hA s h⟩

/-- Two cosieves covering the vertices cover the actual ordinary nerve. -/
theorem cosieve_nerve_cover {A B : Set E}
    (hA : IsUpperSet A) (hB : IsUpperSet B) (hcover : ∀ e, e ∈ A ∨ e ∈ B) :
    fullSubposetComplex A ⊔ fullSubposetComplex B = ⊤ := by
  apply top_unique
  intro Δ s _
  exact (hcover (s.obj 0)).imp
    (vertex_mem_of_first_mem hA s) (vertex_mem_of_first_mem hB s)

end Thomason.Construction

end

section

/-! # The face-poset map for nonsingular simplicial targets

For a nonsingular simplicial set, face inclusions are unique. Reading the
last vertex in each face therefore gives a genuine simplicial map from
the nerve of its nondegenerate face poset into the original target.
-/

namespace Thomason.Construction.NonsingularLastVertex

open CategoryTheory Opposite
open scoped Simplicial

noncomputable section

variable {X : SSet.{0}} [X.Nonsingular]

/-- Read a face's last vertex inside the greatest face of a flag. -/
def vertex {n : SimplexCategory} (s : (nerve X.N).obj (.op n))
    (i : Fin (n.len+1)) : Fin ((s.obj (Fin.last n.len)).dim+1) :=
  (SSet.N.monoOfLE (s.monotone (Fin.le_last i))).toOrderHom
    (Fin.last (s.obj i).dim)

theorem vertex_monotone {n : SimplexCategory} (s : (nerve X.N).obj (.op n)) :
    Monotone (vertex s) := by
  intro i j hij
  have he := SSet.N.monoOfLE_comp (s.monotone hij) (s.monotone (Fin.le_last j))
  have hv := congrArg
    (fun f => f.toOrderHom (Fin.last (s.obj i).dim)) he
  change (SSet.N.monoOfLE (s.monotone (Fin.le_last j))).toOrderHom
    ((SSet.N.monoOfLE (s.monotone hij)).toOrderHom (Fin.last (s.obj i).dim)) =
      vertex s i at hv
  rw [← hv]
  exact (SSet.N.monoOfLE (s.monotone (Fin.le_last j))).toOrderHom.monotone
    (Fin.le_last _)

def ordinal {n : SimplexCategory} (s : (nerve X.N).obj (.op n)) :
    n ⟶ SimplexCategory.mk (s.obj (Fin.last n.len)).dim :=
  SimplexCategory.Hom.mk ⟨vertex s, vertex_monotone s⟩

def simplex {n : SimplexCategory} (s : (nerve X.N).obj (.op n)) : X.obj (.op n) :=
  X.map (ordinal s).op (s.obj (Fin.last n.len)).simplex

/-- Restricting a flag changes its greatest face by the unique face map. -/
theorem ordinal_naturality {m n : SimplexCategory} (a : m ⟶ n)
    (s : (nerve X.N).obj (.op n)) :
    a ≫ ordinal s = ordinal ((nerve X.N).map a.op s) ≫
      SSet.N.monoOfLE (s.monotone (Fin.le_last (a.toOrderHom (Fin.last m.len)))) := by
  apply SimplexCategory.Hom.ext
  apply DFunLike.ext
  intro i
  change vertex s (a.toOrderHom i) =
    (SSet.N.monoOfLE
      (s.monotone (Fin.le_last (a.toOrderHom (Fin.last m.len))))).toOrderHom
        (vertex ((nerve X.N).map a.op s) i)
  have he := SSet.N.monoOfLE_comp
    (s.monotone (a.toOrderHom.monotone (Fin.le_last i)))
    (s.monotone (Fin.le_last (a.toOrderHom (Fin.last m.len))))
  exact (congrArg
    (fun f => f.toOrderHom (Fin.last (s.obj (a.toOrderHom i)).dim)) he).symm

theorem simplex_naturality {m n : SimplexCategory} (a : m ⟶ n)
    (s : (nerve X.N).obj (.op n)) :
    X.map a.op (simplex s) = simplex ((nerve X.N).map a.op s) := by
  unfold simplex
  rw [← Functor.map_comp_apply, ← op_comp, ordinal_naturality, op_comp,
    Functor.map_comp_apply]
  exact congrArg (X.map (ordinal ((nerve X.N).map a.op s)).op)
    (SSet.N.map_monoOfLE
      (s.monotone (Fin.le_last (a.toOrderHom (Fin.last m.len)))))

/-- Actual face-poset last vertex, with codomain the original simplicial set. -/
def map (X : SSet.{0}) [X.Nonsingular] : nerve X.N ⟶ X where
  app d := ↾fun s => simplex s
  naturality _ _ a := by
    apply ConcreteCategory.hom_ext
    intro s
    exact (simplex_naturality a.unop s).symm

/-- Every output simplex remains inside the greatest input face. -/
theorem simplex_carrier {n : SimplexCategory} (s : (nerve X.N).obj (.op n)) :
    SSet.Subcomplex.ofSimplex (simplex s) ≤ (s.obj (Fin.last n.len)).subcomplex :=
  SSet.Subcomplex.ofSimplex_map_le (ordinal s) _

end

end Thomason.Construction.NonsingularLastVertex

end

section

/-! # The ordinary face-poset comparison lifts through the fat resolution

For a nonsingular source the nondegenerate faces give a canonical functor
to its face-simplex category. Its augmentation is the face-poset
last-vertex map.
-/

namespace Thomason.Construction.FaceSimplexResolution

open CategoryTheory Opposite
open scoped Simplicial

noncomputable section

def simplexObject {X : SSet.{0}} {n : ℕ} (x : X _⦋n⦌) : Face X :=
  .op { obj := .op (SemiSimplexCategory.mk n), val := x }

def simplexMorphism {X : SSet.{0}} {n m : ℕ} (x : X _⦋n⦌) (y : X _⦋m⦌)
    (f : SimplexCategory.mk n ⟶ SimplexCategory.mk m) [hm : Mono f]
    (hf : X.map f.op y = x) : simplexObject x ⟶ simplexObject y :=
  Quiver.Hom.op
    { hom := (@SemiSimplexCategory.homOfMono (.mk n) (.mk m) f hm).op
      map_val := by
        change X.map (SemiSimplexCategory.toSimplexCategory.map
          (@SemiSimplexCategory.homOfMono (.mk n) (.mk m) f hm)).op y = x
        exact (congrArg (fun g : SimplexCategory.mk n ⟶ SimplexCategory.mk m =>
          X.map g.op y)
          (@SemiSimplexCategory.toSimplexCategory_map_homOfMono (.mk n) (.mk m) f hm)).trans hf }

@[simp]
theorem simplexMorphism_projection {X : SSet.{0}} {n m : ℕ}
    (x : X _⦋n⦌) (y : X _⦋m⦌) (f : SimplexCategory.mk n ⟶ SimplexCategory.mk m)
    [hm : Mono f] (hf : X.map f.op y = x) :
    (projection X).map (simplexMorphism x y f hf) = f :=
  @SemiSimplexCategory.toSimplexCategory_map_homOfMono (.mk n) (.mk m) f hm

def nondegenerateFaceFunctor (X : SSet.{0}) [X.Nonsingular] : X.N ⥤ Face X where
  obj x := simplexObject x.simplex
  map {x y} f := simplexMorphism x.simplex y.simplex
    (SSet.N.monoOfLE (leOfHom f)) (SSet.N.map_monoOfLE _)
  map_id x := by
    apply (semiProjection X).map_injective
    apply SemiSimplexCategory.toSimplexCategory.map_injective
    change (projection X).map _ = (projection X).map _
    simp only [simplexMorphism_projection, SSet.N.monoOfLE_refl,
      CategoryTheory.Functor.map_id]
    rfl
  map_comp f g := by
    apply (semiProjection X).map_injective
    apply SemiSimplexCategory.toSimplexCategory.map_injective
    change (projection X).map _ = (projection X).map _
    simp only [simplexMorphism_projection, CategoryTheory.Functor.map_comp]
    exact (SSet.N.monoOfLE_comp (leOfHom f) (leOfHom g)).symm

def nondegenerateLift (X : SSet.{0}) [X.Nonsingular] : nerve X.N ⟶ functor.obj X :=
  nerveMap (nondegenerateFaceFunctor X)

theorem nondegenerateLift_ordinal {X : SSet.{0}} [X.Nonsingular] {n : SimplexCategory}
    (s : (nerve X.N).obj (.op n)) :
    ordinal (s ⋙ nondegenerateFaceFunctor X) = NonsingularLastVertex.ordinal s := by
  apply SimplexCategory.Hom.ext
  apply DFunLike.ext
  intro i
  exact congrArg (fun f => f.toOrderHom (Fin.last (s.obj i).dim))
    (simplexMorphism_projection (s.obj i).simplex (s.obj (Fin.last n.len)).simplex
      (SSet.N.monoOfLE (s.monotone (Fin.le_last i))) (SSet.N.map_monoOfLE _))

/-- The diagram commutes as simplicial maps into the original source. -/
@[reassoc]
theorem nondegenerateLift_augmentation (X : SSet.{0}) [X.Nonsingular] :
    nondegenerateLift X ≫ augmentation X = NonsingularLastVertex.map X := by
  apply NatTrans.ext
  funext d
  apply ConcreteCategory.hom_ext
  intro s
  change X.map (ordinal (s ⋙ nondegenerateFaceFunctor X)).op _ =
    X.map (NonsingularLastVertex.ordinal s).op _
  rw [nondegenerateLift_ordinal]
  rfl

/-- A map out of a nonsingular source has a specified map into the
resolution after passing to its nondegenerate face poset. -/
def resolvedMap {A X : SSet.{0}} [A.Nonsingular] (a : A ⟶ X) :
    nerve A.N ⟶ functor.obj X := nondegenerateLift A ≫ functor.map a

@[reassoc]
theorem resolvedMap_augmentation {A X : SSet.{0}} [A.Nonsingular] (a : A ⟶ X) :
    resolvedMap a ≫ augmentation X = NonsingularLastVertex.map A ≫ a := by
  rw [resolvedMap, Category.assoc, augmentation_naturality,
    ← Category.assoc, nondegenerateLift_augmentation]

end

end Thomason.Construction.FaceSimplexResolution

end

end OAI
