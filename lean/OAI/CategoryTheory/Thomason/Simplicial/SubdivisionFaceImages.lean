import OAI.CategoryTheory.Thomason.Gray.GrayMappingInterchangeEvaluation
import OAI.CategoryTheory.Thomason.Gray.SimplexCylinderGeneration
import OAI.CategoryTheory.Thomason.Simplicial.FaceSimplexLift
import OAI.CategoryTheory.Thomason.Simplicial.HornWeakEquivalences
import OAI.CategoryTheory.Thomason.Simplicial.RealizationTopology
import OAI.CategoryTheory.Thomason.Simplicial.RealizedSimplexWeakEquivalences
import OAI.CategoryTheory.Thomason.Simplicial.SingularKanComplex
import OAI.CategoryTheory.Thomason.Simplicial.TruncationQuotientComposition
import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj
import Mathlib.Data.Finset.Preimage
import Mathlib.Topology.Homotopy.Contractible

namespace OAI

section

/-! # Singular simplices carry continuous homotopies to simplicial homotopies

The interval coordinate of an ordered simplex is its affine barycentric
coordinate. Its compatibility includes every face and degeneracy.
-/

namespace Thomason.Construction

open CategoryTheory Convexity
open scoped Simplicial

noncomputable section

/-- The affine time coordinate of a simplex of the simplicial interval. -/
def singularSimplexTime {n : SimplexCategoryᵒᵖ} (u : (Δ[1] : SSet.{0}).obj n) :
    C(StdSimplex ℝ (Fin (n.unop.len+1)), unitInterval) where
  toFun x := StdSimplex.homeomorphI (StdSimplex.map (SSet.stdSimplex.objEquiv u).toOrderHom x)
  continuous_toFun := StdSimplex.homeomorphI.continuous.comp (by fun_prop)

/-- The affine time is natural even when the ordinal map merges vertices. -/
theorem singularSimplexTime_naturality {m n : SimplexCategory} (f : m ⟶ n)
    (u : (Δ[1] : SSet.{0}).obj (.op n)) (x : StdSimplex ℝ (Fin (m.len+1))) :
    singularSimplexTime ((Δ[1] : SSet.{0}).map f.op u) x =
      singularSimplexTime u (StdSimplex.map f.toOrderHom x) := by
  change StdSimplex.homeomorphI
      (StdSimplex.map ((SSet.stdSimplex.objEquiv u).toOrderHom ∘ f.toOrderHom) x) = _
  rw [StdSimplex.map_comp]
  rfl

/-- A continuous homotopy applied simplexwise, with the affine interval coordinate. -/
def singularHomotopy {X Y : TopCat.{0}} {f g : X ⟶ Y} (H : f.hom.Homotopy g.hom) :
    SSet.Homotopy (TopCat.toSSet.map f) (TopCat.toSSet.map g) where
  h := {
    app n := ↾fun p => (TopCat.toSSetObjEquiv Y n).symm
      ⟨fun x => H (singularSimplexTime p.2 x, (TopCat.toSSetObjEquiv X n p.1) x),
        H.continuous.comp (by fun_prop)⟩
    naturality m n a := by
      ext p
      rcases p with ⟨s, u⟩
      apply (TopCat.toSSetObjEquiv Y n).injective
      apply ContinuousMap.ext
      intro x
      change H (singularSimplexTime ((Δ[1] : SSet.{0}).map a u) x,
          (TopCat.toSSetObjEquiv X m s) (StdSimplex.map a.unop.toOrderHom x)) =
        H (singularSimplexTime u (StdSimplex.map a.unop.toOrderHom x),
          (TopCat.toSSetObjEquiv X m s) (StdSimplex.map a.unop.toOrderHom x))
      exact congrArg (fun t => H (t, (TopCat.toSSetObjEquiv X m s)
        (StdSimplex.map a.unop.toOrderHom x))) (singularSimplexTime_naturality a.unop u x) }
  h₀ := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro p
    apply (TopCat.toSSetObjEquiv Y n).injective
    apply ContinuousMap.ext
    intro x
    change H (StdSimplex.homeomorphI (StdSimplex.map (fun _ => (0 : Fin 2)) x),
      (TopCat.toSSetObjEquiv X n p) x) = f.hom ((TopCat.toSSetObjEquiv X n p) x)
    rw [StdSimplex.map_const, StdSimplex.homeomorphI_single_zero]
    exact H.map_zero_left _
  h₁ := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro p
    apply (TopCat.toSSetObjEquiv Y n).injective
    apply ContinuousMap.ext
    intro x
    change H (StdSimplex.homeomorphI (StdSimplex.map (fun _ => (1 : Fin 2)) x),
      (TopCat.toSSetObjEquiv X n p) x) = g.hom ((TopCat.toSSetObjEquiv X n p) x)
    rw [StdSimplex.map_const, StdSimplex.homeomorphI_single_one]
    exact H.map_one_left _
  rel := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro p
    exact False.elim p.1.property

/-- After singularization, continuous homotopies preserve the actual realization weak test. -/
theorem singular_weakEquivalence_iff {X Y : TopCat.{0}} {f g : X ⟶ Y}
    (H : f.hom.Homotopy g.hom) :
    realizationWeakEquivalences (TopCat.toSSet.map f) ↔
      realizationWeakEquivalences (TopCat.toSSet.map g) :=
  RealizedCylinder.weakEquivalence_iff (singularHomotopy H)

end

end Thomason.Construction

end

section

/-! # Evaluation of actual singular simplices -/

namespace Thomason.Construction

open CategoryTheory Convexity
open scoped Simplicial

noncomputable section

/-- The counit on a represented singular simplex is its defining continuous map. -/
theorem singular_counit_simplex (X : TopCat.{0}) (n : SimplexCategory)
    (s : (TopCat.toSSet.obj X).obj (.op n)) :
    (SSet.toTopSimplex.inv.app n ≫ SSet.toTop.map (SSet.yonedaEquiv.symm s)) ≫
      sSetTopAdj.counit.app X = s.down := by
  have ht := congrArg (fun f : TopCat.toSSet.obj X ⟶ TopCat.toSSet.obj X =>
    (f.app (.op n) s).down) (sSetTopAdj.right_triangle_components X)
  change ((sSetTopAdj.unit.app (TopCat.toSSet.obj X)).app (.op n) s).down ≫
    sSetTopAdj.counit.app X = s.down at ht
  rw [sSetTopAdj_unit_app_app_down] at ht
  exact ht

/-- Pointwise evaluation formula for every simplex in the realization colimit. -/
theorem singular_counit_leg (X : TopCat.{0})
    (j : CostructuredArrow SSet.stdSimplex (TopCat.toSSet.obj X))
    (p : (RealizationPrism.diagram (TopCat.toSSet.obj X)).obj j) :
    (sSetTopAdj.counit.app X).hom ((RealizationPrism.leg (TopCat.toSSet.obj X) j).hom p) =
      (TopCat.toSSetObjEquiv X (.op j.left) (SSet.yonedaEquiv j.hom)) p.down := by
  have h := singular_counit_simplex X j.left (SSet.yonedaEquiv j.hom)
  rw [Equiv.symm_apply_apply] at h
  exact congrArg (fun f => f.hom p) h

/-- Evaluation of a simplicial-interval simplex is its affine time function. -/
theorem realizationTime_simplex (n : SimplexCategory)
    (u : (Δ[1] : SSet.{0}).obj (.op n)) (p : StdSimplex ℝ (Fin (n.len+1))) :
    PrismBarycentric.realizationTime.hom
      ((RealizationPrism.leg (Δ[1] : SSet.{0})
        (CostructuredArrow.mk (SSet.yonedaEquiv.symm u))).hom (ULift.up p)) =
      singularSimplexTime u p := by
  have hu : SSet.yonedaEquiv.symm u = SSet.stdSimplex.map (SSet.stdSimplex.objEquiv u) := by
    apply SSet.yonedaEquiv.injective
    rw [Equiv.apply_symm_apply, SSet.yonedaEquiv_map, Equiv.symm_apply_apply]
  change StdSimplex.homeomorphI ((SimplexCategory.mk 1).toTopHomeo
    ((SSet.toTop.map (SSet.yonedaEquiv.symm u)).hom
      ((SSet.toTopSimplex.inv.app n).hom (ULift.up p)))) = _
  rw [hu, SimplexCategory.toTopHomeo_naturality_apply]
  have h := congrArg (fun f => f.hom (ULift.up p)) (SSet.toTopSimplex.inv_hom_id_app n)
  exact congrArg (fun q => StdSimplex.homeomorphI
    (StdSimplex.map (SSet.stdSimplex.objEquiv u).toOrderHom q.down)) h

/-- Evaluation commutes with a simplicial map into the singular set, simplexwise. -/
theorem singular_counit_map_leg {K : SSet.{0}} (X : TopCat.{0})
    (f : K ⟶ TopCat.toSSet.obj X) (j : CostructuredArrow SSet.stdSimplex K)
    (p : (RealizationPrism.diagram K).obj j) :
    (sSetTopAdj.counit.app X).hom
      ((SSet.toTop.map f).hom ((RealizationPrism.leg K j).hom p)) =
      (TopCat.toSSetObjEquiv X (.op j.left)
        (f.app (.op j.left) (SSet.yonedaEquiv j.hom))) p.down := by
  have he := congrArg (fun g => g.hom p) (RealizationPrism.leg_naturality f j)
  change (SSet.toTop.map f).hom ((RealizationPrism.leg K j).hom p) = _ at he
  rw [he, singular_counit_leg]
  exact congrArg (fun s => (TopCat.toSSetObjEquiv X (.op j.left) s) p.down)
    (SSet.yonedaEquiv_comp j.hom f)

/-- The same simplexwise naturality for the interval coordinate. -/
theorem realizationTime_map_leg {K : SSet.{0}} (f : K ⟶ (Δ[1] : SSet.{0}))
    (j : CostructuredArrow SSet.stdSimplex K) (p : (RealizationPrism.diagram K).obj j) :
    PrismBarycentric.realizationTime.hom
      ((SSet.toTop.map f).hom ((RealizationPrism.leg K j).hom p)) =
      singularSimplexTime (f.app (.op j.left) (SSet.yonedaEquiv j.hom)) p.down := by
  have he := congrArg (fun g => g.hom p) (RealizationPrism.leg_naturality f j)
  change (SSet.toTop.map f).hom ((RealizationPrism.leg K j).hom p) = _ at he
  rw [he]
  have hj : j.hom ≫ f = SSet.yonedaEquiv.symm
      (f.app (.op j.left) (SSet.yonedaEquiv j.hom)) := by
    apply SSet.yonedaEquiv.injective
    rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
  change PrismBarycentric.realizationTime.hom
    ((RealizationPrism.leg (Δ[1] : SSet.{0}) (CostructuredArrow.mk (j.hom ≫ f))).hom p) = _
  rw [hj]
  exact realizationTime_simplex _ _ _

end

end Thomason.Construction

end

section

/-! # A direct singular/realization compatibility for homotopy equivalences -/

namespace Thomason.Construction

open CategoryTheory

noncomputable section

/-- Simplicial homotopy inverses give actual topological homotopy inverses. -/
def realizationHomotopyEquiv {X Y : SSet.{0}} (f : X ⟶ Y) (g : Y ⟶ X)
    (hX : SSet.Homotopy (f ≫ g) (𝟙 X)) (hY : SSet.Homotopy (g ≫ f) (𝟙 Y)) :
    ContinuousMap.HomotopyEquiv (SSet.toTop.obj X) (SSet.toTop.obj Y) where
  toFun := (SSet.toTop.map f).hom
  invFun := (SSet.toTop.map g).hom
  left_inv := ⟨(RealizedCylinder.homotopy hX).cast (by
    rw [Functor.map_comp]; rfl) (by rw [CategoryTheory.Functor.map_id]; rfl)⟩
  right_inv := ⟨(RealizedCylinder.homotopy hY).cast (by
    rw [Functor.map_comp]; rfl) (by rw [CategoryTheory.Functor.map_id]; rfl)⟩

/-- The semantic weak test for a simplicial map with actual homotopy inverse. -/
theorem simplicial_homotopy_inverse_weak {X Y : SSet.{0}} (f : X ⟶ Y) (g : Y ⟶ X)
    (hX : SSet.Homotopy (f ≫ g) (𝟙 X)) (hY : SSet.Homotopy (g ≫ f) (𝟙 Y)) :
    realizationWeakEquivalences f :=
  homotopyEquiv_isWeakHomotopyEquivalence (realizationHomotopyEquiv f g hX hY)

/-- Singularization of a continuous homotopy equivalence satisfies the actual
realization weak-equivalence test, without using the counit weak theorem. -/
theorem singular_homotopy_equivalence_weak {X Y : TopCat.{0}}
    (e : ContinuousMap.HomotopyEquiv X Y) :
    realizationWeakEquivalences (TopCat.toSSet.map (TopCat.ofHom e.toFun)) := by
  let f : X ⟶ Y := TopCat.ofHom e.toFun
  let g : Y ⟶ X := TopCat.ofHom e.invFun
  have hX : SSet.Homotopy (TopCat.toSSet.map f ≫ TopCat.toSSet.map g) (𝟙 _) := by
    have h := singularHomotopy (f := f ≫ g) (g := 𝟙 X) e.left_inv.some
    simpa only [Functor.map_comp, CategoryTheory.Functor.map_id] using h
  have hY : SSet.Homotopy (TopCat.toSSet.map g ≫ TopCat.toSSet.map f) (𝟙 _) := by
    have h := singularHomotopy (f := g ≫ f) (g := 𝟙 Y) e.right_inv.some
    simpa only [Functor.map_comp, CategoryTheory.Functor.map_id] using h
  exact simplicial_homotopy_inverse_weak _ _ hX hY

/-- In particular, every stationary topological deformation remains weak after
singularization and realization. -/
theorem singular_deformation_weak {X Y : TopCat.{0}} {f : X ⟶ Y}
    (d : TopologicalDeformation.Data f) :
    realizationWeakEquivalences (TopCat.toSSet.map f) := by
  apply singular_homotopy_equivalence_weak (X := X) (Y := Y) {
    toFun := f.hom
    invFun := d.retraction.hom
    left_inv := by
      have he : d.retraction.hom.comp f.hom = ContinuousMap.id X :=
        congrArg TopCat.Hom.hom d.left_inv
      rw [he]
    right_inv := ⟨d.homotopy.toHomotopy⟩ }

end

end Thomason.Construction

end

section

/-! # The actual realization–singular counit on contractible spaces -/

namespace Thomason.Construction

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

noncomputable section

/-- The realization of the zero simplex is an actual terminal topological space. -/
def realizedPointIsTerminal : IsTerminal (SSet.toTop.obj (Δ[0] : SSet.{0})) := by
  let P := SSet.toTop.obj (Δ[0] : SSet.{0})
  letI : ∀ X : TopCat.{0}, Unique (X ⟶ P) := fun X => {
    default := TopCat.ofHom (ContinuousMap.const X default)
    uniq f := by
      apply TopCat.hom_ext
      apply ContinuousMap.ext
      intro x
      exact Subsingleton.elim _ _ }
  exact IsTerminal.ofUnique _

/-- The singular simplicial set of this point is the actual zero simplex. -/
def singularRealizedPointIso :
    TopCat.toSSet.obj (SSet.toTop.obj (Δ[0] : SSet.{0})) ≅ (Δ[0] : SSet.{0}) :=
  (realizedPointIsTerminal.isTerminalObj TopCat.toSSet _).uniqueUpToIso
    SSet.stdSimplex.isTerminalObj₀

/-- At a point, the evaluation counit is an isomorphism. -/
instance counit_realized_point_isIso :
    IsIso (sSetTopAdj.counit.app (SSet.toTop.obj (Δ[0] : SSet.{0}))) := by
  have he : sSetTopAdj.counit.app (SSet.toTop.obj (Δ[0] : SSet.{0})) =
      SSet.toTop.map singularRealizedPointIso.hom := by
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro x
    exact @Subsingleton.elim (SSet.toTop.obj (Δ[0] : SSet.{0})) inferInstance _ _
  rw [he]
  infer_instance

/-- The counit weak-equivalence test transports along actual homotopy equivalences. -/
theorem singular_counit_weak_of_homotopyEquiv {X Y : TopCat.{0}}
    (e : ContinuousMap.HomotopyEquiv X Y)
    (hY : topologicalWeakEquivalences (sSetTopAdj.counit.app Y)) :
    topologicalWeakEquivalences (sSetTopAdj.counit.app X) := by
  let f : X ⟶ Y := TopCat.ofHom e.toFun
  have hf : topologicalWeakEquivalences f := homotopyEquiv_isWeakHomotopyEquivalence e
  have hs : topologicalWeakEquivalences (SSet.toTop.map (TopCat.toSSet.map f)) :=
    singular_homotopy_equivalence_weak e
  apply topologicalWeakEquivalences.of_postcomp (sSetTopAdj.counit.app X) f hf
  have hn : SSet.toTop.map (TopCat.toSSet.map f) ≫ sSetTopAdj.counit.app Y =
      sSetTopAdj.counit.app X ≫ f := sSetTopAdj.counit.naturality f
  rw [← hn]
  exact topologicalWeakEquivalences.comp_mem _ _ hs hY

/-- Contractibility suffices for the actual counit weak-equivalence theorem. -/
theorem singular_counit_weak_contractible (X : TopCat.{0}) [ContractibleSpace X] :
    topologicalWeakEquivalences (sSetTopAdj.counit.app X) := by
  let e := (ContractibleSpace.hequiv_unit X).some.trans
    (Homeomorph.homeomorphOfUnique Unit (SSet.toTop.obj (Δ[0] : SSet.{0}))).toHomotopyEquiv
  exact singular_counit_weak_of_homotopyEquiv e (topologicalWeakEquivalences.of_isIso _)

end

end Thomason.Construction

end

section

/-! # The singular homotopy comparison commutes with actual evaluation -/

namespace Thomason.Construction

open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open scoped Simplicial

noncomputable section

/-- Evaluation of a singular homotopy is the original homotopy on both coordinates. -/
theorem singularHomotopy_counit {X Y : TopCat.{0}} {f g : X ⟶ Y}
    (H : f.hom.Homotopy g.hom)
    (z : SSet.toTop.obj (TopCat.toSSet.obj X ⊗ Δ[1])) :
    (sSetTopAdj.counit.app Y).hom ((SSet.toTop.map (singularHomotopy H).h).hom z) =
      H (PrismBarycentric.realizationTime.hom
          ((SSet.toTop.map (snd (TopCat.toSSet.obj X) Δ[1])).hom z),
        (sSetTopAdj.counit.app X).hom
          ((SSet.toTop.map (fst (TopCat.toSSet.obj X) Δ[1])).hom z)) := by
  obtain ⟨j, p, rfl⟩ := RealizationPrism.point_representation (TopCat.toSSet.obj X ⊗ Δ[1]) z
  rw [singular_counit_map_leg, realizationTime_map_leg, singular_counit_map_leg]
  rfl

/-- The realized simplicial homotopy is given by the same assembled comparison. -/
theorem realizedHomotopy_apply {K L : SSet.{0}} {f g : K ⟶ L}
    (H : SSet.Homotopy f g) (t : unitInterval) (x : SSet.toTop.obj K) :
    RealizedCylinder.homotopy H (t, x) =
      (SSet.toTop.map H.h).hom ((RealizedCylinder.comparison K).hom (x, t)) := by
  obtain ⟨j, p, rfl⟩ := RealizationPrism.point_representation K x
  rw [RealizedCylinder.comparison_leg]
  exact congrArg (fun h => h.hom (p, t))
    (RealizationPrism.assemble_fac K _
      (fun j => RealizedCylinder.piece K j ≫ SSet.toTop.map H.h)
      (fun q => by rw [← Category.assoc, RealizedCylinder.piece_naturality]) j)

/-- Realizing a singular homotopy and then evaluating recovers the continuous homotopy
at every point, not merely its homotopy class. -/
theorem realizedSingularHomotopy_counit {X Y : TopCat.{0}} {f g : X ⟶ Y}
    (H : f.hom.Homotopy g.hom) (t : unitInterval)
    (x : SSet.toTop.obj (TopCat.toSSet.obj X)) :
    (sSetTopAdj.counit.app Y).hom (RealizedCylinder.homotopy (singularHomotopy H) (t, x)) =
      H (t, (sSetTopAdj.counit.app X).hom x) := by
  rw [realizedHomotopy_apply, singularHomotopy_counit,
    RealizedCylinder.comparison_time, RealizedCylinder.comparison_first]

end

end Thomason.Construction

end

section

/-! # Exact relative stationarity survives actual geometric realization -/

namespace Thomason.Construction.RealizedCylinder

open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open scoped Simplicial

noncomputable section

variable {A K L : SSet.{0}} {f g : K ⟶ L}

/-- A stationary simplicial cylinder is stationary at every point of the
    actual realized image, not just at its vertices. -/
theorem homotopy_stationary (H : SSet.Homotopy f g) (i : A ⟶ K)
    (hi : i ▷ Δ[1] ≫ H.h = fst A Δ[1] ≫ i ≫ f)
    (t : unitInterval) (x : SSet.toTop.obj A) :
    homotopy H (t, (SSet.toTop.map i).hom x) =
      (SSet.toTop.map f).hom ((SSet.toTop.map i).hom x) := by
  rw [realizedHomotopy_apply]
  have hn := congrArg (fun u => u.hom (x, t)) (comparison_naturality i)
  change (comparison K).hom ((SSet.toTop.map i).hom x, t) =
    (SSet.toTop.map (i ▷ Δ[1])).hom ((comparison A).hom (x, t)) at hn
  rw [hn]
  change ((SSet.toTop.map (i ▷ Δ[1]) ≫ SSet.toTop.map H.h).hom)
    ((comparison A).hom (x, t)) = _
  rw [← SSet.toTop.map_comp, hi, SSet.toTop.map_comp, SSet.toTop.map_comp]
  change (SSet.toTop.map f).hom ((SSet.toTop.map i).hom
    ((SSet.toTop.map (fst A Δ[1])).hom ((comparison A).hom (x, t)))) = _
  rw [comparison_first]

/-- The realized homotopy is relative to the entire image of the specified
    simplicial map; no embedding hypothesis is needed. -/
def homotopyRelOfStationary (H : SSet.Homotopy f g) (i : A ⟶ K)
    (hi : i ▷ Δ[1] ≫ H.h = fst A Δ[1] ≫ i ≫ f) :
    (SSet.toTop.map f).hom.HomotopyRel (SSet.toTop.map g).hom
      (Set.range (SSet.toTop.map i).hom) where
  toHomotopy := homotopy H
  prop' t y hy := by
    obtain ⟨x, rfl⟩ := hy
    exact homotopy_stationary H i hi t x

end

end Thomason.Construction.RealizedCylinder

end

section

/-! # Relative Kan lifts and the actual realization weak test -/

namespace Thomason.Construction

open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open SSet.modelCategoryQuillen
open scoped Simplicial

noncomputable section

/-- Lift a homotopy through a Kan fibration, preserving a prescribed homotopy
on any simplicial subobject. The endpoint commutes strictly with the fibration. -/
theorem exists_kan_relative_homotopy {A K E B : SSet.{0}}
    (i : A ⟶ K) [Mono i] (p : E ⟶ B) [HomotopicalAlgebra.Fibration p]
    (f : K ⟶ E) {a : A ⟶ E} (HA : SSet.Homotopy (i ≫ f) a)
    {g : K ⟶ B} (HB : SSet.Homotopy (f ≫ p) g)
    (hc : HA.h ≫ p = i ▷ Δ[1] ≫ HB.h) :
    ∃ (g' : K ⟶ E) (H : SSet.Homotopy f g'),
      i ▷ Δ[1] ≫ H.h = HA.h ∧ H.h ≫ p = HB.h ∧ g' ≫ p = g := by
  obtain ⟨e, he₀, hei, hep⟩ := exists_kan_cylinder_lift i p f HA.h HB.h
    HA.h₀ hc HB.h₀.symm
  let H : SSet.Homotopy f (SSet.ι₁ ≫ e) := {
    h := e
    h₀ := he₀
    h₁ := rfl
    rel := by
      apply NatTrans.ext
      funext m
      apply ConcreteCategory.hom_ext
      intro x
      exact False.elim x.1.property }
  refine ⟨SSet.ι₁ ≫ e, H, hei, hep, ?_⟩
  rw [Category.assoc, hep, HB.h₁]

/-- The new endpoint in a relative Kan lift has exactly the same actual
realization weak-equivalence status as the initial map. -/
theorem exists_kan_relative_homotopy_weak {A K E B : SSet.{0}}
    (i : A ⟶ K) [Mono i] (p : E ⟶ B) [HomotopicalAlgebra.Fibration p]
    (f : K ⟶ E) {a : A ⟶ E} (HA : SSet.Homotopy (i ≫ f) a)
    {g : K ⟶ B} (HB : SSet.Homotopy (f ≫ p) g)
    (hc : HA.h ≫ p = i ▷ Δ[1] ≫ HB.h) :
    ∃ (g' : K ⟶ E) (H : SSet.Homotopy f g'),
      i ▷ Δ[1] ≫ H.h = HA.h ∧ H.h ≫ p = HB.h ∧ g' ≫ p = g ∧
      (realizationWeakEquivalences f ↔ realizationWeakEquivalences g') := by
  obtain ⟨g', H, hi, hp, hg⟩ := exists_kan_relative_homotopy i p f HA HB hc
  exact ⟨g', H, hi, hp, hg, RealizedCylinder.weakEquivalence_iff H⟩

/-- If the prescribed cylinder is stationary, the lift is stationary on the
entire realized subobject, as an actual relative continuous homotopy. -/
theorem exists_kan_stationary_lift {A K E B : SSet.{0}}
    (i : A ⟶ K) [Mono i] (p : E ⟶ B) [HomotopicalAlgebra.Fibration p]
    (f : K ⟶ E) {g : K ⟶ B} (HB : SSet.Homotopy (f ≫ p) g)
    (hc : i ▷ Δ[1] ≫ HB.h = fst A Δ[1] ≫ i ≫ f ≫ p) :
    ∃ (g' : K ⟶ E) (H : SSet.Homotopy f g'),
      g' ≫ p = g ∧ i ▷ Δ[1] ≫ H.h = fst A Δ[1] ≫ i ≫ f ∧
      Nonempty ((SSet.toTop.map f).hom.HomotopyRel (SSet.toTop.map g').hom
        (Set.range (SSet.toTop.map i).hom)) ∧
      (realizationWeakEquivalences f ↔ realizationWeakEquivalences g') := by
  let HA : SSet.Homotopy (i ≫ f) (i ≫ f) := {
    h := fst A Δ[1] ≫ i ≫ f
    h₀ := by simp
    h₁ := by simp
    rel := by
      apply NatTrans.ext
      funext m
      apply ConcreteCategory.hom_ext
      intro x
      exact False.elim x.1.property }
  have hh : HA.h ≫ p = i ▷ Δ[1] ≫ HB.h := by
    change (fst A Δ[1] ≫ i ≫ f) ≫ p = _
    simpa only [Category.assoc] using hc.symm
  obtain ⟨g', H, hi, _, hg, hw⟩ := exists_kan_relative_homotopy_weak i p f HA HB hh
  exact ⟨g', H, hg, hi, ⟨RealizedCylinder.homotopyRelOfStationary H i hi⟩, hw⟩

end

end Thomason.Construction

end

section

/-! # Exactifying a simplicial relative weak lift through a Kan fibration -/

namespace Thomason.Construction

open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open SSet.modelCategoryQuillen
open scoped Simplicial

noncomputable section

/-- Once a relative approximation is simplicial, the Kan cylinder lifting
property makes its projection exact while retaining the original boundary. -/
theorem exactify_simplicial_relative_lift {A K E B : SSet.{0}}
    (i : A ⟶ K) [Mono i] (p : E ⟶ B) [HomotopicalAlgebra.Fibration p]
    (a : A ⟶ E) (b : K ⟶ B) (d : K ⟶ E) (hd : i ≫ d = a)
    (H : SSet.Homotopy (d ≫ p) b)
    (hH : i ▷ Δ[1] ≫ H.h = fst A Δ[1] ≫ a ≫ p) :
    ∃ l : K ⟶ E, i ≫ l = a ∧ l ≫ p = b := by
  let h : A ⊗ (Δ[1] : SSet.{0}) ⟶ E := fst A Δ[1] ≫ a
  have hzero : SSet.ι₀ ≫ h = i ≫ d := by
    rw [hd]
    simp only [h, ← Category.assoc, SSet.ι₀_fst, Category.id_comp]
  have hp : h ≫ p = i ▷ Δ[1] ≫ H.h := by
    simpa only [h, Category.assoc] using hH.symm
  obtain ⟨e, _, hei, hep⟩ := exists_kan_cylinder_lift i p d h H.h hzero hp H.h₀.symm
  refine ⟨SSet.ι₁ ≫ e, ?_, ?_⟩
  · have hn : i ≫ SSet.ι₁ = SSet.ι₁ ≫ i ▷ (Δ[1] : SSet.{0}) := by
      apply NatTrans.ext
      funext k
      apply ConcreteCategory.hom_ext
      intro x
      rfl
    rw [← Category.assoc, hn, Category.assoc, hei]
    simp only [h, ← Category.assoc, SSet.ι₁_fst, Category.id_comp]
  · rw [Category.assoc, hep, H.h₁]

end

end Thomason.Construction

end

section

/-! # Exact comparison of realized homotopies

Commuting simplicial cylinder squares commute after realization at every
parameter point. Concatenation retains the same pointwise comparison.
-/

namespace Thomason.Construction

open CategoryTheory MonoidalCategory
open scoped Simplicial

noncomputable section

theorem realized_homotopy_square {A K X Y : SSet.{0}}
    {f g : K ⟶ X} {a b : A ⟶ Y}
    (H : SSet.Homotopy f g) (G : SSet.Homotopy a b)
    (i : A ⟶ K) (k : Y ⟶ X) (h : i ▷ Δ[1] ≫ H.h = G.h ≫ k)
    (t : unitInterval) (x : SSet.toTop.obj A) :
    RealizedCylinder.homotopy H (t, (SSet.toTop.map i).hom x) =
      (SSet.toTop.map k).hom (RealizedCylinder.homotopy G (t, x)) := by
  rw [realizedHomotopy_apply, realizedHomotopy_apply]
  have hn := congrArg (fun q => q.hom (x, t)) (RealizedCylinder.comparison_naturality i)
  change (RealizedCylinder.comparison K).hom ((SSet.toTop.map i).hom x, t) =
    (SSet.toTop.map (i ▷ Δ[1])).hom ((RealizedCylinder.comparison A).hom (x, t)) at hn
  rw [hn]
  change (SSet.toTop.map (i ▷ Δ[1]) ≫ SSet.toTop.map H.h).hom
    ((RealizedCylinder.comparison A).hom (x, t)) = _
  rw [← SSet.toTop.map_comp, h, SSet.toTop.map_comp]
  rfl

theorem homotopy_trans_pointwise {X Y Z T : Type}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] [TopologicalSpace T]
    {f₀ f₁ f₂ : C(X, Y)} {g₀ g₁ g₂ : C(Z, T)}
    (H : f₀.Homotopy f₁) (H' : f₁.Homotopy f₂)
    (G : g₀.Homotopy g₁) (G' : g₁.Homotopy g₂)
    (i : Z → X) (k : T → Y)
    (h : ∀ t z, H (t, i z) = k (G (t, z)))
    (h' : ∀ t z, H' (t, i z) = k (G' (t, z)))
    (t : unitInterval) (z : Z) :
    H.trans H' (t, i z) = k (G.trans G' (t, z)) := by
  rw [ContinuousMap.Homotopy.trans_apply, ContinuousMap.Homotopy.trans_apply]
  split_ifs
  · exact h _ z
  · exact h' _ z

end

end Thomason.Construction

end

section

/-! # Exact singular adjunction for higher parameter spaces and their boundaries -/

namespace Thomason.Construction

open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open scoped Simplicial

noncomputable section

/-- Product realization gives an exact singular adjunction for a whole
parameterized family, using the actual canonical product comparison. -/
def singularProductEquiv (K A : SSet.{0}) (X : TopCat.{0})
    [IsIso (realizationProductComparison K A)] :
    (TopCat.of (SSet.toTop.obj K × SSet.toTop.obj A) ⟶ X) ≃
      (K ⊗ A ⟶ TopCat.toSSet.obj X) :=
  (Iso.homCongr (asIso (realizationProductComparison K A)).symm (Iso.refl X)).trans
    (sSetTopAdj.homEquiv _ X)

/-- The forward adjunction is evaluation after the canonical projections. -/
theorem singularProductEquiv_apply (K A : SSet.{0}) (X : TopCat.{0})
    [IsIso (realizationProductComparison K A)]
    (H : TopCat.of (SSet.toTop.obj K × SSet.toTop.obj A) ⟶ X) :
    singularProductEquiv K A X H =
      sSetTopAdj.homEquiv _ X (realizationProductComparison K A ≫ H) := by
  change sSetTopAdj.homEquiv _ X (_ ≫ H ≫ 𝟙 X) = _
  rw [Category.comp_id]
  rfl

/-- Restriction in the higher parameter commutes exactly with the singular
adjunction, including restriction to the entire parameter boundary. -/
theorem singularProductEquiv_restrict (K : SSet.{0}) {A C : SSet.{0}}
    (i : C ⟶ A) (X : TopCat.{0})
    [IsIso (realizationProductComparison K A)] [IsIso (realizationProductComparison K C)]
    (H : TopCat.of (SSet.toTop.obj K × SSet.toTop.obj A) ⟶ X) :
    K ◁ i ≫ singularProductEquiv K A X H =
      singularProductEquiv K C X (realizationProductRightMap K i ≫ H) := by
  rw [singularProductEquiv_apply, singularProductEquiv_apply,
    ← sSetTopAdj.homEquiv_naturality_left, ← Category.assoc,
    realizationProductComparison_naturality_right, Category.assoc]

/-- Postcomposition also commutes exactly with the full singular family. -/
theorem singularProductEquiv_postcomp (K A : SSet.{0}) {X Y : TopCat.{0}}
    [IsIso (realizationProductComparison K A)] (p : X ⟶ Y)
    (H : TopCat.of (SSet.toTop.obj K × SSet.toTop.obj A) ⟶ X) :
    singularProductEquiv K A X H ≫ TopCat.toSSet.map p =
      singularProductEquiv K A Y (H ≫ p) := by
  rw [singularProductEquiv_apply, singularProductEquiv_apply,
    ← sSetTopAdj.homEquiv_naturality_right, Category.assoc]

/-- Recovering a singular family by actual realization and evaluation is
exact on every point of its entire parameter space. -/
theorem singularProductEquiv_evaluate (K A : SSet.{0}) (X : TopCat.{0})
    [IsIso (realizationProductComparison K A)]
    (H : TopCat.of (SSet.toTop.obj K × SSet.toTop.obj A) ⟶ X) :
    inv (realizationProductComparison K A) ≫
      SSet.toTop.map (singularProductEquiv K A X H) ≫ sSetTopAdj.counit.app X = H := by
  rw [singularProductEquiv_apply]
  change inv (realizationProductComparison K A) ≫
    (sSetTopAdj.homEquiv _ X).symm
      ((sSetTopAdj.homEquiv _ X) (realizationProductComparison K A ≫ H)) = H
  rw [Equiv.symm_apply_apply, IsIso.inv_hom_id_assoc]

/-- Higher cubes with arbitrary simplicial parameter spaces admit the
exact adjunction; the inverse retains all continuous family coordinates. -/
def singularCubeProductEquiv (K : SSet.{0}) (n : ℕ) (X : TopCat.{0}) :
    (TopCat.of (SSet.toTop.obj K × SSet.toTop.obj (RealizedCube.obj n)) ⟶ X) ≃
      (K ⊗ RealizedCube.obj n ⟶ TopCat.toSSet.obj X) := by
  have := realizationProductComparison_cube_isIso K n
  exact singularProductEquiv K (RealizedCube.obj n) X

/-- The same exact adjunction holds for the COMPLETE cube boundary. -/
def singularCubeBoundaryProductEquiv (K : SSet.{0}) (n : ℕ) (X : TopCat.{0}) :
    (TopCat.of (SSet.toTop.obj K × SSet.toTop.obj (RealizedCube.boundary n).toSSet) ⟶ X) ≃
      (K ⊗ (RealizedCube.boundary n).toSSet ⟶ TopCat.toSSet.obj X) := by
  have := realizationProductComparison_cubeBoundary_isIso K n
  exact singularProductEquiv K (RealizedCube.boundary n).toSSet X

/-- Restriction from the cube to its complete boundary is exactly the
ordinary continuous boundary restriction under these equivalences. -/
theorem singularCubeProductEquiv_boundary (K : SSet.{0}) (n : ℕ) (X : TopCat.{0})
    (H : TopCat.of (SSet.toTop.obj K × SSet.toTop.obj (RealizedCube.obj (n+1))) ⟶ X) :
    K ◁ (RealizedCube.boundary n).ι ≫ singularCubeProductEquiv K (n+1) X H =
      singularCubeBoundaryProductEquiv K n X
        (realizationProductRightMap K (RealizedCube.boundary n).ι ≫ H) := by
  have := realizationProductComparison_cube_isIso K (n+1)
  have := realizationProductComparison_cubeBoundary_isIso K n
  exact singularProductEquiv_restrict K (RealizedCube.boundary n).ι X H

end

end Thomason.Construction

end

section

/-! # The realization–singular unit on the local models of the main theorem -/

namespace Thomason.Construction

open CategoryTheory
open scoped Simplicial

noncomputable section

/-- The existing explicit greatest-vertex contraction gives contractibility. -/
theorem greatest_poset_realization_contractible {P : Type} [PartialOrder P]
    (v : P) (hv : ∀ x, x ≤ v) : ContractibleSpace (SSet.toTop.obj (nerve P)) :=
  (contractible_iff_id_nullhomotopic _).mpr
    ⟨ConePrism.vertexPoint v, ⟨ConePrism.contraction v hv⟩⟩

/-- Contractibility of each actual realized standard simplex. -/
theorem standard_simplex_realization_contractible (n : ℕ) :
    ContractibleSpace (SSet.toTop.obj (Δ[n] : SSet.{0})) := by
  let := greatest_poset_realization_contractible
    (ULift.up (Fin.last n) : ULift.{0} (Fin (n+1)))
    (fun x => show x.down ≤ Fin.last n from Fin.le_last _)
  exact (TopCat.homeoOfIso (SSet.toTop.mapIso (SSet.stdSimplex.isoNerve n))).contractibleSpace

/-- The adjunction triangle turns a counit weak equivalence into the corresponding unit test. -/
theorem singular_unit_weak_of_counit {K : SSet.{0}}
    (h : topologicalWeakEquivalences (sSetTopAdj.counit.app (SSet.toTop.obj K))) :
    realizationWeakEquivalences (sSetTopAdj.unit.app K) := by
  change topologicalWeakEquivalences (SSet.toTop.map (sSetTopAdj.unit.app K))
  apply topologicalWeakEquivalences.of_postcomp _ _ h
  exact (sSetTopAdj.left_triangle_components K).symm ▸
    topologicalWeakEquivalences.id_mem (SSet.toTop.obj K)

/-- The unit is weak whenever the actual realization is contractible. -/
theorem singular_unit_weak_contractible (K : SSet.{0})
    [ContractibleSpace (SSet.toTop.obj K)] :
    realizationWeakEquivalences (sSetTopAdj.unit.app K) :=
  singular_unit_weak_of_counit (singular_counit_weak_contractible _)

/-- The genuine singular unit of every standard simplex is weak. -/
theorem singular_unit_standard_simplex_weak (n : ℕ) :
    realizationWeakEquivalences (sSetTopAdj.unit.app (Δ[n] : SSet.{0})) := by
  let := standard_simplex_realization_contractible n
  exact singular_unit_weak_contractible _

/-- The same unit test holds on every greatest-element poset nerve used by the main induction. -/
theorem singular_unit_greatest_poset_weak {P : Type} [PartialOrder P]
    (v : P) (hv : ∀ x, x ≤ v) :
    realizationWeakEquivalences (sSetTopAdj.unit.app (nerve P)) := by
  let := greatest_poset_realization_contractible v hv
  exact singular_unit_weak_contractible _

end

end Thomason.Construction

end

section

/-! # Actual weak equivalences and face embeddings of subdivided simplices -/

namespace Thomason.Construction

open CategoryTheory PartialOrder
open scoped Simplicial

noncomputable section

/-- The full vertex set is the greatest vertex in a subdivided simplex. -/
def totalVertexChain (n : ℕ) : NonemptyFiniteChains (ULift.{0} (Fin (n+1))) where
  finset := Finset.univ
  nonempty := Finset.univ_nonempty
  comparable _ _ := le_total _ _

theorem le_totalVertexChain (n : ℕ) (s : NonemptyFiniteChains (ULift.{0} (Fin (n+1)))) :
    s ≤ totalVertexChain n := Finset.subset_univ _

/-- Every actual simplicial map between two standard simplices is weak. -/
theorem standard_simplex_hom_weak {m n : SimplexCategory}
    (f : SSet.stdSimplex.{0}.obj m ⟶ SSet.stdSimplex.obj n) :
    realizationWeakEquivalences f := by
  rw [← SSet.stdSimplex.map_preimage f]
  exact realized_simplex_map_weak _

/-- On each standard simplex, last vertex is weak by the actual contraction
of its finite-chain nerve onto its greatest vertex. -/
theorem simplexLastVertex_weak (n : SimplexCategory) :
    realizationWeakEquivalences (simplexLastVertex.{0}.app n) := by
  let v := (ConePrism.vertexIndex (totalVertexChain n.len)).hom
  have hv : realizationWeakEquivalences v :=
    ConePrism.greatest_vertex_weak _ (le_totalVertexChain n.len)
  apply realizationWeakEquivalences.of_precomp v _ hv
  exact standard_simplex_hom_weak _

/-- The same result expressed using the original subdivision functor. -/
theorem lastVertex_standard_weak (n : SimplexCategory) :
    realizationWeakEquivalences (lastVertex.app (SSet.stdSimplex.{0}.obj n)) := by
  apply realizationWeakEquivalences.of_precomp (SSet.stdSimplex.sdIso.inv.app n) _
    (realizationWeakEquivalences.of_isIso _)
  rw [lastVertex_on_standard_simplex]
  exact simplexLastVertex_weak n

/-- Injective vertex maps remain injective on finite nonempty chains. -/
theorem finiteChain_map_injective {P Q : Type} [PartialOrder P] [PartialOrder Q]
    (f : P →o Q) (hf : Function.Injective f) :
    Function.Injective (NonemptyFiniteChains.orderHomMap f) := by
  classical
  intro a b hab
  apply NonemptyFiniteChains.ext
  exact (Finset.image_injective hf) (congrArg NonemptyFiniteChains.finset hab)

/-- The finite-chain nerve of a simplex preserves every face embedding. -/
theorem simplexSubdivision_map_mono {m n : SimplexCategory} (f : m ⟶ n) [Mono f] :
    Mono (SimplexCategory.sd.{0}.map f) := by
  let F : ULift.{0} (Fin (m.len+1)) →o ULift.{0} (Fin (n.len+1)) :=
    (SimplexCategory.toPartOrd.map f).hom
  have hF : Function.Injective F := by
    intro x y hxy
    apply ULift.ext
    exact SimplexCategory.mono_iff_injective.mp (inferInstance : Mono f)
      (congrArg ULift.down hxy)
  rw [NatTrans.mono_iff_mono_app]
  intro d
  apply (CategoryTheory.mono_iff_injective _).mpr
  intro x y hxy
  apply nerve.ext_of_isThin
  funext i
  exact finiteChain_map_injective F hF (congrArg (fun z => z.obj i) hxy)

/-- On the original left-Kan-extension subdivision functor, every standard
face inclusion is still an actual simplicial monomorphism. -/
theorem subdivision_standard_map_mono {m n : SimplexCategory} (f : m ⟶ n) [Mono f] :
    Mono (SSet.sd.map (SSet.stdSimplex.{0}.map f)) := by
  have := simplexSubdivision_map_mono f
  have : Mono (SSet.stdSimplex.sdIso.hom.app m ≫ SimplexCategory.sd.map f) := inferInstance
  exact mono_of_mono_fac (SSet.stdSimplex.sdIso.hom.naturality f)

end

end Thomason.Construction

end

section

/-! # Exact images of subdivided faces

A subdivided face consists of the chains supported on its original vertices.
The statement includes all simplicial degrees, and hence computes actual
intersections of the face images used in boundary gluing.
-/

namespace Thomason.Construction

open CategoryTheory PartialOrder

noncomputable section

variable {P Q : Type} [PartialOrder P] [PartialOrder Q]

/-- Chains whose original vertices all belong to a specified set. -/
def chainsSupported (A : Set P) : Set (NonemptyFiniteChains P) :=
  {s | ∀ x ∈ s.finset, x ∈ A}

theorem chainsSupported_isLowerSet (A : Set P) : IsLowerSet (chainsSupported A) :=
  fun _ _ h hs x hx => hs x (h hx)

theorem chainsSupported_inter (A B : Set P) :
    chainsSupported (A ∩ B) = chainsSupported A ∩ chainsSupported B := by
  ext s
  exact ⟨fun h => ⟨fun x hx => (h x hx).1, fun x hx => (h x hx).2⟩,
    fun h x hx => ⟨h.1 x hx, h.2 x hx⟩⟩

/-- Pull a supported finite chain back through its original order embedding. -/
def finiteChainPreimage (f : P ↪o Q) (s : NonemptyFiniteChains Q)
    (hs : s ∈ chainsSupported (Set.range f)) : NonemptyFiniteChains P where
  finset := s.finset.preimage f f.injective.injOn
  nonempty := by
    obtain ⟨y, hy⟩ := s.nonempty
    obtain ⟨x, rfl⟩ := hs y hy
    exact ⟨x, Finset.mem_preimage.mpr hy⟩
  comparable a b := by
    have ha := Finset.mem_preimage.mp a.property
    have hb := Finset.mem_preimage.mp b.property
    exact (s.comparable ⟨f a.val, ha⟩ ⟨f b.val, hb⟩).imp
      (fun h => f.le_iff_le.mp h) (fun h => f.le_iff_le.mp h)

theorem finiteChainPreimage_map (f : P ↪o Q) (s : NonemptyFiniteChains Q)
    (hs : s ∈ chainsSupported (Set.range f)) :
    (finiteChainPreimage f s hs).map f.toOrderHom = s := by
  classical
  apply NonemptyFiniteChains.ext
  ext y
  constructor
  · intro hy
    obtain ⟨x, hx, rfl⟩ := (NonemptyFiniteChains.mem_map_iff _ _ _).mp hy
    change f x ∈ s.finset
    simpa only [finiteChainPreimage, Finset.mem_preimage] using hx
  · intro hy
    obtain ⟨x, rfl⟩ := hs y hy
    exact (NonemptyFiniteChains.mem_map_iff _ _ _).mpr
      ⟨x, (Finset.mem_preimage (hf := f.injective.injOn)).mpr hy, rfl⟩

theorem finiteChainPreimage_mono (f : P ↪o Q)
    {s t : NonemptyFiniteChains Q}
    (hs : s ∈ chainsSupported (Set.range f))
    (ht : t ∈ chainsSupported (Set.range f)) (h : s ≤ t) :
    finiteChainPreimage f s hs ≤ finiteChainPreimage f t ht := by
  intro x hx
  change x ∈ t.finset.preimage f f.injective.injOn
  change x ∈ s.finset.preimage f f.injective.injOn at hx
  exact Finset.mem_preimage.mpr (h (Finset.mem_preimage.mp hx))

theorem finiteChain_map_supported (f : P ↪o Q) (s : NonemptyFiniteChains P) :
    s.map f.toOrderHom ∈ chainsSupported (Set.range f) := by
  intro y hy
  obtain ⟨x, _, rfl⟩ := (NonemptyFiniteChains.mem_map_iff _ _ _).mp hy
  exact ⟨x, rfl⟩

/-- Exact image of the nerve map on finite chains, not merely its vertices. -/
theorem finiteChain_nerve_range (f : P ↪o Q) :
    SSet.Subcomplex.range
      (nerveMap (NonemptyFiniteChains.orderHomMap f.toOrderHom).monotone.functor) =
      fullSubposetComplex (chainsSupported (Set.range f)) := by
  ext d s
  constructor
  · rintro ⟨t, rfl⟩ i
    exact finiteChain_map_supported f (t.obj i)
  · intro hs
    let t : (nerve (NonemptyFiniteChains P)).obj d :=
      { obj i := finiteChainPreimage f (s.obj i) (hs i)
        map {i j} u := homOfLE
          (finiteChainPreimage_mono f (hs i) (hs j) (leOfHom (s.map u))) }
    refine ⟨t, ?_⟩
    apply nerve.ext_of_isThin
    funext i
    exact finiteChainPreimage_map f (s.obj i) (hs i)

/-- The chain nerve preserves intersections of original vertex images. -/
theorem finiteChain_nerve_range_inter {R : Type} [PartialOrder R]
    (f : P ↪o Q) (g : R ↪o Q) :
    SSet.Subcomplex.range
        (nerveMap (NonemptyFiniteChains.orderHomMap f.toOrderHom).monotone.functor) ⊓
      SSet.Subcomplex.range
        (nerveMap (NonemptyFiniteChains.orderHomMap g.toOrderHom).monotone.functor) =
      fullSubposetComplex (chainsSupported (Set.range f ∩ Set.range g)) := by
  rw [finiteChain_nerve_range, finiteChain_nerve_range, ← fullSubposetComplex_inter,
    ← chainsSupported_inter]

/-- The exact face-image description for the actual simplex subdivision. -/
theorem simplexSubdivision_map_range {m n : SimplexCategory} (f : m ⟶ n) [Mono f] :
    SSet.Subcomplex.range (SimplexCategory.sd.{0}.map f) =
      fullSubposetComplex (chainsSupported
        (Set.range (fun x : ULift.{0} (Fin (m.len + 1)) =>
          (ULift.up (f.toOrderHom x.down) : ULift.{0} (Fin (n.len + 1)))))) := by
  let F : ULift.{0} (Fin (m.len + 1)) ↪o ULift.{0} (Fin (n.len + 1)) :=
    { toFun x := ULift.up (f.toOrderHom x.down)
      inj' := by
        intro x y h
        apply ULift.ext
        exact SimplexCategory.mono_iff_injective.mp (inferInstance : Mono f)
          (congrArg ULift.down h)
      map_rel_iff' := by
        intro x y
        change f.toOrderHom x.down ≤ f.toOrderHom y.down ↔ x.down ≤ y.down
        exact (f.toOrderHom.monotone.strictMono_of_injective
          (SimplexCategory.mono_iff_injective.mp (inferInstance : Mono f))).le_iff_le }
  exact finiteChain_nerve_range F

end

end Thomason.Construction

end

end OAI
