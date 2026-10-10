import OAI.CategoryTheory.Thomason.Gray.GrayChainGlobeRestriction
import OAI.CategoryTheory.Thomason.Gray.SimplexCylinderGeneration
import OAI.CategoryTheory.Thomason.Gray.SingularCylinderEquivalence
import OAI.CategoryTheory.Thomason.Simplicial.NonsingularFaceCarriers
import OAI.CategoryTheory.Thomason.Simplicial.SimplexCubeRetract
import OAI.CategoryTheory.Thomason.Simplicial.SingularKanComplex
import OAI.CategoryTheory.Thomason.Simplicial.SubdivisionFaceImages
import OAI.CategoryTheory.Thomason.Simplicial.TruncationCongruence
import Mathlib.AlgebraicTopology.SimplicialSet.FiniteProd
import Mathlib.CategoryTheory.Monoidal.Closed.FunctorToTypes
import Mathlib.Topology.CompactOpen

namespace OAI

section

/-! # Constructed oriental comparison and actual cylinder weak equivalence

Finite positive-chain decomposition gives the atom-generation property
for the oriental comparison. The normalized chain identities hold for the
simplex complexes.
-/

namespace Thomason.Construction.NormalizedSimplexIdentities

open CategoryTheory _root_.OAI.Thomason.Construction.DirectedComplex

noncomputable section

/-- The actual orientals abelianize naturally to the normalized simplex
complexes, without a separate published generation premise. -/
def orientalAbelianizationIso (h : NormalizedSimplexIdentities) :
    h.cosimplicial ⋙ StrictOmegaCategory.Abelianization.functor ≅
      h.chainCosimplicial :=
  (simplexAtoms h).abelianizationCosimplicialIso

/-- The simplex comparison with the global chain model follows
from normalized simplex identities. -/
def constructedChainModelComparison (h : NormalizedSimplexIdentities) :
    h.cylinderCosimplicial ≅
      h.cosimplicial ⋙ StrictOmegaCategory.GrayChainExtension.model :=
  (simplexAtoms h).chainModelComparison

theorem constructedChainModelComparison_endpoint (h : NormalizedSimplexIdentities)
    (side : Bool) (m : SimplexCategory) :
    (h.cylinderEndpoint side).app m ≫ h.constructedChainModelComparison.hom.app m =
      (StrictOmegaCategory.GrayChainExtension.modelEndpoint side).app (h.object m.len) :=
  (simplexAtoms h).chainModelComparison_endpoint side m

/-- Projection from every concrete positive-chain cylinder is an actual
Street-nerve realization weak equivalence, with no Gray or model-structure
input and no atom-generation assumption. -/
theorem chainCylinder_projection_weak (h : NormalizedSimplexIdentities)
    (K : DirectedComplex.{0}) :
    h.streetWeakEquivalences (RightCylinder.projection K).realization :=
  (simplexAtoms h).chainCylinder_projection_weak K

end

end Thomason.Construction.NormalizedSimplexIdentities

end

section

/-! # Homotopy extension for actual realized simplicial subobjects

Singular Kan lifting and the exact cylinder evaluation extend continuous
homotopies. This does not use weak equivalences of the unit or counit.
-/

namespace Thomason.Construction

open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open scoped Simplicial

noncomputable section

/-- Every realized simplicial monomorphism has the homotopy extension property,
with the prescribed homotopy retained pointwise on the entire subobject. -/
theorem realization_homotopy_extension {A K : SSet.{0}} {X : TopCat.{0}}
    (i : A ⟶ K) [Mono i] (f : SSet.toTop.obj K ⟶ X)
    {g : SSet.toTop.obj A ⟶ X}
    (H : (SSet.toTop.map i ≫ f).hom.Homotopy g.hom) :
    ∃ F : C(unitInterval × SSet.toTop.obj K, X),
      (∀ x, F (0, x) = f.hom x) ∧
      ∀ t x, F (t, (SSet.toTop.map i).hom x) = H (t, x) := by
  let a := sSetTopAdj.homEquiv K X f
  let h := sSetTopAdj.unit.app A ▷ Δ[1] ≫ (singularHomotopy H).h
  have h₀ : SSet.ι₀ ≫ h = i ≫ a := by
    dsimp only [h]
    rw [← Category.assoc, SSet.ι₀_comp, Category.assoc, SSet.Homotopy.h₀]
    change sSetTopAdj.unit.app A ≫ TopCat.toSSet.map (SSet.toTop.map i ≫ f) =
      i ≫ (sSetTopAdj.unit.app K ≫ TopCat.toSSet.map f)
    rw [TopCat.toSSet.map_comp, ← Category.assoc]
    exact congrArg (fun k => k ≫ TopCat.toSSet.map f) (sSetTopAdj.unit.naturality i).symm
  let := singular_kan X
  obtain ⟨e, he₀, hei⟩ := exists_kan_homotopy_extension i a h h₀
  refine ⟨evaluateSingularCylinder e, ?_, ?_⟩
  · intro x
    rw [evaluateSingularCylinder_zero, he₀]
    exact congrArg (fun k => k.hom x) ((sSetTopAdj.homEquiv K X).symm_apply_apply f)
  · intro t x
    rw [evaluateSingularCylinder_naturality, hei]
    exact evaluateSingularCylinder_unit H t x

/-- The extension may be packaged as a continuous homotopy with its endpoint. -/
theorem realization_homotopy_extension_endpoint {A K : SSet.{0}} {X : TopCat.{0}}
    (i : A ⟶ K) [Mono i] (f : SSet.toTop.obj K ⟶ X)
    {g : SSet.toTop.obj A ⟶ X}
    (H : (SSet.toTop.map i ≫ f).hom.Homotopy g.hom) :
    ∃ (g' : SSet.toTop.obj K ⟶ X) (H' : f.hom.Homotopy g'.hom),
      ∀ t x, H' (t, (SSet.toTop.map i).hom x) = H (t, x) := by
  obtain ⟨F, hF₀, hFi⟩ := realization_homotopy_extension i f H
  let g' : SSet.toTop.obj K ⟶ X := TopCat.ofHom
    ⟨fun x => F (1, x), F.continuous.comp (by fun_prop)⟩
  let H' : f.hom.Homotopy g'.hom := {
    toContinuousMap := F
    map_zero_left := hF₀
    map_one_left := fun _ => rfl }
  exact ⟨g', H', hFi⟩

end

end Thomason.Construction

end

section

/-! # Homotopy extension from two opposite faces of an actual cube boundary -/

namespace Thomason.Construction.RealizedCube

open CategoryTheory Topology
open scoped Simplicial

noncomputable section

/-- The two faces perpendicular to the first coordinate. -/
def oppositeFaces (n : ℕ) : (obj (n+1)).Subcomplex :=
  ⨆ e : Bool, SSet.Subcomplex.range (face n 0 e)

theorem oppositeFaces_le_boundary (n : ℕ) : oppositeFaces n ≤ boundary n := by
  apply iSup_le
  intro e
  exact le_iSup_of_le (0, e) le_rfl

def oppositeFacesInclusion (n : ℕ) :
    (oppositeFaces n : SSet.{0}) ⟶ (boundary n : SSet.{0}) :=
  SSet.Subcomplex.homOfLE (oppositeFaces_le_boundary n)

instance oppositeFacesInclusion_mono (n : ℕ) : Mono (oppositeFacesInclusion n) := by
  unfold oppositeFacesInclusion
  infer_instance

theorem oppositeFaces_coordinate (n : ℕ)
    (x : SSet.toTop.obj (oppositeFaces n : SSet.{0})) :
    coordinates (n+1) ((SSet.toTop.map (oppositeFaces n).ι).hom x) 0 = 0 ∨
      coordinates (n+1) ((SSet.toTop.map (oppositeFaces n).ι).hom x) 0 = 1 := by
  have hx : (SSet.toTop.map (oppositeFaces n).ι).hom x ∈
      Set.range (SSet.toTop.map (oppositeFaces n).ι).hom := ⟨x, rfl⟩
  have hr : Set.range (SSet.toTop.map (oppositeFaces n).ι).hom =
      ⋃ e : Bool, Set.range (SSet.toTop.map (face n 0 e)).hom := by
    change Set.range (SSet.toTop.map (iSup (fun e : Bool =>
      SSet.Subcomplex.range (face n 0 e))).ι).hom = _
    rw [RealizationPrism.range_iSup_inclusion]
    congr 1
    funext e
    exact (RealizationPrism.range_realized_map (face n 0 e)).symm
  rw [hr] at hx
  obtain ⟨e, z, hz⟩ := Set.mem_iUnion.mp hx
  rw [← hz, coordinates_face, Fin.insertNth_apply_same]
  cases e <;> simp [endpoint]

/-- Contract the remaining coordinates without leaving either opposite face. -/
def oppositeFacesContraction (n : ℕ) :
    C(unitInterval × SSet.toTop.obj (oppositeFaces n : SSet.{0}),
      SSet.toTop.obj (boundary n : SSet.{0})) :=
  (boundarySection n).comp {
    toFun z := ⟨Fin.cons
      (coordinates (n+1) ((SSet.toTop.map (oppositeFaces n).ι).hom z.2) 0)
      (fun i => unitInterval.symm z.1 *
        coordinates (n+1) ((SSet.toTop.map (oppositeFaces n).ι).hom z.2) i.succ),
      ⟨0, oppositeFaces_coordinate n z.2⟩⟩
    continuous_toFun := by fun_prop }

theorem oppositeFacesContraction_zero (n : ℕ)
    (x : SSet.toTop.obj (oppositeFaces n : SSet.{0})) :
    oppositeFacesContraction n (0, x) =
      (SSet.toTop.map (oppositeFacesInclusion n)).hom x := by
  apply (RealizationPrism.inclusion_isClosedEmbedding (obj (n+1)) (boundary n)).injective
  change (SSet.toTop.map (boundary n).ι).hom (boundarySection n _) = _
  rw [boundarySection_inclusion]
  have he : (SSet.toTop.map (oppositeFacesInclusion n) ≫
      SSet.toTop.map (boundary n).ι) = SSet.toTop.map (oppositeFaces n).ι := by
    rw [← SSet.toTop.map_comp]
    rfl
  have hx := congrArg (fun f => f.hom x) he
  change sectionMap (n+1) (Fin.cons
    (coordinates (n+1) ((SSet.toTop.map (oppositeFaces n).ι).hom x) 0)
    (fun i => unitInterval.symm 0 *
      coordinates (n+1) ((SSet.toTop.map (oppositeFaces n).ι).hom x) i.succ)) = _
  have hc : Fin.cons
      (coordinates (n+1) ((SSet.toTop.map (oppositeFaces n).ι).hom x) 0)
      (fun i => unitInterval.symm 0 *
        coordinates (n+1) ((SSet.toTop.map (oppositeFaces n).ι).hom x) i.succ) =
      coordinates (n+1) ((SSet.toTop.map (oppositeFaces n).ι).hom x) := by
    funext i
    cases i using Fin.cases <;> simp
  rw [hc]
  exact (section_coordinates (n+1) ((SSet.toTop.map (oppositeFaces n).ι).hom x)).trans hx.symm

/-- The literal face point in the full cube boundary. -/
def boundaryFacePoint (n : ℕ) (e : Bool) (u : Fin n → unitInterval) :
    Cube.boundary (Fin (n+1)) :=
  ⟨Fin.cons (endpoint e) u, ⟨0, by cases e <;> simp [endpoint]⟩⟩

theorem boundaryFacePoint_mem_oppositeFaces (n : ℕ) (e : Bool)
    (u : Fin n → unitInterval) :
    ∃ x : SSet.toTop.obj (oppositeFaces n : SSet.{0}),
      (SSet.toTop.map (oppositeFacesInclusion n)).hom x =
        boundarySection n (boundaryFacePoint n e u) := by
  have hm : sectionMap (n+1) (Fin.cons (endpoint e) u) ∈
      Set.range (SSet.toTop.map (oppositeFaces n).ι).hom := by
    have hr := RealizationPrism.range_iSup_inclusion (obj (n+1))
      (fun e : Bool => SSet.Subcomplex.range (face n 0 e))
    change Set.range (SSet.toTop.map (oppositeFaces n).ι).hom = _ at hr
    rw [hr]
    apply Set.mem_iUnion.mpr
    refine ⟨e, ?_⟩
    rw [← RealizationPrism.range_realized_map]
    refine ⟨sectionMap n u, ?_⟩
    simpa only [Fin.insertNth_zero'] using (section_face n 0 e u).symm
  obtain ⟨x, hx⟩ := hm
  refine ⟨x, ?_⟩
  apply (RealizationPrism.inclusion_isClosedEmbedding (obj (n+1)) (boundary n)).injective
  rw [boundarySection_inclusion]
  have he : oppositeFacesInclusion n ≫ (boundary n).ι = (oppositeFaces n).ι := rfl
  have hm := SSet.toTop.congr_map he
  rw [SSet.toTop.map_comp] at hm
  have ht := congrArg (fun f => f.hom x) hm
  exact ht.trans hx

theorem oppositeFacesContraction_one (n : ℕ) (e : Bool)
    (u : Fin n → unitInterval) (x : SSet.toTop.obj (oppositeFaces n : SSet.{0}))
    (hx : (SSet.toTop.map (oppositeFacesInclusion n)).hom x =
      boundarySection n (boundaryFacePoint n e u)) :
    oppositeFacesContraction n (1, x) =
      boundarySection n (boundaryFacePoint n e (fun _ => 0)) := by
  have he : oppositeFacesInclusion n ≫ (boundary n).ι = (oppositeFaces n).ι := rfl
  have hm := SSet.toTop.congr_map he
  rw [SSet.toTop.map_comp] at hm
  have ht := congrArg (fun f => f.hom x) hm
  change (SSet.toTop.map (boundary n).ι).hom
      ((SSet.toTop.map (oppositeFacesInclusion n)).hom x) = _ at ht
  rw [hx, boundarySection_inclusion] at ht
  have hc := congrArg (fun z => coordinates (n+1) z 0) ht
  rw [coordinates_section] at hc
  change endpoint e = _ at hc
  apply congrArg (boundarySection n)
  apply Subtype.ext
  change (Fin.cons (coordinates (n+1)
    ((SSet.toTop.map (oppositeFaces n).ι).hom x) 0)
    (fun i : Fin n => unitInterval.symm 1 * coordinates (n+1)
      ((SSet.toTop.map (oppositeFaces n).ι).hom x) i.succ) :
        Fin (n+1) → unitInterval) = Fin.cons (endpoint e) (fun _ => 0)
  rw [← hc]
  funext i
  cases i using Fin.cases <;> simp

end

end Thomason.Construction.RealizedCube

end

section

/-! # Normalize opposite faces of an arbitrary cubical boundary map -/

namespace Thomason.Construction.RealizedCube

open CategoryTheory

noncomputable section

/-- Any boundary map can be homotoped so that each of its two opposite
faces is constant. The two constants are its original corner values. -/
theorem boundary_normalization {X : TopCat.{0}} (n : ℕ)
    (a : C(Cube.boundary (Fin (n+1)), X)) :
    ∃ F : C(unitInterval × Cube.boundary (Fin (n+1)), X),
      (∀ x, F (0, x) = a x) ∧
      ∀ (e : Bool) (u : Fin n → unitInterval),
        F (1, boundaryFacePoint n e u) =
          a (boundaryFacePoint n e (fun _ => 0)) := by
  let f : SSet.toTop.obj (boundary n : SSet.{0}) ⟶ X :=
    TopCat.ofHom (a.comp (boundaryCoordinates n))
  let g : SSet.toTop.obj (oppositeFaces n : SSet.{0}) ⟶ X :=
    TopCat.ofHom ⟨fun x => f.hom (oppositeFacesContraction n (1, x)), by fun_prop⟩
  let H : (SSet.toTop.map (oppositeFacesInclusion n) ≫ f).hom.Homotopy g.hom := {
    toFun z := f.hom (oppositeFacesContraction n z)
    continuous_toFun := f.hom.continuous.comp (oppositeFacesContraction n).continuous
    map_zero_left x := by
      rw [oppositeFacesContraction_zero]
      rfl
    map_one_left _ := rfl }
  obtain ⟨F, hF₀, hFA⟩ := realization_homotopy_extension (oppositeFacesInclusion n) f H
  let F' : C(unitInterval × Cube.boundary (Fin (n+1)), X) :=
    F.comp ⟨fun z => (z.1, boundarySection n z.2), by fun_prop⟩
  refine ⟨F', ?_, ?_⟩
  · intro x
    change F (0, boundarySection n x) = a x
    rw [hF₀]
    change a (boundaryCoordinates n (boundarySection n x)) = a x
    rw [boundaryCoordinates_section]
  · intro e u
    obtain ⟨x, hx⟩ := boundaryFacePoint_mem_oppositeFaces n e u
    change F (1, boundarySection n (boundaryFacePoint n e u)) = _
    rw [← hx, hFA]
    change f.hom (oppositeFacesContraction n (1, x)) = _
    rw [oppositeFacesContraction_one n e u x hx]
    change a (boundaryCoordinates n (boundarySection n _)) = _
    rw [boundaryCoordinates_section]

/-- Normalize a complete lifting square while retaining a homotopy of the
base cube compatible with the prescribed boundary at every time. -/
theorem boundary_square_normalization {X Y : TopCat.{0}} (p : X ⟶ Y) (n : ℕ)
    (a : C(Cube.boundary (Fin (n+1)), X))
    (b : C(Fin (n+1) → unitInterval, Y))
    (hab : ∀ z, p.hom (a z) = b z.val) :
    ∃ (F : C(unitInterval × Cube.boundary (Fin (n+1)), X))
      (B : C(unitInterval × (Fin (n+1) → unitInterval), Y)),
      (∀ z, F (0, z) = a z) ∧ (∀ z, B (0, z) = b z) ∧
      (∀ t z, p.hom (F (t, z)) = B (t, z.val)) ∧
      ∀ (e : Bool) (u : Fin n → unitInterval),
        F (1, boundaryFacePoint n e u) =
          a (boundaryFacePoint n e (fun _ => 0)) := by
  obtain ⟨F, hF₀, hFe⟩ := boundary_normalization n a
  let f : SSet.toTop.obj (obj (n+1)) ⟶ Y := TopCat.ofHom (b.comp (coordinates (n+1)))
  let g : SSet.toTop.obj (boundary n : SSet.{0}) ⟶ Y :=
    TopCat.ofHom ⟨fun z => p.hom (F (1, boundaryCoordinates n z)), by fun_prop⟩
  let H : (SSet.toTop.map (boundary n).ι ≫ f).hom.Homotopy g.hom := {
    toFun z := p.hom (F (z.1, boundaryCoordinates n z.2))
    continuous_toFun := by fun_prop
    map_zero_left z := by
      rw [hF₀, hab]
      rfl
    map_one_left _ := rfl }
  obtain ⟨B, hB₀, hBs⟩ := realization_homotopy_extension (boundary n).ι f H
  let B' : C(unitInterval × (Fin (n+1) → unitInterval), Y) :=
    B.comp ⟨fun z => (z.1, sectionMap (n+1) z.2), by fun_prop⟩
  refine ⟨F, B', hF₀, ?_, ?_, hFe⟩
  · intro z
    change B (0, sectionMap (n+1) z) = b z
    rw [hB₀]
    change b (coordinates (n+1) (sectionMap (n+1) z)) = b z
    rw [coordinates_section]
  · intro t z
    change p.hom (F (t, z)) = B (t, sectionMap (n+1) z.val)
    rw [← boundarySection_inclusion n z, hBs]
    change p.hom (F (t, z)) = p.hom (F (t, boundaryCoordinates n (boundarySection n z)))
    rw [boundaryCoordinates_section]

end

end Thomason.Construction.RealizedCube

end

section

/-! # Exact adjunction compatibility for realized simplicial homotopies -/

namespace Thomason.Construction

open CategoryTheory

noncomputable section

/-- Realizing a simplicial homotopy and then taking its singular cylinder
adjoint agrees exactly with postcomposing the original homotopy by the unit. -/
theorem singularCylinderMap_realizedHomotopy {K L : SSet.{0}} {f g : K ⟶ L}
    (H : SSet.Homotopy f g) :
    singularCylinderMap (RealizedCylinder.homotopy H).toContinuousMap =
      H.h ≫ sSetTopAdj.unit.app L := by
  apply evaluateSingularCylinder_injective
  apply ContinuousMap.ext
  rintro ⟨t, x⟩
  rw [evaluate_singularCylinderMap]
  change RealizedCylinder.homotopy H (t, x) = _
  rw [realizedHomotopy_apply]
  change (SSet.toTop.map H.h).hom ((RealizedCylinder.comparison K).hom (x, t)) =
    (sSetTopAdj.counit.app (SSet.toTop.obj L)).hom
      ((SSet.toTop.map (H.h ≫ sSetTopAdj.unit.app L)).hom
        ((RealizedCylinder.comparison K).hom (x, t)))
  rw [SSet.toTop.map_comp]
  have ht := congrArg (fun k => k.hom
    ((SSet.toTop.map H.h).hom ((RealizedCylinder.comparison K).hom (x, t))))
      (sSetTopAdj.left_triangle_components L)
  exact ht.symm

end

end Thomason.Construction

end

section

/-! # The continuous/singular adjunction retains exact relative homotopies -/

namespace Thomason.Construction

open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open scoped Simplicial

noncomputable section

/-- An arbitrary continuous homotopy on a realization has a simplicial
adjoint, with its two specified adjoint endpoint maps. -/
def adjointRealizationHomotopy {K : SSet.{0}} {X : TopCat.{0}}
    {f g : SSet.toTop.obj K ⟶ X} (H : f.hom.Homotopy g.hom) :
    SSet.Homotopy (sSetTopAdj.homEquiv K X f) (sSetTopAdj.homEquiv K X g) where
  h := singularCylinderMap H.toContinuousMap
  h₀ := by
    change SSet.ι₀ ≫ singularCylinderMap H.toContinuousMap = sSetTopAdj.homEquiv K X f
    apply (sSetTopAdj.homEquiv K X).symm.injective
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro x
    rw [Equiv.symm_apply_apply, ← evaluateSingularCylinder_zero,
      evaluate_singularCylinderMap]
    exact H.apply_zero x
  h₁ := by
    change SSet.ι₁ ≫ singularCylinderMap H.toContinuousMap = sSetTopAdj.homEquiv K X g
    apply (sSetTopAdj.homEquiv K X).symm.injective
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro x
    rw [Equiv.symm_apply_apply, ← evaluateSingularCylinder_one,
      evaluate_singularCylinderMap]
    exact H.apply_one x
  rel := by
    apply NatTrans.ext
    funext d
    apply ConcreteCategory.hom_ext
    intro z
    exact False.elim z.1.property

/-- A constant cylinder is adjoint to the constant simplicial cylinder,
including all higher simplices. -/
theorem evaluateSingularCylinder_constant {K : SSet.{0}} {X : TopCat.{0}}
    (f : K ⟶ TopCat.toSSet.obj X) (t : unitInterval) (x : SSet.toTop.obj K) :
    evaluateSingularCylinder (fst K (Δ[1] : SSet.{0}) ≫ f) (t, x) =
      ((sSetTopAdj.homEquiv K X).symm f).hom x := by
  change (sSetTopAdj.counit.app X).hom
    ((SSet.toTop.map (fst K Δ[1] ≫ f)).hom ((RealizedCylinder.comparison K).hom (x,t))) = _
  rw [SSet.toTop.map_comp]
  change (sSetTopAdj.counit.app X).hom ((SSet.toTop.map f).hom
    ((SSet.toTop.map (fst K Δ[1])).hom ((RealizedCylinder.comparison K).hom (x,t)))) = _
  rw [RealizedCylinder.comparison_first]
  rfl

/-- Stationarity on the entire realized image is retained exactly by the
adjoint cylinder. No monomorphism or weak equivalence hypothesis is needed. -/
theorem adjointRealizationHomotopy_stationary {A K : SSet.{0}} {X : TopCat.{0}}
    (i : A ⟶ K) {f g : SSet.toTop.obj K ⟶ X}
    (H : f.hom.HomotopyRel g.hom (Set.range (SSet.toTop.map i).hom)) :
    i ▷ Δ[1] ≫ (adjointRealizationHomotopy H.toHomotopy).h =
      fst A Δ[1] ≫ i ≫ sSetTopAdj.homEquiv K X f := by
  apply evaluateSingularCylinder_injective
  apply ContinuousMap.ext
  rintro ⟨t, x⟩
  rw [← evaluateSingularCylinder_naturality]
  change evaluateSingularCylinder (singularCylinderMap H.toContinuousMap)
      (t, (SSet.toTop.map i).hom x) = _
  rw [evaluate_singularCylinderMap, evaluateSingularCylinder_constant]
  have hn : (sSetTopAdj.homEquiv A X).symm (i ≫ sSetTopAdj.homEquiv K X f) =
      SSet.toTop.map i ≫ f := by
    rw [← sSetTopAdj.homEquiv_naturality_left, Equiv.symm_apply_apply]
  rw [hn]
  exact H.eq_fst t ⟨x, rfl⟩

/-- The adjoint of a realized map is its original map followed by the
actual realization/singular unit. -/
theorem adjoint_realized_map {A X : SSet.{0}} (a : A ⟶ X) :
    sSetTopAdj.homEquiv A (SSet.toTop.obj X) (SSet.toTop.map a) =
      a ≫ sSetTopAdj.unit.app X := by
  change sSetTopAdj.homEquiv A (SSet.toTop.obj X) (SSet.toTop.map a) =
    a ≫ sSetTopAdj.homEquiv X (SSet.toTop.obj X) (𝟙 _)
  rw [← sSetTopAdj.homEquiv_naturality_left, Category.comp_id]

/-- An exact continuous relative extension gives an exact singular relative
extension. The original simplicial boundary is preserved after the unit. -/
theorem adjoint_relative_extension {A K X : SSet.{0}} (i : A ⟶ K) (a : A ⟶ X)
    (c : SSet.toTop.obj K ⟶ SSet.toTop.obj X)
    (hc : SSet.toTop.map i ≫ c = SSet.toTop.map a) :
    i ≫ sSetTopAdj.homEquiv K (SSet.toTop.obj X) c = a ≫ sSetTopAdj.unit.app X := by
  rw [← sSetTopAdj.homEquiv_naturality_left, hc, adjoint_realized_map]

end

end Thomason.Construction

end

section

/-! # Finite singular approximation of full relative cubical families -/

namespace Thomason.Construction

open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open scoped Simplicial

noncomputable section

/-- The actual triangulated cube is finite in every dimension. -/
theorem realizedCube_finite (n : ℕ) : (RealizedCube.obj n).Finite := by
  induction n with
  | zero => change (Δ[0] : SSet.{0}).Finite; infer_instance
  | succ n ih =>
    change (RealizedCube.obj n ⊗ (Δ[1] : SSet.{0})).Finite
    have := ih
    infer_instance

/-- A continuous higher family whose whole boundary is simplicial gives
an exact singular family with that entire boundary, followed by the unit. -/
theorem singularCubeProductEquiv_relative {K X : SSet.{0}} (n : ℕ)
    (a : K ⊗ (RealizedCube.boundary n).toSSet ⟶ X)
    (H : TopCat.of (SSet.toTop.obj K × SSet.toTop.obj (RealizedCube.obj (n+1))) ⟶
      SSet.toTop.obj X)
    (hH : SSet.toTop.map (K ◁ (RealizedCube.boundary n).ι) ≫
      realizationProductComparison K (RealizedCube.obj (n+1)) ≫ H = SSet.toTop.map a) :
    K ◁ (RealizedCube.boundary n).ι ≫ singularCubeProductEquiv K (n+1) (SSet.toTop.obj X) H =
      a ≫ sSetTopAdj.unit.app X := by
  have := realizationProductComparison_cube_isIso K (n+1)
  rw [show singularCubeProductEquiv K (n+1) (SSet.toTop.obj X) H =
    sSetTopAdj.homEquiv _ _ (realizationProductComparison K (RealizedCube.obj (n+1)) ≫ H)
      from singularProductEquiv_apply _ _ _ H]
  exact adjoint_relative_extension _ a _ hH

/-- One finite singular carrier contains the entire higher cubical
family and its exact original boundary. The carrier retains the full
continuous evaluation, not just the two endpoint maps. -/
theorem finite_singular_cube_family {K X : SSet.{0}} [K.Finite] (n : ℕ)
    (a : K ⊗ (RealizedCube.boundary n).toSSet ⟶ X)
    (H : TopCat.of (SSet.toTop.obj K × SSet.toTop.obj (RealizedCube.obj (n+1))) ⟶
      SSet.toTop.obj X)
    (hH : SSet.toTop.map (K ◁ (RealizedCube.boundary n).ι) ≫
      realizationProductComparison K (RealizedCube.obj (n+1)) ≫ H = SSet.toTop.map a) :
    ∃ (S : (TopCat.toSSet.obj (SSet.toTop.obj X)).Subcomplex) (_ : SSet.Finite S.toSSet)
      (d : K ⊗ RealizedCube.obj (n+1) ⟶ S.toSSet)
      (aS : K ⊗ (RealizedCube.boundary n).toSSet ⟶ S.toSSet),
      aS ≫ S.ι = a ≫ sSetTopAdj.unit.app X ∧
      K ◁ (RealizedCube.boundary n).ι ≫ d = aS ∧
      (realizationCubeProductIso K (n+1)).inv ≫
        SSet.toTop.map d ≫ SSet.toTop.map S.ι ≫ sSetTopAdj.counit.app (SSet.toTop.obj X) = H := by
  have := realizedCube_finite (n+1)
  have := realizationProductComparison_cube_isIso K (n+1)
  let f := singularCubeProductEquiv K (n+1) (SSet.toTop.obj X) H
  let S := SSet.Subcomplex.range f
  let d := SSet.Subcomplex.toRange f
  let aS := K ◁ (RealizedCube.boundary n).ι ≫ d
  refine ⟨S, inferInstance, d, aS, ?_, rfl, ?_⟩
  · dsimp only [aS]
    rw [Category.assoc, SSet.Subcomplex.toRange_ι]
    exact singularCubeProductEquiv_relative n a H hH
  · rw [← Category.assoc (SSet.toTop.map d), ← SSet.toTop.map_comp d S.ι,
      SSet.Subcomplex.toRange_ι]
    exact singularProductEquiv_evaluate K (RealizedCube.obj (n+1)) (SSet.toTop.obj X) H

end

end Thomason.Construction

end

section

/-! # Exact singular families over finite simplicial parameter spaces -/

namespace Thomason.Construction

open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open scoped Simplicial

noncomputable section

/-- Changing the family parameter commutes with the actual product
adjunction. Both sides represent the same full continuous family. -/
theorem singularFiniteProductEquiv_parameter {L K P : SSet.{0}} [P.Finite]
    (f : L ⟶ K) (X : TopCat.{0})
    (H : TopCat.of (SSet.toTop.obj K × SSet.toTop.obj P) ⟶ X) :
    letI := realizationProductComparison_finite_isIso K P
    letI := realizationProductComparison_finite_isIso L P
    f ▷ P ≫ singularProductEquiv K P X H =
      singularProductEquiv L P X ((SSet.toTop.map f ▷ SSet.toTop.obj P) ≫ H) := by
  let := realizationProductComparison_finite_isIso K P
  let := realizationProductComparison_finite_isIso L P
  rw [singularProductEquiv_apply, singularProductEquiv_apply,
    ← sSetTopAdj.homEquiv_naturality_left, ← Category.assoc,
    realizationProductComparison_naturality_left]
  exact congrArg (sSetTopAdj.homEquiv (L ⊗ P) X)
    (Category.assoc (realizationProductComparison L P)
      (SSet.toTop.map f ▷ SSet.toTop.obj P) H)

/-- Restriction to an arbitrary prescribed simplicial parameter subspace
is exact under the singular adjunction. The parameter need only be finite;
it need not already be presented as a triangulated cube. -/
theorem singularFiniteProductEquiv_relative {K A P X : SSet.{0}} [P.Finite]
    (i : A ⟶ P) (a : K ⊗ A ⟶ X)
    (H : TopCat.of (SSet.toTop.obj K × SSet.toTop.obj P) ⟶ SSet.toTop.obj X)
    (hH : SSet.toTop.map (K ◁ i) ≫ realizationProductComparison K P ≫ H =
      SSet.toTop.map a) :
    letI := realizationProductComparison_finite_isIso K P
    K ◁ i ≫ singularProductEquiv K P (SSet.toTop.obj X) H =
      a ≫ sSetTopAdj.unit.app X := by
  let := realizationProductComparison_finite_isIso K P
  rw [singularProductEquiv_apply]
  exact adjoint_relative_extension _ a _ hH

/-- A whole continuous family and its entire prescribed subfamily fit in
one finite singular carrier. Evaluation recovers the original family at
every point of the actual product realization. -/
theorem finite_singular_parameter_family {K A P X : SSet.{0}} [K.Finite] [P.Finite]
    (i : A ⟶ P) (a : K ⊗ A ⟶ X)
    (H : TopCat.of (SSet.toTop.obj K × SSet.toTop.obj P) ⟶ SSet.toTop.obj X)
    (hH : SSet.toTop.map (K ◁ i) ≫ realizationProductComparison K P ≫ H =
      SSet.toTop.map a) :
    letI := realizationProductComparison_finite_isIso K P
    ∃ (S : (TopCat.toSSet.obj (SSet.toTop.obj X)).Subcomplex)
      (_ : SSet.Finite S.toSSet) (d : K ⊗ P ⟶ S.toSSet) (aS : K ⊗ A ⟶ S.toSSet),
      aS ≫ S.ι = a ≫ sSetTopAdj.unit.app X ∧
      K ◁ i ≫ d = aS ∧
      inv (realizationProductComparison K P) ≫ SSet.toTop.map d ≫
        SSet.toTop.map S.ι ≫ sSetTopAdj.counit.app (SSet.toTop.obj X) = H := by
  let := realizationProductComparison_finite_isIso K P
  let f := singularProductEquiv K P (SSet.toTop.obj X) H
  let S := SSet.Subcomplex.range f
  let d := SSet.Subcomplex.toRange f
  let aS := K ◁ i ≫ d
  refine ⟨S, inferInstance, d, aS, ?_, rfl, ?_⟩
  · dsimp only [aS]
    rw [Category.assoc, SSet.Subcomplex.toRange_ι]
    exact singularFiniteProductEquiv_relative i a H hH
  · rw [← Category.assoc (SSet.toTop.map d), ← SSet.toTop.map_comp d S.ι,
      SSet.Subcomplex.toRange_ι]
    exact singularProductEquiv_evaluate K P (SSet.toTop.obj X) H

end

end Thomason.Construction

end

section

/-! # Singular fibrations give exact continuous relative homotopy lifts

This is an interface between horn lifting and the actual topology of realized
subcomplexes. No comparison weak equivalence is assumed.
-/

namespace Thomason.Construction

open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open SSet.modelCategoryQuillen
open scoped Simplicial

noncomputable section

/-- If the actual singular map is a Kan fibration, it lifts any continuous
homotopy on a realization while respecting a prescribed subcomplex homotopy. -/
theorem singular_fibration_relative_homotopy_lifting
    {A K : SSet.{0}} {X Y : TopCat.{0}} (i : A ⟶ K) [Mono i]
    (p : X ⟶ Y) [HomotopicalAlgebra.Fibration (TopCat.toSSet.map p)]
    (f : SSet.toTop.obj K ⟶ X)
    (a : C(unitInterval × SSet.toTop.obj A, X))
    (H : C(unitInterval × SSet.toTop.obj K, Y))
    (ha₀ : ∀ x, a (0, x) = f.hom ((SSet.toTop.map i).hom x))
    (hap : ∀ t x, p.hom (a (t, x)) = H (t, (SSet.toTop.map i).hom x))
    (hf₀ : ∀ x, p.hom (f.hom x) = H (0, x)) :
    ∃ F : C(unitInterval × SSet.toTop.obj K, X),
      (∀ x, F (0, x) = f.hom x) ∧
      (∀ t x, F (t, (SSet.toTop.map i).hom x) = a (t, x)) ∧
      ∀ t x, p.hom (F (t, x)) = H (t, x) := by
  let fs := sSetTopAdj.homEquiv K X f
  have ha : SSet.ι₀ ≫ singularCylinderMap a = i ≫ fs := by
    rw [singularCylinderMap_zero]
    dsimp only [fs]
    rw [← sSetTopAdj.homEquiv_naturality_left]
    congr 1
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro x
    exact ha₀ x
  have hb : singularCylinderMap a ≫ TopCat.toSSet.map p =
      i ▷ Δ[1] ≫ singularCylinderMap H := by
    rw [singularCylinderMap_postcomp, singularCylinderMap_naturality]
    congr 1
    ext z
    exact hap z.1 z.2
  have hf : fs ≫ TopCat.toSSet.map p = SSet.ι₀ ≫ singularCylinderMap H := by
    dsimp only [fs]
    rw [← sSetTopAdj.homEquiv_naturality_right, singularCylinderMap_zero]
    congr 1
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro x
    exact hf₀ x
  obtain ⟨e, he₀, hei, hep⟩ := exists_kan_cylinder_lift i (TopCat.toSSet.map p)
    fs (singularCylinderMap a) (singularCylinderMap H) ha hb hf
  refine ⟨evaluateSingularCylinder e, ?_, ?_, ?_⟩
  · intro x
    rw [evaluateSingularCylinder_zero, he₀]
    exact congrArg (fun k => k.hom x) ((sSetTopAdj.homEquiv K X).symm_apply_apply f)
  · intro t x
    rw [evaluateSingularCylinder_naturality, hei, evaluate_singularCylinderMap]
  · intro t x
    rw [← evaluateSingularCylinder_postcomp, hep, evaluate_singularCylinderMap]

end

end Thomason.Construction

end

section

/-! # Singular Kan fibrations lift homotopies on literal cubes and boundaries -/

namespace Thomason.Construction.RealizedCube

open CategoryTheory Convexity
open SSet.modelCategoryQuillen
open scoped Simplicial

noncomputable section

/-- The relative homotopy lifting property for an ordinary cube and its entire
boundary follows from the Kan fibration property of the actual singular map. -/
theorem singular_fibration_cube_lifting {X Y : TopCat.{0}} (p : X ⟶ Y)
    [HomotopicalAlgebra.Fibration (TopCat.toSSet.map p)] (n : ℕ)
    (f : C(Fin (n+1) → unitInterval, X))
    (a : C(unitInterval × Cube.boundary (Fin (n+1)), X))
    (H : C(unitInterval × (Fin (n+1) → unitInterval), Y))
    (ha₀ : ∀ x : Cube.boundary (Fin (n+1)), a (0, x) = f x.val)
    (hap : ∀ t (x : Cube.boundary (Fin (n+1))), p.hom (a (t, x)) = H (t, x.val))
    (hf₀ : ∀ x, p.hom (f x) = H (0, x)) :
    ∃ F : C(unitInterval × (Fin (n+1) → unitInterval), X),
      (∀ x, F (0, x) = f x) ∧
      (∀ t (x : Cube.boundary (Fin (n+1))), F (t, x.val) = a (t, x)) ∧
      ∀ t x, p.hom (F (t, x)) = H (t, x) := by
  let f' : SSet.toTop.obj (obj (n+1)) ⟶ X := TopCat.ofHom (f.comp (coordinates (n+1)))
  let a' : C(unitInterval × SSet.toTop.obj (boundary n : SSet.{0}), X) :=
    a.comp ⟨fun z => (z.1, boundaryCoordinates n z.2),
      continuous_fst.prodMk ((boundaryCoordinates n).continuous.comp continuous_snd)⟩
  let H' : C(unitInterval × SSet.toTop.obj (obj (n+1)), Y) :=
    H.comp ⟨fun z => (z.1, coordinates (n+1) z.2),
      continuous_fst.prodMk ((coordinates (n+1)).continuous.comp continuous_snd)⟩
  have h₀ : ∀ x, a' (0, x) = f'.hom ((SSet.toTop.map (boundary n).ι).hom x) := by
    intro x
    exact ha₀ (boundaryCoordinates n x)
  have hp : ∀ t x, p.hom (a' (t, x)) = H' (t, (SSet.toTop.map (boundary n).ι).hom x) := by
    intro t x
    exact hap t (boundaryCoordinates n x)
  have hf : ∀ x, p.hom (f'.hom x) = H' (0, x) := by
    intro x
    exact hf₀ (coordinates (n+1) x)
  obtain ⟨F, hF₀, hFa, hFp⟩ := singular_fibration_relative_homotopy_lifting
    (boundary n).ι p f' a' H' h₀ hp hf
  let F' : C(unitInterval × (Fin (n+1) → unitInterval), X) :=
    F.comp ⟨fun z => (z.1, sectionMap (n+1) z.2),
      continuous_fst.prodMk ((sectionMap (n+1)).continuous.comp continuous_snd)⟩
  refine ⟨F', ?_, ?_, ?_⟩
  · intro x
    change F (0, sectionMap (n+1) x) = f x
    rw [hF₀]
    change f (coordinates (n+1) (sectionMap (n+1) x)) = f x
    rw [coordinates_section]
  · intro t x
    change F (t, sectionMap (n+1) x.val) = a (t, x)
    rw [← boundarySection_inclusion n x, hFa]
    change a (t, boundaryCoordinates n (boundarySection n x)) = a (t, x)
    rw [boundaryCoordinates_section]
  · intro t x
    change p.hom (F (t, sectionMap (n+1) x)) = H (t, x)
    rw [hFp]
    change H (t, coordinates (n+1) (sectionMap (n+1) x)) = H (t, x)
    rw [coordinates_section]

end

end Thomason.Construction.RealizedCube

end

section

/-! # Path lifting and strict point surjectivity for singular fibrations -/

namespace Thomason.Construction

open CategoryTheory MonoidalCategory
open SSet.modelCategoryQuillen
open scoped Simplicial

noncomputable section

/-- Singular Kan fibrations lift continuous homotopies on any realization
with the given initial lift fixed exactly. -/
theorem singular_fibration_homotopy_lifting {K : SSet.{0}} {X Y : TopCat.{0}}
    (p : X ⟶ Y) [HomotopicalAlgebra.Fibration (TopCat.toSSet.map p)]
    (f : SSet.toTop.obj K ⟶ X) (H : C(unitInterval × SSet.toTop.obj K, Y))
    (h₀ : ∀ x, p.hom (f.hom x) = H (0, x)) :
    ∃ F : C(unitInterval × SSet.toTop.obj K, X),
      (∀ x, F (0, x) = f.hom x) ∧ ∀ t x, p.hom (F (t, x)) = H (t, x) := by
  let fs := sSetTopAdj.homEquiv K X f
  have hf : fs ≫ TopCat.toSSet.map p = SSet.ι₀ ≫ singularCylinderMap H := by
    dsimp only [fs]
    rw [← sSetTopAdj.homEquiv_naturality_right, singularCylinderMap_zero]
    congr 1
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    exact h₀
  let : HasLiftingProperty (SSet.ι₀ (X := K)) (TopCat.toSSet.map p) :=
    anodyne_iota_zero K _ (by rw [← HomotopicalAlgebra.fibration_iff]; infer_instance)
  let sq : CommSq fs SSet.ι₀ (TopCat.toSSet.map p) (singularCylinderMap H) := ⟨hf⟩
  refine ⟨evaluateSingularCylinder sq.lift, ?_, ?_⟩
  · intro x
    rw [evaluateSingularCylinder_zero, sq.fac_left]
    exact congrArg (fun k => k.hom x) ((sSetTopAdj.homEquiv K X).symm_apply_apply f)
  · intro t x
    rw [← evaluateSingularCylinder_postcomp, sq.fac_right, evaluate_singularCylinderMap]

/-- Every path in the base of a singular Kan fibration has a continuous lift
from any specified point over its source. -/
theorem singular_fibration_path_lifting {X Y : TopCat.{0}} (p : X ⟶ Y)
    [HomotopicalAlgebra.Fibration (TopCat.toSSet.map p)]
    {x : X} {y : Y} (γ : Path (p.hom x) y) :
    ∃ q : C(unitInterval, X), q 0 = x ∧ ∀ t, p.hom (q t) = γ t := by
  let f : SSet.toTop.obj (Δ[0] : SSet.{0}) ⟶ X :=
    TopCat.ofHom (ContinuousMap.const _ x)
  let H : C(unitInterval × SSet.toTop.obj (Δ[0] : SSet.{0}), Y) :=
    ⟨fun z => γ z.1, γ.continuous.comp continuous_fst⟩
  have h₀ : ∀ z, p.hom (f.hom z) = H (0, z) := fun _ => γ.source.symm
  obtain ⟨F, hF₀, hFp⟩ := singular_fibration_homotopy_lifting p f H h₀
  let q : C(unitInterval, X) := F.comp
    ⟨fun t => (t, default), continuous_id.prodMk continuous_const⟩
  exact ⟨q, hF₀ default, fun t => hFp t default⟩

/-- Surjectivity on path components becomes strict surjectivity on points
when the actual singular map is a Kan fibration. -/
theorem singular_fibration_surjective_of_components {X Y : TopCat.{0}} (p : X ⟶ Y)
    [HomotopicalAlgebra.Fibration (TopCat.toSSet.map p)]
    (hp : Function.Surjective (HomotopyMaps.componentsMap p.hom)) :
    Function.Surjective p.hom := by
  intro y
  obtain ⟨a, ha⟩ := hp (ZerothHomotopy.mk y)
  induction a using ZerothHomotopy.rec with
  | mk x =>
    have hj : Joined (p.hom x) y := Quotient.exact ha
    obtain ⟨q, _, hq⟩ := singular_fibration_path_lifting p hj.somePath
    exact ⟨q 1, (hq 1).trans hj.somePath.target⟩

/-- The degree-zero lifting consequence of a weak singular fibration,
proved for the actual topological weak-equivalence test. -/
theorem singular_fibration_surjective_of_weak {X Y : TopCat.{0}} (p : X ⟶ Y)
    [HomotopicalAlgebra.Fibration (TopCat.toSSet.map p)]
    (hp : IsWeakHomotopyEquivalence p.hom) : Function.Surjective p.hom :=
  singular_fibration_surjective_of_components p hp.1.2

end

end Thomason.Construction

end

section

/-! # The actual singular complex of the continuous path space

The constructed realization cylinder homeomorphism identifies the singular
complex of the compact-open path space with the simplicial internal hom.
-/

namespace Thomason.Construction

open CategoryTheory MonoidalCategory MonoidalClosed
open scoped Simplicial

noncomputable section

/-- The ordinary compact-open space of all paths, with unrestricted ends. -/
def continuousPathSpace (X : TopCat.{0}) : TopCat.{0} :=
  TopCat.of C(unitInterval, X)

/-- Exponential adjunction with the compact interval, in the order used by
the realization cylinder. No local compactness of the parameter space is needed. -/
def continuousPathFamilyEquiv (K : SSet.{0}) (X : TopCat.{0}) :
    (SSet.toTop.obj K ⟶ continuousPathSpace X) ≃
      C(unitInterval × SSet.toTop.obj K, X) where
  toFun f := f.hom.uncurry.comp ContinuousMap.prodSwap
  invFun H := TopCat.ofHom ((H.comp ContinuousMap.prodSwap).curry)
  left_inv f := by
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro x
    apply ContinuousMap.ext
    intro t
    rfl
  right_inv H := by
    apply ContinuousMap.ext
    rintro ⟨t, x⟩
    rfl

/-- Singular path families are exactly singular-valued simplicial cylinders. -/
def singularPathCylinderEquiv (K : SSet.{0}) (X : TopCat.{0}) :
    (K ⟶ TopCat.toSSet.obj (continuousPathSpace X)) ≃
      (K ⊗ Δ[1] ⟶ TopCat.toSSet.obj X) :=
  (sSetTopAdj.homEquiv K (continuousPathSpace X)).symm |>.trans
    ((continuousPathFamilyEquiv K X).trans (singularCylinderEquiv K X))

/-- The cylinder correspondence respects every simplicial parameter change. -/
theorem singularPathCylinderEquiv_naturality {A K : SSet.{0}} (i : A ⟶ K)
    (X : TopCat.{0}) (f : K ⟶ TopCat.toSSet.obj (continuousPathSpace X)) :
    singularPathCylinderEquiv A X (i ≫ f) =
      i ▷ Δ[1] ≫ singularPathCylinderEquiv K X f := by
  change singularCylinderMap
    (continuousPathFamilyEquiv A X ((sSetTopAdj.homEquiv A _).symm (i ≫ f))) = _
  rw [sSetTopAdj.homEquiv_naturality_left_symm]
  change singularCylinderMap
      (continuousPathFamilyEquiv A X
        (SSet.toTop.map i ≫ (sSetTopAdj.homEquiv K _).symm f)) =
    i ▷ Δ[1] ≫ singularCylinderMap
      (continuousPathFamilyEquiv K X ((sSetTopAdj.homEquiv K _).symm f))
  rw [singularCylinderMap_naturality]
  rfl

/-- Braiding identifies the two orders of the simplicial cylinder. -/
def swapCylinderEquiv (K : SSet.{0}) (X : SSet.{0}) :
    (K ⊗ Δ[1] ⟶ X) ≃ (Δ[1] ⊗ K ⟶ X) :=
  Iso.homCongr (β_ K Δ[1]) (Iso.refl X)

/-- The hom-set form of the path-space/internal-hom identification. -/
def singularPathInternalEquiv (K : SSet.{0}) (X : TopCat.{0}) :
    (K ⟶ TopCat.toSSet.obj (continuousPathSpace X)) ≃
      (K ⟶ (ihom (Δ[1] : SSet.{0})).obj (TopCat.toSSet.obj X)) :=
  (singularPathCylinderEquiv K X).trans
    ((swapCylinderEquiv K _).trans ((ihom.adjunction Δ[1]).homEquiv K _))

theorem singularPathInternalEquiv_naturality {A K : SSet.{0}} (i : A ⟶ K)
    (X : TopCat.{0}) (f : K ⟶ TopCat.toSSet.obj (continuousPathSpace X)) :
    singularPathInternalEquiv A X (i ≫ f) =
      i ≫ singularPathInternalEquiv K X f := by
  change curry ((β_ A Δ[1]).inv ≫ singularPathCylinderEquiv A X (i ≫ f) ≫ 𝟙 _) =
    i ≫ curry ((β_ K Δ[1]).inv ≫ singularPathCylinderEquiv K X f ≫ 𝟙 _)
  rw [singularPathCylinderEquiv_naturality, ← curry_natural_left]
  congr 1

/-- The actual compact-open path space and the simplicial internal hom have
isomorphic singular complexes. -/
def singularPathSpaceIso (X : TopCat.{0}) :
    TopCat.toSSet.obj (continuousPathSpace X) ≅
      (ihom (Δ[1] : SSet.{0})).obj (TopCat.toSSet.obj X) :=
  Yoneda.ext _ _ (fun {_} => singularPathInternalEquiv _ X)
    (fun {_} => (singularPathInternalEquiv _ X).symm)
    (fun _ => Equiv.symm_apply_apply _ _) (fun _ => Equiv.apply_symm_apply _ _)
    (fun i f => singularPathInternalEquiv_naturality i X f)

/-- Postcomposition on actual compact-open path spaces. -/
def continuousPathMap {X Y : TopCat.{0}} (p : X ⟶ Y) :
    continuousPathSpace X ⟶ continuousPathSpace Y :=
  TopCat.ofHom ⟨fun γ => p.hom.comp γ, ContinuousMap.continuous_postcomp p.hom⟩

theorem singularPathCylinderEquiv_postcomp (K : SSet.{0})
    {X Y : TopCat.{0}} (p : X ⟶ Y)
    (f : K ⟶ TopCat.toSSet.obj (continuousPathSpace X)) :
    singularPathCylinderEquiv K Y (f ≫ TopCat.toSSet.map (continuousPathMap p)) =
      singularPathCylinderEquiv K X f ≫ TopCat.toSSet.map p := by
  change singularCylinderMap
    (continuousPathFamilyEquiv K Y
      ((sSetTopAdj.homEquiv K _).symm (f ≫ TopCat.toSSet.map (continuousPathMap p)))) = _
  rw [sSetTopAdj.homEquiv_naturality_right_symm]
  change singularCylinderMap
      (continuousPathFamilyEquiv K Y
        ((sSetTopAdj.homEquiv K _).symm f ≫ continuousPathMap p)) =
    singularCylinderMap
      (continuousPathFamilyEquiv K X ((sSetTopAdj.homEquiv K _).symm f)) ≫
        TopCat.toSSet.map p
  rw [singularCylinderMap_postcomp]
  rfl

theorem singularPathInternalEquiv_postcomp (K : SSet.{0})
    {X Y : TopCat.{0}} (p : X ⟶ Y)
    (f : K ⟶ TopCat.toSSet.obj (continuousPathSpace X)) :
    singularPathInternalEquiv K Y (f ≫ TopCat.toSSet.map (continuousPathMap p)) =
      singularPathInternalEquiv K X f ≫ (ihom Δ[1]).map (TopCat.toSSet.map p) := by
  change curry ((β_ K Δ[1]).inv ≫
      singularPathCylinderEquiv K Y (f ≫ TopCat.toSSet.map (continuousPathMap p)) ≫ 𝟙 _) =
    curry ((β_ K Δ[1]).inv ≫ singularPathCylinderEquiv K X f ≫ 𝟙 _) ≫ _
  rw [singularPathCylinderEquiv_postcomp, ← curry_natural_right]
  simp only [Category.comp_id, Category.assoc]

/-- The internal-hom comparison is natural in the target space. -/
theorem singularPathSpaceIso_naturality {X Y : TopCat.{0}} (p : X ⟶ Y) :
    TopCat.toSSet.map (continuousPathMap p) ≫ (singularPathSpaceIso Y).hom =
      (singularPathSpaceIso X).hom ≫ (ihom Δ[1]).map (TopCat.toSSet.map p) := by
  have h := singularPathInternalEquiv_naturality
    (TopCat.toSSet.map (continuousPathMap p)) Y (𝟙 _)
  have h' := singularPathInternalEquiv_postcomp _ p (𝟙 _)
  change TopCat.toSSet.map (continuousPathMap p) ≫
      singularPathInternalEquiv _ Y (𝟙 _) =
    singularPathInternalEquiv _ X (𝟙 _) ≫ (ihom Δ[1]).map (TopCat.toSSet.map p)
  simpa only [Category.comp_id, Category.id_comp] using h.symm.trans h'

/-- Naturality gives an isomorphism of the actual induced path-map arrows. -/
def singularPathMapArrowIso {X Y : TopCat.{0}} (p : X ⟶ Y) :
    Arrow.mk (TopCat.toSSet.map (continuousPathMap p)) ≅
      Arrow.mk ((ihom Δ[1]).map (TopCat.toSSet.map p)) :=
  Arrow.isoMk (singularPathSpaceIso X) (singularPathSpaceIso Y)
    (singularPathSpaceIso_naturality p).symm

end

end Thomason.Construction

end

end OAI
