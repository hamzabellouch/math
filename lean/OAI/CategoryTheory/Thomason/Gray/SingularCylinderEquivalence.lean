import OAI.CategoryTheory.Thomason.Gray.DirectedGlobeUniversal
import OAI.CategoryTheory.Thomason.Gray.GrayMappingInterchangeEvaluation
import OAI.CategoryTheory.Thomason.Gray.TripleGlobeAtoms
import OAI.CategoryTheory.Thomason.Gray.TripleGlobeCylinderSource
import OAI.CategoryTheory.Thomason.Simplicial.SubdivisionFaceImages

namespace OAI

section

/-! # The actual realization weak equivalence of positive-chain cylinders

The explicit minimum contraction gives a homotopy inverse on Street nerves.
This bridge uses the existing published simplex-generation premise, but no
right Gray adjunction, transfer, localization or Kan lifting premise.
-/

namespace Thomason.Construction.SimplexAtomsInput

open CategoryTheory _root_.OAI.Thomason.Construction.DirectedComplex

noncomputable section

variable {h : NormalizedSimplexIdentities} (a : SimplexAtomsInput h)

include a

/-- The projection of an actual chain cylinder is a weak equivalence for
the prescribed topological realization of the Street nerve. -/
theorem chainCylinder_projection_weak (K : DirectedComplex.{0}) :
    h.streetWeakEquivalences (RightCylinder.projection K).realization := by
  let i : K.realization ⟶ (rightCylinder K).realization :=
    (RightCylinder.endpoint K false).realization
  let p : (rightCylinder K).realization ⟶ K.realization :=
    (RightCylinder.projection K).realization
  let c : (rightCylinder (rightCylinder K)).realization ⟶
      (rightCylinder K).realization := (RightCylinder.minimum K).realization
  have hip : i ≫ p = 𝟙 K.realization := by
    apply StrictOmegaCategory.Hom.ext
    funext x
    exact RightCylinder.realization_projection_endpoint K false x
  have hzero : (RightCylinder.endpoint (rightCylinder K) false).realization ≫ c =
      p ≫ i := by
    apply StrictOmegaCategory.Hom.ext
    funext x
    exact RightCylinder.realization_minimum_outer_zero (K := K) x
  have hone : (RightCylinder.endpoint (rightCylinder K) true).realization ≫ c =
      𝟙 (rightCylinder K).realization := by
    apply StrictOmegaCategory.Hom.ext
    funext x
    exact RightCylinder.realization_minimum_outer_one (K := K) x
  have hx : SSet.Homotopy (h.streetNerve.map p ≫ h.streetNerve.map i)
      (𝟙 (h.streetNerve.obj (rightCylinder K).realization)) := by
    have hc := a.chainNerveHomotopy c
    rw [hzero, hone, CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id] at hc
    exact hc
  have hy : SSet.Homotopy (h.streetNerve.map i ≫ h.streetNerve.map p)
      (𝟙 (h.streetNerve.obj K.realization)) := by
    rw [← CategoryTheory.Functor.map_comp, hip, CategoryTheory.Functor.map_id]
    exact SSet.RelativeMorphism.Homotopy.refl _
  exact simplicial_homotopy_inverse_weak (h.streetNerve.map p) (h.streetNerve.map i) hx hy

end

end Thomason.Construction.SimplexAtomsInput

end

section

/-! # The actual Gray–Street cylinder comparison and singular evaluation -/

namespace Thomason.Construction.RightGrayInput

open CategoryTheory MonoidalCategory

noncomputable section

variable {h : NormalizedSimplexIdentities} (G : RightGrayInput h)
  (aw : SimplexComplex.AlexanderWhitneyInput h)

/-- The continuous comparison from the ordinary cylinder to the realized Gray cylinder. -/
def realizedCylinderComparison (X : StrictOmegaCategory.{0}) :
    TopologicalInterval.cylinder.obj (SSet.toTop.obj (h.streetNerve.obj X)) ⟶
      SSet.toTop.obj (h.streetNerve.obj (G.cylinder.obj X)) :=
  RealizedCylinder.comparison (h.streetNerve.obj X) ≫
    SSet.toTop.map (G.nerveCylinder aw X)

/-- The geometric Gray comparison is natural in actual strict functors. -/
theorem realizedCylinderComparison_naturality {X Y : StrictOmegaCategory.{0}}
    (f : X ⟶ Y) :
    TopologicalInterval.cylinder.map (SSet.toTop.map (h.streetNerve.map f)) ≫
      G.realizedCylinderComparison aw Y =
    G.realizedCylinderComparison aw X ≫
      SSet.toTop.map (h.streetNerve.map (G.cylinder.map f)) := by
  unfold realizedCylinderComparison
  rw [← Category.assoc, RealizedCylinder.comparison_naturality, Category.assoc,
    ← SSet.toTop.map_comp, G.nerveCylinder_naturality aw, SSet.toTop.map_comp, Category.assoc]

/-- Preceding the nerve comparison by the explicit prism does not change its weak test. -/
theorem nerveCylinder_weak_iff (X : StrictOmegaCategory.{0}) :
    realizationWeakEquivalences (G.nerveCylinder aw X) ↔
      topologicalWeakEquivalences (G.realizedCylinderComparison aw X) := by
  change topologicalWeakEquivalences (SSet.toTop.map (G.nerveCylinder aw X)) ↔
    topologicalWeakEquivalences
      (RealizedCylinder.comparison (h.streetNerve.obj X) ≫
        SSet.toTop.map (G.nerveCylinder aw X))
  constructor
  · exact fun h => topologicalWeakEquivalences.comp_mem _ _
      (RealizedCylinder.comparison_weak _) h
  · exact fun h => topologicalWeakEquivalences.of_precomp _ _
      (RealizedCylinder.comparison_weak _) h

/-- Collapsing the Gray interval recovers the original realization point exactly. -/
theorem realizedCylinderComparison_projection (X : StrictOmegaCategory.{0}) :
    G.realizedCylinderComparison aw X ≫
      SSet.toTop.map (h.streetNerve.map (G.projection.app X)) =
        TopologicalInterval.projection (SSet.toTop.obj (h.streetNerve.obj X)) := by
  unfold realizedCylinderComparison
  rw [Category.assoc, ← SSet.toTop.map_comp, G.nerveCylinder_projection aw]
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro p
  exact RealizedCylinder.comparison_first _ p.1 p.2

/-- The geometric Gray-cylinder comparison is weak exactly when its strict projection
satisfies the actual Street-nerve weak-equivalence test. -/
theorem realizedCylinderComparison_weak_iff (X : StrictOmegaCategory.{0}) :
    topologicalWeakEquivalences (G.realizedCylinderComparison aw X) ↔
      h.streetWeakEquivalences (G.projection.app X) := by
  have hc : topologicalWeakEquivalences (G.realizedCylinderComparison aw X ≫
      SSet.toTop.map (h.streetNerve.map (G.projection.app X))) := by
    rw [G.realizedCylinderComparison_projection aw]
    exact TopologicalInterval.projection_weak _
  constructor
  · intro hf
    exact topologicalWeakEquivalences.of_precomp _ _ hf hc
  · intro hg
    exact topologicalWeakEquivalences.of_postcomp _ _ hg hc

/-- The actual simplicial Gray–Street comparison and the strict cylinder projection
have exactly the same semantic weak-equivalence obligation. -/
theorem nerveCylinder_weak_iff_projection (X : StrictOmegaCategory.{0}) :
    realizationWeakEquivalences (G.nerveCylinder aw X) ↔
      h.streetWeakEquivalences (G.projection.app X) :=
  (G.nerveCylinder_weak_iff aw X).trans (G.realizedCylinderComparison_weak_iff aw X)

/-- Singularizing and realizing a strict Gray homotopy commutes pointwise with evaluation. -/
theorem realizedHomotopy_singular_counit {X Y : StrictOmegaCategory.{0}}
    (P : G.cylinder.obj X ⟶ Y) (t : unitInterval)
    (x : SSet.toTop.obj (TopCat.toSSet.obj (SSet.toTop.obj (h.streetNerve.obj X)))) :
    (sSetTopAdj.counit.app (SSet.toTop.obj (h.streetNerve.obj Y))).hom
      (RealizedCylinder.homotopy (singularHomotopy (G.realizedHomotopy aw P)) (t, x)) =
        G.realizedHomotopy aw P (t,
          (sSetTopAdj.counit.app (SSet.toTop.obj (h.streetNerve.obj X))).hom x) :=
  realizedSingularHomotopy_counit (G.realizedHomotopy aw P) t x

end

end Thomason.Construction.RightGrayInput

end

section

/-! # Exact evaluation of cylinders with values in a singular set -/

namespace Thomason.Construction

open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open scoped Simplicial

noncomputable section

/-- A singular-valued simplicial cylinder gives an actual continuous cylinder. -/
def evaluateSingularCylinder {K : SSet.{0}} {X : TopCat.{0}}
    (e : K ⊗ Δ[1] ⟶ TopCat.toSSet.obj X) :
    C(unitInterval × SSet.toTop.obj K, X) where
  toFun z := (sSetTopAdj.counit.app X).hom
    ((SSet.toTop.map e).hom ((RealizedCylinder.comparison K).hom (z.2, z.1)))
  continuous_toFun := (sSetTopAdj.counit.app X).hom.continuous.comp
    ((SSet.toTop.map e).hom.continuous.comp
      ((RealizedCylinder.comparison K).hom.continuous.comp continuous_swap))

/-- Evaluation commutes exactly with restriction along a simplicial map. -/
theorem evaluateSingularCylinder_naturality {A K : SSet.{0}} {X : TopCat.{0}}
    (i : A ⟶ K) (e : K ⊗ Δ[1] ⟶ TopCat.toSSet.obj X)
    (t : unitInterval) (x : SSet.toTop.obj A) :
    evaluateSingularCylinder e (t, (SSet.toTop.map i).hom x) =
      evaluateSingularCylinder (i ▷ Δ[1] ≫ e) (t, x) := by
  have hn := congrArg (fun u => u.hom (x, t)) (RealizedCylinder.comparison_naturality i)
  change (RealizedCylinder.comparison K).hom ((SSet.toTop.map i).hom x, t) =
    (SSet.toTop.map (i ▷ Δ[1])).hom ((RealizedCylinder.comparison A).hom (x, t)) at hn
  dsimp only [evaluateSingularCylinder, ContinuousMap.coe_mk]
  rw [hn, SSet.toTop.map_comp]
  rfl

/-- Evaluation commutes with postcomposition by an actual continuous map. -/
theorem evaluateSingularCylinder_postcomp {K : SSet.{0}} {X Y : TopCat.{0}}
    (e : K ⊗ Δ[1] ⟶ TopCat.toSSet.obj X) (p : X ⟶ Y)
    (t : unitInterval) (x : SSet.toTop.obj K) :
    evaluateSingularCylinder (e ≫ TopCat.toSSet.map p) (t, x) =
      p.hom (evaluateSingularCylinder e (t, x)) := by
  have hc := congrArg (fun k => k.hom
    ((SSet.toTop.map e).hom ((RealizedCylinder.comparison K).hom (x, t))))
      (sSetTopAdj.counit.naturality p)
  dsimp only [evaluateSingularCylinder, ContinuousMap.coe_mk]
  rw [SSet.toTop.map_comp]
  exact hc

/-- The zero endpoint is the actual adjoint of the zero face. -/
theorem evaluateSingularCylinder_zero {K : SSet.{0}} {X : TopCat.{0}}
    (e : K ⊗ Δ[1] ⟶ TopCat.toSSet.obj X) (x : SSet.toTop.obj K) :
    evaluateSingularCylinder e (0, x) =
      ((sSetTopAdj.homEquiv K X).symm (SSet.ι₀ ≫ e)).hom x := by
  dsimp only [evaluateSingularCylinder, ContinuousMap.coe_mk]
  rw [RealizedCylinder.comparison_zero]
  change ((SSet.toTop.map SSet.ι₀ ≫ SSet.toTop.map e) ≫
    sSetTopAdj.counit.app X).hom x = _
  rw [← SSet.toTop.map_comp]
  rfl

/-- The one endpoint is the actual adjoint of the one face. -/
theorem evaluateSingularCylinder_one {K : SSet.{0}} {X : TopCat.{0}}
    (e : K ⊗ Δ[1] ⟶ TopCat.toSSet.obj X) (x : SSet.toTop.obj K) :
    evaluateSingularCylinder e (1, x) =
      ((sSetTopAdj.homEquiv K X).symm (SSet.ι₁ ≫ e)).hom x := by
  dsimp only [evaluateSingularCylinder, ContinuousMap.coe_mk]
  rw [RealizedCylinder.comparison_one]
  change ((SSet.toTop.map SSet.ι₁ ≫ SSet.toTop.map e) ≫
    sSetTopAdj.counit.app X).hom x = _
  rw [← SSet.toTop.map_comp]
  rfl

/-- Singularizing a continuous homotopy and restricting by the unit recovers
that same homotopy at every time and point. -/
theorem evaluateSingularCylinder_unit {K : SSet.{0}} {X : TopCat.{0}}
    {f g : SSet.toTop.obj K ⟶ X} (H : f.hom.Homotopy g.hom)
    (t : unitInterval) (x : SSet.toTop.obj K) :
    evaluateSingularCylinder
      (sSetTopAdj.unit.app K ▷ Δ[1] ≫ (singularHomotopy H).h) (t, x) = H (t, x) := by
  rw [← evaluateSingularCylinder_naturality]
  change (sSetTopAdj.counit.app X).hom
    ((SSet.toTop.map (singularHomotopy H).h).hom
      ((RealizedCylinder.comparison (TopCat.toSSet.obj (SSet.toTop.obj K))).hom
        ((SSet.toTop.map (sSetTopAdj.unit.app K)).hom x, t))) = _
  rw [← realizedHomotopy_apply, realizedSingularHomotopy_counit]
  have ht := congrArg (fun u => u.hom x) (sSetTopAdj.left_triangle_components K)
  change (sSetTopAdj.counit.app (SSet.toTop.obj K)).hom
    ((SSet.toTop.map (sSetTopAdj.unit.app K)).hom x) = x at ht
  rw [ht]

end

end Thomason.Construction

end

section

/-! # The adjunction on arbitrary continuous cylinders

The two realized projections provide an explicit adjoint cylinder whose
evaluation is the original continuous map at every time and point.
-/

namespace Thomason.Construction

open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open scoped Simplicial

noncomputable section

/-- Pull a continuous cylinder back along the actual realized projections. -/
def cylinderRealizationMap {K : SSet.{0}} {X : TopCat.{0}}
    (H : C(unitInterval × SSet.toTop.obj K, X)) : SSet.toTop.obj (K ⊗ Δ[1]) ⟶ X :=
  TopCat.ofHom {
    toFun z := H (PrismBarycentric.realizationTime.hom
      ((SSet.toTop.map (snd K Δ[1])).hom z), (SSet.toTop.map (fst K Δ[1])).hom z)
    continuous_toFun := H.continuous.comp
      (((PrismBarycentric.realizationTime.hom.continuous.comp
        (SSet.toTop.map (snd K Δ[1])).hom.continuous)).prodMk
          (SSet.toTop.map (fst K Δ[1])).hom.continuous) }

/-- The simplicial adjoint of an arbitrary continuous cylinder. -/
def singularCylinderMap {K : SSet.{0}} {X : TopCat.{0}}
    (H : C(unitInterval × SSet.toTop.obj K, X)) : K ⊗ Δ[1] ⟶ TopCat.toSSet.obj X :=
  sSetTopAdj.homEquiv _ _ (cylinderRealizationMap H)

/-- The original continuous cylinder is recovered exactly by evaluation. -/
theorem evaluate_singularCylinderMap {K : SSet.{0}} {X : TopCat.{0}}
    (H : C(unitInterval × SSet.toTop.obj K, X)) (t : unitInterval)
    (x : SSet.toTop.obj K) :
    evaluateSingularCylinder (singularCylinderMap H) (t, x) = H (t, x) := by
  have he : SSet.toTop.map (singularCylinderMap H) ≫ sSetTopAdj.counit.app X =
      cylinderRealizationMap H :=
    (sSetTopAdj.homEquiv _ _).symm_apply_apply (cylinderRealizationMap H)
  change ((SSet.toTop.map (singularCylinderMap H) ≫ sSetTopAdj.counit.app X).hom)
    ((RealizedCylinder.comparison K).hom (x, t)) = _
  rw [he]
  change H (_, _) = _
  rw [RealizedCylinder.comparison_time, RealizedCylinder.comparison_first]

/-- The actual projections of a realized simplicial cylinder are natural. -/
theorem cylinderRealizationMap_naturality {A K : SSet.{0}} {X : TopCat.{0}}
    (i : A ⟶ K) (H : C(unitInterval × SSet.toTop.obj K, X)) :
    SSet.toTop.map (i ▷ Δ[1]) ≫ cylinderRealizationMap H =
      cylinderRealizationMap
        (H.comp ⟨fun z => (z.1, (SSet.toTop.map i).hom z.2),
          continuous_fst.prodMk ((SSet.toTop.map i).hom.continuous.comp continuous_snd)⟩) := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro z
  have hf := congrArg (fun k => (SSet.toTop.map k).hom z) (whiskerRight_fst i (Δ[1] : SSet.{0}))
  have ht := congrArg (fun k => (SSet.toTop.map k).hom z) (whiskerRight_snd i (Δ[1] : SSet.{0}))
  simp only [SSet.toTop.map_comp] at hf ht
  change (SSet.toTop.map (fst K Δ[1])).hom ((SSet.toTop.map (i ▷ Δ[1])).hom z) =
    (SSet.toTop.map i).hom ((SSet.toTop.map (fst A Δ[1])).hom z) at hf
  change (SSet.toTop.map (snd K Δ[1])).hom ((SSet.toTop.map (i ▷ Δ[1])).hom z) =
    (SSet.toTop.map (snd A Δ[1])).hom z at ht
  change H (PrismBarycentric.realizationTime.hom
      ((SSet.toTop.map (snd K Δ[1])).hom ((SSet.toTop.map (i ▷ Δ[1])).hom z)),
      (SSet.toTop.map (fst K Δ[1])).hom ((SSet.toTop.map (i ▷ Δ[1])).hom z)) = _
  rw [hf, ht]
  rfl

/-- The zero face of the adjoint cylinder is the adjoint of its zero endpoint. -/
theorem singularCylinderMap_zero {K : SSet.{0}} {X : TopCat.{0}}
    (H : C(unitInterval × SSet.toTop.obj K, X)) :
    SSet.ι₀ ≫ singularCylinderMap H =
      sSetTopAdj.homEquiv K X
        (TopCat.ofHom ⟨fun x => H (0, x), H.continuous.comp (by fun_prop)⟩) := by
  rw [singularCylinderMap, ← sSetTopAdj.homEquiv_naturality_left]
  congr 1
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  change H (PrismBarycentric.realizationTime.hom
      ((SSet.toTop.map (snd K Δ[1])).hom ((SSet.toTop.map SSet.ι₀).hom x)),
      (SSet.toTop.map (fst K Δ[1])).hom ((SSet.toTop.map SSet.ι₀).hom x)) = H (0, x)
  rw [← RealizedCylinder.comparison_zero, RealizedCylinder.comparison_time,
    RealizedCylinder.comparison_first]

/-- Restriction of the continuous cylinder commutes with its simplicial adjoint. -/
theorem singularCylinderMap_naturality {A K : SSet.{0}} {X : TopCat.{0}}
    (i : A ⟶ K) (H : C(unitInterval × SSet.toTop.obj K, X)) :
    i ▷ Δ[1] ≫ singularCylinderMap H =
      singularCylinderMap
        (H.comp ⟨fun z => (z.1, (SSet.toTop.map i).hom z.2),
          continuous_fst.prodMk ((SSet.toTop.map i).hom.continuous.comp continuous_snd)⟩) := by
  rw [singularCylinderMap, ← sSetTopAdj.homEquiv_naturality_left,
    cylinderRealizationMap_naturality]
  rfl

/-- Postcomposition commutes with the adjoint cylinder, before realization. -/
theorem singularCylinderMap_postcomp {K : SSet.{0}} {X Y : TopCat.{0}}
    (H : C(unitInterval × SSet.toTop.obj K, X)) (p : X ⟶ Y) :
    singularCylinderMap H ≫ TopCat.toSSet.map p = singularCylinderMap (p.hom.comp H) := by
  rw [singularCylinderMap, ← sSetTopAdj.homEquiv_naturality_right]
  rfl

end

end Thomason.Construction

end

section

/-! # The exact singular adjunction for continuous cylinders -/

namespace Thomason.Construction

open CategoryTheory MonoidalCategory
open scoped Simplicial

noncomputable section

/-- Applying the explicit cylinder adjunction to an evaluated singular map
returns the original map in every simplicial degree. -/
theorem singularCylinderMap_evaluate {K : SSet.{0}} {X : TopCat.{0}}
    (e : K ⊗ Δ[1] ⟶ TopCat.toSSet.obj X) :
    singularCylinderMap (evaluateSingularCylinder e) = e := by
  apply (sSetTopAdj.homEquiv _ _).symm.injective
  rw [singularCylinderMap, Equiv.symm_apply_apply]
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro z
  change (sSetTopAdj.counit.app X).hom
    ((SSet.toTop.map e).hom
      ((RealizedCylinder.comparison K).hom ((RealizedCylinder.coordinates K).hom z))) =
    (sSetTopAdj.counit.app X).hom ((SSet.toTop.map e).hom z)
  rw [RealizedCylinder.comparison_coordinates]

/-- Continuous cylinders and singular-valued simplicial cylinders are exactly
equivalent, with the constructed evaluation formula as inverse. -/
def singularCylinderEquiv (K : SSet.{0}) (X : TopCat.{0}) :
    C(unitInterval × SSet.toTop.obj K, X) ≃ (K ⊗ Δ[1] ⟶ TopCat.toSSet.obj X) where
  toFun := singularCylinderMap
  invFun := evaluateSingularCylinder
  left_inv H := by
    apply ContinuousMap.ext
    rintro ⟨t, x⟩
    exact evaluate_singularCylinderMap H t x
  right_inv := singularCylinderMap_evaluate

/-- Equality of evaluated continuous cylinders detects equality of the actual
singular-valued simplicial maps. -/
theorem evaluateSingularCylinder_injective {K : SSet.{0}} {X : TopCat.{0}} :
    Function.Injective (evaluateSingularCylinder (K := K) (X := X)) :=
  (singularCylinderEquiv K X).symm.injective

end

end Thomason.Construction

end

end OAI
