import OAI.CategoryTheory.Thomason.Gray.GrayMappingInterchangeEvaluation
import OAI.CategoryTheory.Thomason.Gray.SingularCylinderEquivalence
import OAI.CategoryTheory.Thomason.Simplicial.FinitePosetCoordinates
import OAI.CategoryTheory.Thomason.Simplicial.SingularCounitSurjectivity
import OAI.CategoryTheory.Thomason.Simplicial.SingularPathSpaceAdjunction
import OAI.CategoryTheory.Thomason.Simplicial.TopologicalDeformationTransport
import OAI.CategoryTheory.Thomason.Strict.StreetSingularWeakReflection

namespace OAI

section

/-! # Barycentric lifting tests for the actual Gray--Street comparison

These are consequences of the constructed topological lifting bridge.
They add no hypothesis to the main theorem and do not assert that an
arbitrary Gray projection has the displayed lifting property.
-/

namespace Thomason.Construction

open CategoryTheory

noncomputable section

/-- Singular boundary lifting forces the weak test both before and after
    singularization, without requiring the singular counit to be weak. -/
theorem weak_and_singular_weak_of_singular_boundary_rlp {X Y : TopCat.{0}} (f : X ⟶ Y)
    (hf : SSet.modelCategoryQuillen.I.rlp (TopCat.toSSet.map f)) :
    topologicalWeakEquivalences f ∧ realizationWeakEquivalences (TopCat.toSSet.map f) := by
  have h := (RealizationPrism.singular_boundary_rlp_iff f).mp hf
  exact ⟨CubicalLifting.weak_of_barycentric f h,
    RealizationPrism.singular_weak_of_boundary_lifting f h⟩

namespace RightGrayInput

variable {h : NormalizedSimplexIdentities} (G : RightGrayInput h)
  (aw : SimplexComplex.AlexanderWhitneyInput h)

/-- The concrete boundary lifting test on a realized strict Gray projection
    suffices for the actual simplicial Gray--Street comparison to be weak. -/
theorem nerveCylinder_weak_of_boundary_lifting (X : StrictOmegaCategory.{0})
    (hp : ∀ n, HasLiftingProperty (RealizationPrism.boundaryInclusion n)
      (SSet.toTop.map (h.streetNerve.map (G.projection.app X)))) :
    realizationWeakEquivalences (G.nerveCylinder aw X) :=
  (G.nerveCylinder_weak_iff_projection aw X).mpr
    (CubicalLifting.weak_of_barycentric _ hp)

/-- The same lifting test controls the original continuous comparison map,
    including all basepoints and positive homotopy groups. -/
theorem realizedCylinderComparison_weak_of_boundary_lifting (X : StrictOmegaCategory.{0})
    (hp : ∀ n, HasLiftingProperty (RealizationPrism.boundaryInclusion n)
      (SSet.toTop.map (h.streetNerve.map (G.projection.app X)))) :
    topologicalWeakEquivalences (G.realizedCylinderComparison aw X) :=
  (G.nerveCylinder_weak_iff aw X).mp (G.nerveCylinder_weak_of_boundary_lifting aw X hp)

end RightGrayInput

namespace NormalizedSimplexIdentities

/-- For strict full inclusions the lifting test implies precisely the
    Street weak test, using the actual closed subspace realization. -/
theorem fullInclusion_weak_of_boundary_lifting (h : NormalizedSimplexIdentities)
    (C : StrictOmegaCategory.{0}) (S : Set C)
    (hp : ∀ n, HasLiftingProperty (RealizationPrism.boundaryInclusion n)
      (SSet.toTop.map (h.streetNerve.map (C.fullInclusion S)))) :
    h.streetWeakEquivalences (C.fullInclusion S) :=
  CubicalLifting.weak_of_barycentric _ hp

end NormalizedSimplexIdentities

end

end Thomason.Construction

end

section

/-! # Gray homotopies in the actual singular path object of Street realization -/

namespace Thomason.Construction

open CategoryTheory MonoidalCategory
open scoped Simplicial

noncomputable section

namespace RightGrayInput

variable {h : NormalizedSimplexIdentities} (G : RightGrayInput h)
  (aw : SimplexComplex.AlexanderWhitneyInput h)

/-- The strict Gray homotopy transposed into the actual compact-open path
space of the Street realization. -/
def singularPathTranspose {X Y : StrictOmegaCategory.{0}} (P : G.cylinder.obj X ⟶ Y) :
    h.streetNerve.obj X ⟶ TopCat.toSSet.obj
      (continuousPathSpace (SSet.toTop.obj (h.streetNerve.obj Y))) :=
  sSetTopAdj.homEquiv _ _ (TopCat.ofHom
    (((G.realizedHomotopy aw P).toContinuousMap.comp ContinuousMap.prodSwap).curry))

/-- The path-space transpose recovers the original Street-nerve cylinder
followed by the actual realization/singular unit. -/
theorem singularPathTranspose_cylinder {X Y : StrictOmegaCategory.{0}}
    (P : G.cylinder.obj X ⟶ Y) :
    singularPathCylinderEquiv _ _ (G.singularPathTranspose aw P) =
      (G.nerveHomotopy aw P).h ≫ sSetTopAdj.unit.app (h.streetNerve.obj Y) := by
  let F : SSet.toTop.obj (h.streetNerve.obj X) ⟶
      continuousPathSpace (SSet.toTop.obj (h.streetNerve.obj Y)) :=
    TopCat.ofHom (((G.realizedHomotopy aw P).toContinuousMap.comp
      ContinuousMap.prodSwap).curry)
  change singularCylinderMap
      (continuousPathFamilyEquiv _ _ ((sSetTopAdj.homEquiv _ _).symm
        (sSetTopAdj.homEquiv _ _ F))) = _
  rw [(sSetTopAdj.homEquiv _ _).symm_apply_apply F]
  change singularCylinderMap (G.realizedHomotopy aw P).toContinuousMap = _
  exact singularCylinderMap_realizedHomotopy (G.nerveHomotopy aw P)

theorem singularPathTranspose_zero {X Y : StrictOmegaCategory.{0}}
    (P : G.cylinder.obj X ⟶ Y) :
    SSet.ι₀ ≫ singularPathCylinderEquiv _ _ (G.singularPathTranspose aw P) =
      h.streetNerve.map ((G.endpoint false).app X ≫ P) ≫
        sSetTopAdj.unit.app (h.streetNerve.obj Y) := by
  rw [G.singularPathTranspose_cylinder aw, ← Category.assoc, (G.nerveHomotopy aw P).h₀]

theorem singularPathTranspose_one {X Y : StrictOmegaCategory.{0}}
    (P : G.cylinder.obj X ⟶ Y) :
    SSet.ι₁ ≫ singularPathCylinderEquiv _ _ (G.singularPathTranspose aw P) =
      h.streetNerve.map ((G.endpoint true).app X ≫ P) ≫
        sSetTopAdj.unit.app (h.streetNerve.obj Y) := by
  rw [G.singularPathTranspose_cylinder aw, ← Category.assoc, (G.nerveHomotopy aw P).h₁]

end RightGrayInput

/-- Weak equivalence of the actual singular internal-hom path map reflects
the original topological weak test, with no singular-counit assumption. -/
theorem weak_of_singular_path_internalHom {X Y : TopCat.{0}} (p : X ⟶ Y)
    (hp : realizationWeakEquivalences
      ((ihom (Δ[1] : SSet.{0})).map (TopCat.toSSet.map p))) :
    IsWeakHomotopyEquivalence p.hom := by
  have hpath : realizationWeakEquivalences (TopCat.toSSet.map (continuousPathMap p)) :=
    (realizationWeakEquivalences.arrow_mk_iso_iff (singularPathMapArrowIso p)).mpr hp
  exact (continuousPathMap_weak_iff p).mp
    (singular_realization_reflects_weak (continuousPathMap p) hpath)

namespace NormalizedSimplexIdentities

/-- The same exact reflection applies to the implemented strict Street nerve. -/
theorem streetWeak_of_singular_path_internalHom (h : NormalizedSimplexIdentities)
    {X Y : StrictOmegaCategory.{0}} (f : X ⟶ Y)
    (hf : realizationWeakEquivalences ((ihom (Δ[1] : SSet.{0})).map
      (TopCat.toSSet.map (SSet.toTop.map (h.streetNerve.map f))))) :
    h.streetWeakEquivalences f :=
  weak_of_singular_path_internalHom _ hf

end NormalizedSimplexIdentities

end

end Thomason.Construction

end

end OAI
