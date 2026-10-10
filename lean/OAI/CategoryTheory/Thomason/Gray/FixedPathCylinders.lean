import OAI.CategoryTheory.Thomason.Gray.SingularCylinderEquivalence
import OAI.CategoryTheory.Thomason.Simplicial.ConstructedPosetCosieves
import OAI.CategoryTheory.Thomason.Simplicial.SingularCounitSurjectivity

namespace OAI

section

/-! # The singular cylinder description of fixed-endpoint path families -/

namespace Thomason.Construction

open CategoryTheory MonoidalCategory
open scoped Simplicial

noncomputable section

theorem singularCylinderMap_one {K : SSet.{0}} {X : TopCat.{0}}
    (H : C(unitInterval × SSet.toTop.obj K, X)) :
    SSet.ι₁ ≫ singularCylinderMap H = sSetTopAdj.homEquiv K X
      (TopCat.ofHom ⟨fun x => H (1, x), H.continuous.comp (by fun_prop)⟩) := by
  rw [singularCylinderMap, ← sSetTopAdj.homEquiv_naturality_left]
  congr 1
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  change H (PrismBarycentric.realizationTime.hom
      ((SSet.toTop.map (CartesianMonoidalCategory.snd K Δ[1])).hom
        ((SSet.toTop.map SSet.ι₁).hom x)),
      (SSet.toTop.map (CartesianMonoidalCategory.fst K Δ[1])).hom
        ((SSet.toTop.map SSet.ι₁).hom x)) = H (1, x)
  rw [← RealizedCylinder.comparison_one, RealizedCylinder.comparison_time,
    RealizedCylinder.comparison_first]

def fixedPathFamily {K : SSet.{0}} {X : TopCat.{0}} {x y : X}
    (f : K ⟶ TopCat.toSSet.obj (TopCat.of (Path x y))) :
    C(unitInterval × SSet.toTop.obj K, X) where
  toFun z := ((sSetTopAdj.homEquiv K _).symm f).hom z.2 z.1
  continuous_toFun := (Path.continuous_uncurry_iff.mpr
    ((sSetTopAdj.homEquiv K _).symm f).hom.continuous).comp continuous_swap

def fixedPathCylinder {K : SSet.{0}} {X : TopCat.{0}} {x y : X}
    (f : K ⟶ TopCat.toSSet.obj (TopCat.of (Path x y))) :
    K ⊗ Δ[1] ⟶ TopCat.toSSet.obj X := singularCylinderMap (fixedPathFamily f)

theorem fixedPathCylinder_evaluate {K : SSet.{0}} {X : TopCat.{0}} {x y : X}
    (f : K ⟶ TopCat.toSSet.obj (TopCat.of (Path x y))) (t : unitInterval)
    (z : SSet.toTop.obj K) :
    evaluateSingularCylinder (fixedPathCylinder f) (t, z) =
      ((sSetTopAdj.homEquiv K _).symm f).hom z t :=
  evaluate_singularCylinderMap (fixedPathFamily f) t z

theorem fixedPathCylinder_zero {K : SSet.{0}} {X : TopCat.{0}} {x y : X}
    (f : K ⟶ TopCat.toSSet.obj (TopCat.of (Path x y))) :
    SSet.ι₀ ≫ fixedPathCylinder f = SSet.const (TopCat.toSSetObj₀Equiv.symm x) := by
  rw [fixedPathCylinder, singularCylinderMap_zero, ← singular_adjoint_const]
  congr 1
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro z
  exact (((sSetTopAdj.homEquiv K _).symm f).hom z).source

theorem fixedPathCylinder_one {K : SSet.{0}} {X : TopCat.{0}} {x y : X}
    (f : K ⟶ TopCat.toSSet.obj (TopCat.of (Path x y))) :
    SSet.ι₁ ≫ fixedPathCylinder f = SSet.const (TopCat.toSSetObj₀Equiv.symm y) := by
  rw [fixedPathCylinder, singularCylinderMap_one, ← singular_adjoint_const]
  congr 1
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro z
  exact (((sSetTopAdj.homEquiv K _).symm f).hom z).target

theorem fixedPathCylinder_naturality {A K : SSet.{0}} {X : TopCat.{0}} {x y : X}
    (i : A ⟶ K) (f : K ⟶ TopCat.toSSet.obj (TopCat.of (Path x y))) :
    fixedPathCylinder (i ≫ f) = i ▷ Δ[1] ≫ fixedPathCylinder f := by
  unfold fixedPathCylinder
  rw [singularCylinderMap_naturality]
  congr 1
  apply ContinuousMap.ext
  rintro ⟨t, z⟩
  change ((sSetTopAdj.homEquiv A _).symm (i ≫ f)).hom z t = _
  rw [sSetTopAdj.homEquiv_naturality_left_symm]
  rfl

theorem fixedPathCylinder_postcomp {K : SSet.{0}} {X Y : TopCat.{0}}
    (p : X ⟶ Y) {x y : X}
    (f : K ⟶ TopCat.toSSet.obj (TopCat.of (Path x y))) :
    fixedPathCylinder (f ≫ TopCat.toSSet.map (TopCat.ofHom (PathSpace.map p.hom))) =
      fixedPathCylinder f ≫ TopCat.toSSet.map p := by
  unfold fixedPathCylinder
  rw [singularCylinderMap_postcomp]
  congr 1
  apply ContinuousMap.ext
  rintro ⟨t, z⟩
  change ((sSetTopAdj.homEquiv K _).symm
      (f ≫ TopCat.toSSet.map (TopCat.ofHom (PathSpace.map p.hom)))).hom z t = _
  rw [sSetTopAdj.homEquiv_naturality_right_symm]
  rfl

/-- An evaluated cylinder with constant endpoints is a continuous family of
paths with those endpoints. -/
def fixedPathRealization {K : SSet.{0}} {X : TopCat.{0}} {x y : X}
    (e : K ⊗ Δ[1] ⟶ TopCat.toSSet.obj X)
    (h₀ : SSet.ι₀ ≫ e = SSet.const (TopCat.toSSetObj₀Equiv.symm x))
    (h₁ : SSet.ι₁ ≫ e = SSet.const (TopCat.toSSetObj₀Equiv.symm y)) :
    SSet.toTop.obj K ⟶ TopCat.of (Path x y) := TopCat.ofHom {
  toFun z := {
    toFun t := evaluateSingularCylinder e (t, z)
    continuous_toFun := (evaluateSingularCylinder e).continuous.comp (by fun_prop)
    source' := by
      rw [evaluateSingularCylinder_zero, h₀, ← singular_adjoint_const,
        Equiv.symm_apply_apply]
      rfl
    target' := by
      rw [evaluateSingularCylinder_one, h₁, ← singular_adjoint_const,
        Equiv.symm_apply_apply]
      rfl }
  continuous_toFun := Path.continuous_uncurry_iff.mp
    ((evaluateSingularCylinder e).continuous.comp continuous_swap) }

end

end Thomason.Construction

end

end OAI
