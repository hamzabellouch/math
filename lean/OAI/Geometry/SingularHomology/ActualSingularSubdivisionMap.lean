import OAI.Geometry.SingularHomology.ActualSingularSubdivision
import OAI.Geometry.SingularHomology.SingularUniversalChainMap

namespace OAI

noncomputable section

open CategoryTheory

namespace Problem340.ActualSingularSubdivision

theorem subdivisionChain_boundaryCompatible :
    SingularUniversalOperator.BoundaryCompatible subdivisionChain := by
  intro n
  exact subdivisionChain_boundary n

def subdivisionChainMap :
    SingularAcyclicModels.singularFunctor ⟶ SingularAcyclicModels.singularFunctor :=
  SingularUniversalOperator.chainMap subdivisionChain subdivisionChain_boundaryCompatible

@[simp]
theorem subdivisionChainMap_f (X : TopCat) (n : ℕ) :
    (subdivisionChainMap.app X).f n = (subdivision n).app X := rfl

@[simp]
theorem subdivisionChainMap_zero (X : TopCat) :
    (subdivisionChainMap.app X).f 0 =
      𝟙 ((SingularAcyclicModels.singularFunctor.obj X).X 0) :=
  SingularUniversalOperator.chainMap_zero subdivisionChain subdivisionChain_boundaryCompatible
    subdivisionChain_zero X

def subdivisionChainHomotopy (X : TopCat) :
    Homotopy (subdivisionChainMap.app X)
      (𝟙 (SingularAcyclicModels.singularFunctor.obj X)) :=
  SingularUniversalOperator.chainMapHomotopy subdivisionChain
    subdivisionChain_boundaryCompatible subdivisionChain_zero X

theorem subdivisionChainHomotopy_naturality {X Y : TopCat} (f : X ⟶ Y) (i j : ℕ) :
    (SingularAcyclicModels.singularFunctor.map f).f i ≫
        (subdivisionChainHomotopy Y).hom i j =
      (subdivisionChainHomotopy X).hom i j ≫
        (SingularAcyclicModels.singularFunctor.map f).f j :=
  SingularUniversalOperator.chainMapHomotopy_naturality subdivisionChain
    subdivisionChain_boundaryCompatible subdivisionChain_zero f i j

theorem subdivisionChainMap_homologyMap_eq_id (X : TopCat) (n : ℕ) :
    HomologicalComplex.homologyMap (subdivisionChainMap.app X) n =
      𝟙 ((SingularAcyclicModels.singularFunctor.obj X).homology n) :=
  SingularUniversalOperator.chainMap_homologyMap_eq_id subdivisionChain
    subdivisionChain_boundaryCompatible subdivisionChain_zero X n

theorem subdivisionChainMap_generator {X : Type} [TopologicalSpace X] (n : ℕ)
    (σ : RealSingularSimplex X n) :
    ((subdivisionChainMap.app (TopCat.of X)).f n).hom (realSingularGenerator σ 1) =
      ((realSingularChainMap σ σ.continuous).f n).hom (subdivisionChain n) :=
  subdivision_generator n σ

alias subdivisionChain_compatible := subdivisionChain_boundaryCompatible

abbrev chainMap := subdivisionChainMap

alias chainMap_app_f := subdivisionChainMap_f

alias chainMap_app_zero := subdivisionChainMap_zero

abbrev chainHomotopy := subdivisionChainHomotopy

alias chainHomotopy_naturality := subdivisionChainHomotopy_naturality

alias homologyMap_chainMap := subdivisionChainMap_homologyMap_eq_id

end Problem340.ActualSingularSubdivision

end

end OAI
