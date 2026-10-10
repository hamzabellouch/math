import OAI.Geometry.SingularHomology.SimplexCoordinates
import OAI.Geometry.SingularHomology.SingularUniversalFinsupp
import OAI.Geometry.SingularHomology.SingularChainsFinsuppBoundary
import OAI.Geometry.SingularHomology.SingularAcyclicModels

namespace OAI

noncomputable section

open CategoryTheory Simplicial Opposite

namespace Problem340.SingularUniversalOperator

def faceMap (n : ℕ) (i : Fin (n + 2)) : simplex n ⟶ simplex (n + 1) :=
  TopCat.ofHom ⟨Convexity.StdSimplex.map i.succAbove, Convexity.StdSimplex.continuous_map ℝ i.succAbove⟩

def faceSum (n : ℕ) (u : (chainsFunctor n).obj (simplex n)) :
    (chainsFunctor n).obj (simplex (n + 1)) :=
  ∑ i : Fin (n + 2), (-1 : ℝ) ^ i.val • ((chainsFunctor n).map (faceMap n i)).hom u

@[simp]
theorem operator_identity_apply {n m : ℕ} (u : (chainsFunctor m).obj (simplex n)) (r : ℝ) :
    ((operator n m u).app (simplex n)).hom ((identityGenerator n).hom r) = r • u := by
  have h := congrArg (fun k : ModuleCat.of ℝ ℝ ⟶ (chainsFunctor m).obj (simplex n) =>
    k.hom r) (identityGenerator_operator u)
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom,
    LinearMap.toSpanSingleton_apply] using! h

theorem operator_identity_boundary (n : ℕ) (u : (chainsFunctor n).obj (simplex n)) :
    ((operator n n u).app (simplex (n + 1))).hom
      (((realSingularChainComplex (simplex (n + 1))).d (n + 1) n).hom
        ((identityGenerator (n + 1)).hom 1)) = faceSum n u := by
  change ((operator n n u).app (simplex (n + 1))).hom
    (((realSingularChainComplex (simplex (n + 1))).d (n + 1) n).hom
      (SingularChainFormulas.simplexChain (ContinuousMap.id _))) = _
  rw [SingularChainFormulas.simplexChain_boundary_real]
  simp only [map_sum, map_smul, faceSum]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  change ((operator n n u).app (simplex (n + 1))).hom
    (realSingularGenerator (SingularChainFormulas.face (ContinuousMap.id _) i) 1) = _
  rw [operator_realSingularGenerator, one_smul]
  rfl

def BoundaryCompatible (u : ∀ n, (chainsFunctor n).obj (simplex n)) : Prop :=
  ∀ n, ((realSingularChainComplex (simplex (n + 1))).d (n + 1) n).hom (u (n + 1)) =
    faceSum n (u n)

theorem operator_comm (u : ∀ n, (chainsFunctor n).obj (simplex n))
    (hu : BoundaryCompatible u) (n : ℕ) :
    operator (n + 1) (n + 1) (u (n + 1)) ≫ SingularAcyclicModels.complex.d (n + 1) n =
      SingularAcyclicModels.complex.d (n + 1) n ≫ operator n n (u n) := by
  apply natTrans_ext_apply
  change ((realSingularChainComplex (simplex (n + 1))).d (n + 1) n).hom
      (((operator (n + 1) (n + 1) (u (n + 1))).app (simplex (n + 1))).hom
        ((identityGenerator (n + 1)).hom 1)) =
    ((operator n n (u n)).app (simplex (n + 1))).hom
      (((realSingularChainComplex (simplex (n + 1))).d (n + 1) n).hom
        ((identityGenerator (n + 1)).hom 1))
  rw [operator_identity_apply, one_smul, operator_identity_boundary]
  exact hu n

def chainMap (u : ∀ n, (chainsFunctor n).obj (simplex n)) (hu : BoundaryCompatible u) :
    SingularAcyclicModels.singularFunctor ⟶ SingularAcyclicModels.singularFunctor :=
  SingularAcyclicModels.operator (fun n => operator n n (u n)) (operator_comm u hu)

@[simp]
theorem chainMap_app_f (u : ∀ n, (chainsFunctor n).obj (simplex n))
    (hu : BoundaryCompatible u) (X : TopCat) (n : ℕ) :
    ((chainMap u hu).app X).f n = (operator n n (u n)).app X := rfl

theorem chainMap_zero (u : ∀ n, (chainsFunctor n).obj (simplex n))
    (hu : BoundaryCompatible u) (hzero : u 0 = (identityGenerator 0).hom 1) (X : TopCat) :
    ((chainMap u hu).app X).f 0 = 𝟙 ((SingularAcyclicModels.singularFunctor.obj X).X 0) := by
  have h : operator 0 0 (u 0) = 𝟙 (chainsFunctor 0) := by
    apply natTrans_ext_apply
    rw [operator_identity_apply, one_smul, hzero]
    rfl
  exact congrArg (fun k => k.app X) h

def chainMapHomotopy (u : ∀ n, (chainsFunctor n).obj (simplex n))
    (hu : BoundaryCompatible u) (hzero : u 0 = (identityGenerator 0).hom 1) (X : TopCat) :
    Homotopy ((chainMap u hu).app X) (𝟙 (SingularAcyclicModels.singularFunctor.obj X)) :=
  SingularAcyclicModels.homotopyApp (chainMap u hu) (𝟙 _) (chainMap_zero u hu hzero) X

theorem chainMapHomotopy_naturality (u : ∀ n, (chainsFunctor n).obj (simplex n))
    (hu : BoundaryCompatible u) (hzero : u 0 = (identityGenerator 0).hom 1)
    {X Y : TopCat} (f : X ⟶ Y) (i j : ℕ) :
    (SingularAcyclicModels.singularFunctor.map f).f i ≫
        (chainMapHomotopy u hu hzero Y).hom i j =
      (chainMapHomotopy u hu hzero X).hom i j ≫
        (SingularAcyclicModels.singularFunctor.map f).f j :=
  SingularAcyclicModels.homotopyApp_naturality (chainMap u hu) (𝟙 _)
    (chainMap_zero u hu hzero) f i j

theorem chainMap_homologyMap_eq_id (u : ∀ n, (chainsFunctor n).obj (simplex n))
    (hu : BoundaryCompatible u) (hzero : u 0 = (identityGenerator 0).hom 1)
    (X : TopCat) (n : ℕ) :
    HomologicalComplex.homologyMap ((chainMap u hu).app X) n =
      𝟙 ((SingularAcyclicModels.singularFunctor.obj X).homology n) := by
  simpa only [HomologicalComplex.homologyMap_id] using
    (chainMapHomotopy u hu hzero X).homologyMap_eq n

end Problem340.SingularUniversalOperator

end

end OAI
