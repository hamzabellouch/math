import OAI.Geometry.SingularHomology.SimplexCoordinates
import OAI.Geometry.SingularHomology.SingularUniversalOperator
import OAI.Geometry.SingularHomology.SingularChainsFinsupp

namespace OAI

noncomputable section

open CategoryTheory Simplicial Opposite

namespace Problem340.SingularUniversalOperator

theorem operator_realSingularGenerator {n m : ℕ}
    (u : (chainsFunctor m).obj (simplex n))
    {X : Type} [TopologicalSpace X] (σ : RealSingularSimplex X n) (r : ℝ) :
    ((operator n m u).app (TopCat.of X)).hom (realSingularGenerator σ r) =
      r • ((realSingularChainMap σ σ.continuous).f m).hom u := by
  have h := congrArg (fun k : ModuleCat.of ℝ ℝ ⟶ (chainsFunctor m).obj (TopCat.of X) =>
    k.hom r) (generator_operator u (TopCat.of X)
      ((TopCat.toSSetObjEquiv (TopCat.of X) (op ⦋n⦌)).symm σ))
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom,
    LinearMap.toSpanSingleton_apply, map_smul, simplexMap, Equiv.apply_symm_apply,
    realSingularGenerator] using! h

@[simp]
theorem operator_finsupp_single {n m : ℕ}
    (u : (chainsFunctor m).obj (simplex n))
    {X : Type} [TopologicalSpace X] (σ : RealSingularSimplex X n) (r : ℝ) :
    ((operator n m u).app (TopCat.of X)).hom
      (singularChainsFinsuppEquiv X n (Finsupp.single σ r)) =
      r • ((realSingularChainMap σ σ.continuous).f m).hom u := by
  rw [singularChainsFinsuppEquiv_single, operator_realSingularGenerator]

theorem identityGenerator_eq_finsupp (n : ℕ) (r : ℝ) :
    (identityGenerator n).hom r =
      singularChainsFinsuppEquiv (Convexity.StdSimplex ℝ (Fin (n + 1))) n
        (Finsupp.single (ContinuousMap.id _) r) := by
  rw [singularChainsFinsuppEquiv_single]
  rfl

theorem operator_eq_realSingularChainLift {n m : ℕ}
    (u : (chainsFunctor m).obj (simplex n)) (X : Type) [TopologicalSpace X] :
    ((operator n m u).app (TopCat.of X)).hom =
      realSingularChainLift (fun σ : RealSingularSimplex X n =>
        ((realSingularChainMap σ σ.continuous).f m).hom u) := by
  apply realSingularChain_linearMap_ext
  intro σ
  erw [operator_realSingularGenerator, realSingularChainLift_generator]

end Problem340.SingularUniversalOperator

end

end OAI
