import OAI.Geometry.SingularHomology.SimplexCoordinates
import OAI.Geometry.SingularHomology.HomologyCycle

namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits Simplicial Opposite

namespace Problem340.SingularUniversalOperator

abbrev chainsFunctor (n : ℕ) : TopCat ⥤ ModuleCat ℝ :=
  ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℝ)).obj
    (ModuleCat.of ℝ ℝ)) ⋙ HomologicalComplex.eval (ModuleCat ℝ) (ComplexShape.down ℕ) n

abbrev simplex (n : ℕ) : TopCat := TopCat.of (Convexity.StdSimplex ℝ (Fin (n + 1)))

def simplexMap {X : TopCat} {n : ℕ} (σ : (TopCat.toSSet.obj X) _⦋n⦌) : simplex n ⟶ X :=
  TopCat.ofHom (TopCat.toSSetObjEquiv X (op ⦋n⦌) σ)

@[simp]
theorem simplexMap_naturality {X Y : TopCat} (g : X ⟶ Y) {n : ℕ}
    (σ : (TopCat.toSSet.obj X) _⦋n⦌) :
    simplexMap ((TopCat.toSSet.map g).app (op ⦋n⦌) σ) = simplexMap σ ≫ g := by
  rfl

@[reassoc (attr := simp)]
theorem generator_map {X Y : TopCat} (g : X ⟶ Y) {n : ℕ}
    (σ : (TopCat.toSSet.obj X) _⦋n⦌) :
    (TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of ℝ ℝ) σ ≫
      (chainsFunctor n).map g =
    (TopCat.toSSet.obj Y).ιChainComplex (R := ModuleCat.of ℝ ℝ)
      ((TopCat.toSSet.map g).app (op ⦋n⦌) σ) :=
  SSet.ι_chainComplexMap_f (TopCat.toSSet.obj X) (TopCat.toSSet.obj Y)
    (TopCat.toSSet.map g) (ModuleCat.of ℝ ℝ) σ

def operator (n m : ℕ) (u : (chainsFunctor m).obj (simplex n)) :
    chainsFunctor n ⟶ chainsFunctor m where
  app X := Sigma.desc (fun σ : (TopCat.toSSet.obj X) _⦋n⦌ =>
    ModuleCat.ofHom (LinearMap.toSpanSingleton ℝ _ u) ≫
      (chainsFunctor m).map (simplexMap σ))
  naturality {X Y} g := by
    apply SSet.chainComplex_hom_ext
    intro σ
    erw [generator_map_assoc]
    dsimp only [SSet.ιChainComplex]
    erw [Sigma.ι_comp_desc, simplexMap_naturality, Functor.map_comp]
    erw [Sigma.ι_comp_desc_assoc]
    rfl

@[reassoc (attr := simp)]
theorem generator_operator {n m : ℕ} (u : (chainsFunctor m).obj (simplex n))
    (X : TopCat) (σ : (TopCat.toSSet.obj X) _⦋n⦌) :
    (TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of ℝ ℝ) σ ≫ (operator n m u).app X =
      ModuleCat.ofHom (LinearMap.toSpanSingleton ℝ _ u) ≫
        (chainsFunctor m).map (simplexMap σ) := by
  exact Sigma.ι_comp_desc _ _

@[simp]
theorem operator_generator_apply {n m : ℕ} (u : (chainsFunctor m).obj (simplex n))
    (X : TopCat) (σ : (TopCat.toSSet.obj X) _⦋n⦌) :
    ((operator n m u).app X).hom
      (((TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of ℝ ℝ) σ).hom 1) =
      ((chainsFunctor m).map (simplexMap σ)).hom u := by
  have h := congrArg (fun k : ModuleCat.of ℝ ℝ ⟶ (chainsFunctor m).obj X => k.hom 1)
    (generator_operator u X σ)
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom,
    LinearMap.toSpanSingleton_apply, one_smul] using! h

def identitySimplex (n : ℕ) : (TopCat.toSSet.obj (simplex n)) _⦋n⦌ :=
  (TopCat.toSSetObjEquiv (simplex n) (op ⦋n⦌)).symm (ContinuousMap.id _)

@[simp]
theorem simplexMap_identity (n : ℕ) : simplexMap (identitySimplex n) = 𝟙 (simplex n) := by
  rfl

def identityGenerator (n : ℕ) : ModuleCat.of ℝ ℝ ⟶ (chainsFunctor n).obj (simplex n) :=
  (TopCat.toSSet.obj (simplex n)).ιChainComplex (identitySimplex n)

@[simp]
theorem map_identitySimplex {X : TopCat} {n : ℕ} (σ : (TopCat.toSSet.obj X) _⦋n⦌) :
    (TopCat.toSSet.map (simplexMap σ)).app (op ⦋n⦌) (identitySimplex n) = σ := by
  apply (TopCat.toSSetObjEquiv X (op ⦋n⦌)).injective
  ext p
  rfl

@[reassoc (attr := simp)]
theorem identityGenerator_map {X : TopCat} {n : ℕ}
    (σ : (TopCat.toSSet.obj X) _⦋n⦌) :
    identityGenerator n ≫ (chainsFunctor n).map (simplexMap σ) =
      (TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of ℝ ℝ) σ := by
  unfold identityGenerator
  erw [generator_map, map_identitySimplex]

theorem natTrans_ext {n : ℕ} {F : TopCat ⥤ ModuleCat ℝ}
    {α β : chainsFunctor n ⟶ F}
    (h : identityGenerator n ≫ α.app (simplex n) =
      identityGenerator n ≫ β.app (simplex n)) : α = β := by
  apply NatTrans.ext
  funext X
  apply SSet.chainComplex_hom_ext
  intro σ
  erw [← identityGenerator_map σ, Category.assoc, Category.assoc,
    α.naturality, β.naturality]
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun k => k ≫ F.map (simplexMap σ)) h).trans (Category.assoc _ _ _))

@[reassoc (attr := simp)]
theorem identityGenerator_operator {n m : ℕ} (u : (chainsFunctor m).obj (simplex n)) :
    identityGenerator n ≫ (operator n m u).app (simplex n) =
      ModuleCat.ofHom (LinearMap.toSpanSingleton ℝ _ u) := by
  unfold identityGenerator
  erw [generator_operator, simplexMap_identity, CategoryTheory.Functor.map_id, Category.comp_id]

theorem natTrans_ext_apply {n : ℕ} {F : TopCat ⥤ ModuleCat ℝ}
    {α β : chainsFunctor n ⟶ F}
    (h : (α.app (simplex n)).hom ((identityGenerator n).hom 1) =
      (β.app (simplex n)).hom ((identityGenerator n).hom 1)) : α = β := by
  apply natTrans_ext
  apply ModuleCat.hom_ext
  apply LinearMap.ext_ring
  exact h

theorem operator_unique {n m : ℕ} (α : chainsFunctor n ⟶ chainsFunctor m) :
    operator n m ((α.app (simplex n)).hom ((identityGenerator n).hom 1)) = α := by
  apply natTrans_ext
  rw [identityGenerator_operator]
  apply ModuleCat.hom_ext
  apply LinearMap.ext_ring
  simp only [ModuleCat.hom_ofHom, LinearMap.toSpanSingleton_apply, one_smul,
    ModuleCat.hom_comp, LinearMap.comp_apply]

end Problem340.SingularUniversalOperator

end

end OAI
