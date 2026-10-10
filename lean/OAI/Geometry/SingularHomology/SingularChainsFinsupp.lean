import OAI.Geometry.SingularHomology.SimplexCoordinates
import OAI.Geometry.SingularHomology.HomologyCycle

namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits Simplicial Opposite

namespace Problem340

abbrev RealSingularSimplex (X : Type) [TopologicalSpace X] (n : ℕ) :=
  C(Convexity.StdSimplex ℝ (Fin (n + 1)), X)

abbrev RealSingularChains (X : Type) [TopologicalSpace X] (n : ℕ) :=
  RealSingularSimplex X n →₀ ℝ

def simplicialChainsFinsuppEquiv (S : SSet) (n : ℕ) :
    (S _⦋n⦌ →₀ ℝ) ≃ₗ[ℝ] (S.chainComplex (ModuleCat.of ℝ ℝ)).X n :=
  ((ModuleCat.finsuppCoconeIsColimit ℝ ℝ (S _⦋n⦌)).coconePointUniqueUpToIso
    (S.isColimitChainComplexXCofan (ModuleCat.of ℝ ℝ) n)).toLinearEquiv

@[simp]
theorem simplicialChainsFinsuppEquiv_single (S : SSet) (n : ℕ)
    (σ : S _⦋n⦌) (r : ℝ) :
    simplicialChainsFinsuppEquiv S n (Finsupp.single σ r) =
      (S.ιChainComplex (R := ModuleCat.of ℝ ℝ) σ).hom r := by
  have h := (ModuleCat.finsuppCoconeIsColimit ℝ ℝ (S _⦋n⦌)).comp_coconePointUniqueUpToIso_hom
    (S.isColimitChainComplexXCofan (ModuleCat.of ℝ ℝ) n) (Discrete.mk σ)
  exact congrArg (fun f : ModuleCat.of ℝ ℝ ⟶ (S.chainComplex (ModuleCat.of ℝ ℝ)).X n =>
    f.hom r) h

def singularChainsFinsuppEquiv (X : Type) [TopologicalSpace X] (n : ℕ) :
    RealSingularChains X n ≃ₗ[ℝ] (realSingularChainComplex X).X n :=
  (Finsupp.domLCongr (TopCat.toSSetObjEquiv (TopCat.of X) (op ⦋n⦌)).symm).trans
    (simplicialChainsFinsuppEquiv (TopCat.toSSet.obj (TopCat.of X)) n)

def realSingularGenerator {X : Type} [TopologicalSpace X] {n : ℕ}
    (σ : RealSingularSimplex X n) : ℝ →ₗ[ℝ] (realSingularChainComplex X).X n :=
  ((TopCat.toSSet.obj (TopCat.of X)).ιChainComplex (R := ModuleCat.of ℝ ℝ)
    ((TopCat.toSSetObjEquiv (TopCat.of X) (op ⦋n⦌)).symm σ)).hom

@[simp]
theorem singularChainsFinsuppEquiv_single (X : Type) [TopologicalSpace X] (n : ℕ)
    (σ : RealSingularSimplex X n) (r : ℝ) :
    singularChainsFinsuppEquiv X n (Finsupp.single σ r) = realSingularGenerator σ r := by
  unfold singularChainsFinsuppEquiv realSingularGenerator
  erw [LinearEquiv.trans_apply, Finsupp.domLCongr_single]
  exact simplicialChainsFinsuppEquiv_single (TopCat.toSSet.obj (TopCat.of X)) n _ r

@[simp]
theorem singularChainsFinsuppEquiv_symm_generator (X : Type) [TopologicalSpace X] (n : ℕ)
    (σ : RealSingularSimplex X n) (r : ℝ) :
    (singularChainsFinsuppEquiv X n).symm (realSingularGenerator σ r) = Finsupp.single σ r := by
  rw [← singularChainsFinsuppEquiv_single X n σ r, LinearEquiv.symm_apply_apply]

def realSingularChainBasis (X : Type) [TopologicalSpace X] (n : ℕ) :
    Module.Basis (RealSingularSimplex X n) ℝ ((realSingularChainComplex X).X n) :=
  Finsupp.basisSingleOne.map (singularChainsFinsuppEquiv X n)

@[simp]
theorem realSingularChainBasis_apply (X : Type) [TopologicalSpace X] (n : ℕ)
    (σ : RealSingularSimplex X n) :
    realSingularChainBasis X n σ = realSingularGenerator σ 1 := by
  rw [realSingularChainBasis, Module.Basis.map_apply]
  exact singularChainsFinsuppEquiv_single X n σ 1

theorem realSingularChain_linearMap_ext {X : Type} [TopologicalSpace X] {n : ℕ}
    {V : Type*} [AddCommMonoid V] [Module ℝ V]
    {f g : (realSingularChainComplex X).X n →ₗ[ℝ] V}
    (h : ∀ σ : RealSingularSimplex X n,
      f (realSingularGenerator σ 1) = g (realSingularGenerator σ 1)) : f = g := by
  apply (realSingularChainBasis X n).ext
  simpa only [realSingularChainBasis_apply] using h

@[elab_as_elim]
theorem realSingularChain_induction {X : Type} [TopologicalSpace X] {n : ℕ}
    {P : (realSingularChainComplex X).X n → Prop}
    (hzero : P 0)
    (hadd : ∀ a b, P a → P b → P (a + b))
    (hgen : ∀ (σ : RealSingularSimplex X n) (r : ℝ), P (realSingularGenerator σ r))
    (z : (realSingularChainComplex X).X n) : P z := by
  obtain ⟨c, rfl⟩ := (singularChainsFinsuppEquiv X n).surjective z
  induction c using Finsupp.induction_linear with
  | zero => simpa only [map_zero] using hzero
  | add c d hc hd => simpa only [map_add] using hadd _ _ hc hd
  | single σ r => simpa only [singularChainsFinsuppEquiv_single] using hgen σ r

def realSingularChainLift {X : Type} [TopologicalSpace X] {n : ℕ}
    {V : Type*} [AddCommMonoid V] [Module ℝ V]
    (v : RealSingularSimplex X n → V) : (realSingularChainComplex X).X n →ₗ[ℝ] V :=
  (Finsupp.linearCombination ℝ v).comp (singularChainsFinsuppEquiv X n).symm.toLinearMap

@[simp]
theorem realSingularChainLift_generator {X : Type} [TopologicalSpace X] {n : ℕ}
    {V : Type*} [AddCommMonoid V] [Module ℝ V]
    (v : RealSingularSimplex X n → V) (σ : RealSingularSimplex X n) (r : ℝ) :
    realSingularChainLift v (realSingularGenerator σ r) = r • v σ := by
  change Finsupp.linearCombination ℝ v ((singularChainsFinsuppEquiv X n).symm _) = _
  rw [← singularChainsFinsuppEquiv_single X n σ r, LinearEquiv.symm_apply_apply]
  simp

theorem realSingularChainLift_unique {X : Type} [TopologicalSpace X] {n : ℕ}
    {V : Type*} [AddCommMonoid V] [Module ℝ V]
    (f : (realSingularChainComplex X).X n →ₗ[ℝ] V) :
    realSingularChainLift (fun σ => f (realSingularGenerator σ 1)) = f := by
  apply realSingularChain_linearMap_ext
  intro σ
  simp

end Problem340

end

end OAI
