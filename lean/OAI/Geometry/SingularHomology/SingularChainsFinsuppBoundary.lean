import OAI.Geometry.SingularHomology.SimplexCoordinates
import OAI.Geometry.SingularHomology.HomologyCycle
import OAI.Geometry.SingularHomology.SingularChainsFinsupp

namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits Simplicial Opposite

namespace Problem340.SingularChainFormulas

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

def simplexChain {n : ℕ} (σ : C(Convexity.StdSimplex ℝ (Fin (n + 1)), X)) :
    (realSingularChainComplex X).X n :=
  ((TopCat.toSSet.obj (TopCat.of X)).ιChainComplex (R := ModuleCat.of ℝ ℝ)
    ((TopCat.toSSetObjEquiv (TopCat.of X) (op ⦋n⦌)).symm σ)).hom (1 : ℝ)

def face {n : ℕ} (σ : C(Convexity.StdSimplex ℝ (Fin (n + 2)), X)) (i : Fin (n + 2)) :
    C(Convexity.StdSimplex ℝ (Fin (n + 1)), X) :=
  σ.comp ⟨Convexity.StdSimplex.map i.succAbove, Convexity.StdSimplex.continuous_map ℝ i.succAbove⟩

lemma simplexChain_boundary {n : ℕ} (σ : C(Convexity.StdSimplex ℝ (Fin (n + 2)), X)) :
    ((realSingularChainComplex X).d (n + 1) n).hom (simplexChain σ) =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val • simplexChain (face σ i) := by
  let S := TopCat.toSSet.obj (TopCat.of X)
  let s := (TopCat.toSSetObjEquiv (TopCat.of X) (op ⦋n + 1⦌)).symm σ
  have h := congrArg (fun k : ModuleCat.of ℝ ℝ ⟶ (S.chainComplex
      (ModuleCat.of ℝ ℝ)).X n => k.hom (1 : ℝ)) (S.ιChainComplex_d (ModuleCat.of ℝ ℝ) s)
  have hsface (i : Fin (n + 2)) : S.δ i s =
      (TopCat.toSSetObjEquiv (TopCat.of X) (op ⦋n⦌)).symm (face σ i) := by
    apply (TopCat.toSSetObjEquiv (TopCat.of X) (op ⦋n⦌)).injective
    ext p
    rfl
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_sum,
    LinearMap.sum_apply, ModuleCat.hom_zsmul, LinearMap.smul_apply, hsface, S, s, SSet.chainComplex] at h
  convert h using 1 <;> rfl

lemma simplexChain_boundary_real {n : ℕ}
    (σ : C(Convexity.StdSimplex ℝ (Fin (n + 2)), X)) :
    ((realSingularChainComplex X).d (n + 1) n).hom (simplexChain σ) =
      ∑ i : Fin (n + 2), (-1 : ℝ) ^ i.val • simplexChain (face σ i) := by
  simpa only [← Int.cast_smul_eq_zsmul ℝ, Int.cast_pow, Int.cast_neg, Int.cast_one]
    using simplexChain_boundary σ

lemma simplexChain_map (f : C(X, Y)) {n : ℕ}
    (σ : C(Convexity.StdSimplex ℝ (Fin (n + 1)), X)) :
    ((realSingularChainMap f f.continuous).f n).hom (simplexChain σ) =
      simplexChain (f.comp σ) := by
  let S := TopCat.toSSet.obj (TopCat.of X)
  let T := TopCat.toSSet.obj (TopCat.of Y)
  let s := (TopCat.toSSetObjEquiv (TopCat.of X) (op ⦋n⦌)).symm σ
  let φ := TopCat.toSSet.map (TopCat.ofHom f)
  have h := congrArg (fun k : ModuleCat.of ℝ ℝ ⟶ (T.chainComplex
      (ModuleCat.of ℝ ℝ)).X n => k.hom (1 : ℝ))
    (SSet.ι_chainComplexMap_f S T φ (ModuleCat.of ℝ ℝ) s)
  exact h

end Problem340.SingularChainFormulas

namespace Problem340

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

abbrev realSingularFace {n : ℕ} (σ : RealSingularSimplex X (n + 1))
    (i : Fin (n + 2)) : RealSingularSimplex X n :=
  SingularChainFormulas.face σ i

lemma realSingularGenerator_eq_smul {n : ℕ} (σ : RealSingularSimplex X n) (r : ℝ) :
    realSingularGenerator σ r = r • SingularChainFormulas.simplexChain σ := by
  change realSingularGenerator σ r = r • realSingularGenerator σ 1
  simpa only [smul_eq_mul, mul_one] using (realSingularGenerator σ).map_smul r (1 : ℝ)

lemma realSingularGenerator_boundary {n : ℕ} (σ : RealSingularSimplex X (n + 1))
    (r : ℝ) :
    ((realSingularChainComplex X).d (n + 1) n).hom (realSingularGenerator σ r) =
      ∑ i : Fin (n + 2), (-1 : ℝ) ^ i.val • realSingularGenerator (realSingularFace σ i) r := by
  simp only [realSingularGenerator_eq_smul, map_smul,
    SingularChainFormulas.simplexChain_boundary_real, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  exact smul_comm r ((-1 : ℝ) ^ i.val) _

lemma realSingularGenerator_map (f : C(X, Y)) {n : ℕ}
    (σ : RealSingularSimplex X n) (r : ℝ) :
    ((realSingularChainMap f f.continuous).f n).hom (realSingularGenerator σ r) =
      realSingularGenerator (f.comp σ) r := by
  simp only [realSingularGenerator_eq_smul, map_smul,
    SingularChainFormulas.simplexChain_map]

def realSingularBoundary (X : Type) [TopologicalSpace X] (n : ℕ) :
    RealSingularChains X (n + 1) →ₗ[ℝ] RealSingularChains X n :=
  Finsupp.linearCombination ℝ fun σ =>
    ∑ i : Fin (n + 2), (-1 : ℝ) ^ i.val • Finsupp.single (realSingularFace σ i) 1

def realSingularPushforward (f : C(X, Y)) (n : ℕ) :
    RealSingularChains X n →ₗ[ℝ] RealSingularChains Y n :=
  Finsupp.lmapDomain ℝ ℝ (fun σ => f.comp σ)

@[simp]
lemma realSingularBoundary_single (n : ℕ) (σ : RealSingularSimplex X (n + 1)) (r : ℝ) :
    realSingularBoundary X n (Finsupp.single σ r) =
      r • ∑ i : Fin (n + 2), (-1 : ℝ) ^ i.val • Finsupp.single (realSingularFace σ i) 1 :=
  Finsupp.linearCombination_single ℝ r σ

@[simp]
lemma realSingularPushforward_single (f : C(X, Y)) (n : ℕ)
    (σ : RealSingularSimplex X n) (r : ℝ) :
    realSingularPushforward f n (Finsupp.single σ r) = Finsupp.single (f.comp σ) r := by
  simp [realSingularPushforward]

lemma singularChainsFinsuppEquiv_boundary (n : ℕ) (c : RealSingularChains X (n + 1)) :
    singularChainsFinsuppEquiv X n (realSingularBoundary X n c) =
      ((realSingularChainComplex X).d (n + 1) n).hom
        (singularChainsFinsuppEquiv X (n + 1) c) := by
  have h : (singularChainsFinsuppEquiv X n).toLinearMap.comp (realSingularBoundary X n) =
      ((realSingularChainComplex X).d (n + 1) n).hom.comp
        (singularChainsFinsuppEquiv X (n + 1)).toLinearMap := by
    apply Finsupp.lhom_ext'
    intro σ
    apply LinearMap.ext
    intro r
    change singularChainsFinsuppEquiv X n (realSingularBoundary X n (Finsupp.single σ r)) =
      ((realSingularChainComplex X).d (n + 1) n).hom
        (singularChainsFinsuppEquiv X (n + 1) (Finsupp.single σ r))
    simp only [
      realSingularBoundary_single, map_smul, map_sum,
      singularChainsFinsuppEquiv_single, realSingularGenerator_eq_smul]
    simp only [one_smul]
    rw [SingularChainFormulas.simplexChain_boundary_real]
  exact LinearMap.congr_fun h c

lemma singularChainsFinsuppEquiv_pushforward (f : C(X, Y)) (n : ℕ)
    (c : RealSingularChains X n) :
    singularChainsFinsuppEquiv Y n (realSingularPushforward f n c) =
      ((realSingularChainMap f f.continuous).f n).hom
        (singularChainsFinsuppEquiv X n c) := by
  have h : (singularChainsFinsuppEquiv Y n).toLinearMap.comp (realSingularPushforward f n) =
      ((realSingularChainMap f f.continuous).f n).hom.comp
        (singularChainsFinsuppEquiv X n).toLinearMap := by
    apply Finsupp.lhom_ext'
    intro σ
    apply LinearMap.ext
    intro r
    change singularChainsFinsuppEquiv Y n (realSingularPushforward f n (Finsupp.single σ r)) =
      ((realSingularChainMap f f.continuous).f n).hom
        (singularChainsFinsuppEquiv X n (Finsupp.single σ r))
    simp only [realSingularPushforward_single, singularChainsFinsuppEquiv_single,
      realSingularGenerator_eq_smul, map_smul, SingularChainFormulas.simplexChain_map]
  exact LinearMap.congr_fun h c

lemma realSingularBoundary_squared (n : ℕ) (c : RealSingularChains X (n + 2)) :
    realSingularBoundary X n (realSingularBoundary X (n + 1) c) = 0 := by
  apply (singularChainsFinsuppEquiv X n).injective
  rw [map_zero, singularChainsFinsuppEquiv_boundary, singularChainsFinsuppEquiv_boundary]
  have h := congrArg (fun k : (realSingularChainComplex X).X (n + 2) ⟶
      (realSingularChainComplex X).X n =>
      k.hom (singularChainsFinsuppEquiv X (n + 2) c))
    ((realSingularChainComplex X).d_comp_d (n + 2) (n + 1) n)
  exact h

lemma realSingularBoundary_pushforward (f : C(X, Y)) (n : ℕ)
    (c : RealSingularChains X (n + 1)) :
    realSingularBoundary Y n (realSingularPushforward f (n + 1) c) =
      realSingularPushforward f n (realSingularBoundary X n c) := by
  apply (singularChainsFinsuppEquiv Y n).injective
  rw [singularChainsFinsuppEquiv_boundary, singularChainsFinsuppEquiv_pushforward,
    singularChainsFinsuppEquiv_pushforward, singularChainsFinsuppEquiv_boundary]
  have h := congrArg (fun k : (realSingularChainComplex X).X (n + 1) ⟶
      (realSingularChainComplex Y).X n =>
      k.hom (singularChainsFinsuppEquiv X (n + 1) c))
    ((realSingularChainMap f f.continuous).comm (n + 1) n)
  exact h

end Problem340

end

end OAI
