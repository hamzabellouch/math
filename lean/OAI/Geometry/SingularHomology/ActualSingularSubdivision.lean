import OAI.Geometry.SingularHomology.SimplexCoordinates
import OAI.Geometry.SingularHomology.BarycentricSubdivision
import OAI.Geometry.SingularHomology.AffineSingularRealization
import OAI.Geometry.SingularHomology.SingularUniversalOperator
import OAI.Geometry.SingularHomology.SimplexSingularRealization

namespace OAI

noncomputable section

open CategoryTheory Simplicial Opposite

namespace Problem340.ActualSingularSubdivision

open SingularSubdivision AffineSingularRealization

def identityChain (n : ℕ) :
    (realSingularChainComplex (StandardSimplex n)).X n :=
  (SingularUniversalOperator.identityGenerator n).hom 1

def subdivisionChain (n : ℕ) :
    (realSingularChainComplex (StandardSimplex n)).X n :=
  realizeInSimplex n n (universalSubdivision n)

def homotopyChain (n : ℕ) :
    (realSingularChainComplex (StandardSimplex n)).X (n + 1) :=
  realizeInSimplex n (n + 1) (universalHomotopy n)

def subdivision (n : ℕ) : SingularUniversalOperator.chainsFunctor n ⟶
    SingularUniversalOperator.chainsFunctor n :=
  SingularUniversalOperator.operator n n (subdivisionChain n)

def homotopyOperator (n : ℕ) : SingularUniversalOperator.chainsFunctor n ⟶
    SingularUniversalOperator.chainsFunctor (n + 1) :=
  SingularUniversalOperator.operator n (n + 1) (homotopyChain n)

lemma realize_standardVertices (n : ℕ) :
    realizeInSimplex n n (generator (standardVertices n)) =
      identityChain n := by
  rw [realizeInSimplex_generator]
  have h : AffineSimplex.simplexRealization (standardVertices n) =
      ContinuousMap.id (StandardSimplex n) := by
    ext p : 1
    exact AffineSimplex.simplexRealize_vertices p
  rw [h]
  rfl

@[simp] theorem subdivisionChain_zero :
    subdivisionChain 0 = identityChain 0 := by
  rw [subdivisionChain, universalSubdivision_zero, realize_standardVertices]

@[simp] theorem homotopyChain_zero : homotopyChain 0 = 0 := by
  rw [homotopyChain, universalHomotopy_zero, map_zero]

theorem subdivisionChain_boundary_affine (n : ℕ) :
    ((realSingularChainComplex (StandardSimplex (n + 1))).d (n + 1) n).hom
        (subdivisionChain (n + 1)) =
      ∑ i : Fin (n + 2), (-1 : ℝ) ^ i.val •
        realizeInSimplex (n + 1) n
          (mapVertices (Convexity.StdSimplex.map i.succAbove) (n + 1) (universalSubdivision n)) := by
  rw [subdivisionChain, ← realizeInSimplex_boundary, universalSubdivision_boundary, map_sum]
  simp only [map_smul]

theorem homotopyChain_boundary_affine (n : ℕ) :
    ((realSingularChainComplex (StandardSimplex (n + 1))).d (n + 2) (n + 1)).hom
        (homotopyChain (n + 1)) =
      identityChain (n + 1) -
        subdivisionChain (n + 1) -
        ∑ i : Fin (n + 2), (-1 : ℝ) ^ i.val •
          realizeInSimplex (n + 1) (n + 1)
            (mapVertices (Convexity.StdSimplex.map i.succAbove) (n + 2) (universalHomotopy n)) := by
  rw [homotopyChain, ← realizeInSimplex_boundary, universalHomotopy_boundary]
  simp only [map_sub, map_sum, map_smul, realize_standardVertices, subdivisionChain]

theorem subdivision_generator {X : Type} [TopologicalSpace X] (n : ℕ)
    (σ : RealSingularSimplex X n) :
    ((subdivision n).app (TopCat.of X)).hom (realSingularGenerator σ 1) =
      ((realSingularChainMap σ σ.continuous).f n).hom (subdivisionChain n) := by
  exact SingularUniversalOperator.operator_generator_apply (subdivisionChain n) (TopCat.of X)
    ((TopCat.toSSetObjEquiv (TopCat.of X) (op ⦋n⦌)).symm σ)

theorem homotopyOperator_generator {X : Type} [TopologicalSpace X] (n : ℕ)
    (σ : RealSingularSimplex X n) :
    ((homotopyOperator n).app (TopCat.of X)).hom (realSingularGenerator σ 1) =
      ((realSingularChainMap σ σ.continuous).f (n + 1)).hom (homotopyChain n) := by
  exact SingularUniversalOperator.operator_generator_apply (homotopyChain n) (TopCat.of X)
    ((TopCat.toSSetObjEquiv (TopCat.of X) (op ⦋n⦌)).symm σ)

lemma realize_eq_aux (k n : ℕ) :
    realizeInSimplex k n = SimplexSingularRealization.realize k n := by
  apply linearMap_ext
  intro p
  rw [realizeInSimplex_generator, SimplexSingularRealization.realize_generator]
  rfl

lemma realizeInSimplex_map (k l n : ℕ) (f : Fin (k + 1) → Fin (l + 1))
    (c : Chains (StandardSimplex k) (n + 1)) :
    ((realSingularChainMap (Convexity.StdSimplex.map f) (Convexity.StdSimplex.continuous_map ℝ f)).f n).hom
        (realizeInSimplex k n c) =
      realizeInSimplex l n (mapVertices (Convexity.StdSimplex.map f) (n + 1) c) := by
  rw [realize_eq_aux, realize_eq_aux]
  exact SimplexSingularRealization.map_realize k l n f c

theorem subdivisionChain_boundary (n : ℕ) :
    ((realSingularChainComplex (StandardSimplex (n + 1))).d (n + 1) n).hom
        (subdivisionChain (n + 1)) =
      ∑ i : Fin (n + 2), (-1 : ℝ) ^ i.val •
        ((realSingularChainMap (Convexity.StdSimplex.map i.succAbove)
          (Convexity.StdSimplex.continuous_map ℝ i.succAbove)).f n).hom (subdivisionChain n) := by
  rw [subdivisionChain_boundary_affine]
  apply Finset.sum_congr rfl
  intro i _
  rw [← realizeInSimplex_map]
  rfl

theorem homotopyChain_boundary (n : ℕ) :
    ((realSingularChainComplex (StandardSimplex (n + 1))).d (n + 2) (n + 1)).hom
        (homotopyChain (n + 1)) =
      identityChain (n + 1) - subdivisionChain (n + 1) -
        ∑ i : Fin (n + 2), (-1 : ℝ) ^ i.val •
          ((realSingularChainMap (Convexity.StdSimplex.map i.succAbove)
            (Convexity.StdSimplex.continuous_map ℝ i.succAbove)).f (n + 1)).hom (homotopyChain n) := by
  rw [homotopyChain_boundary_affine]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [← realizeInSimplex_map]
  rfl

theorem subdivision_zero : subdivision 0 = 𝟙 (SingularUniversalOperator.chainsFunctor 0) := by
  unfold subdivision
  rw [subdivisionChain_zero]
  exact SingularUniversalOperator.operator_unique
    (𝟙 (SingularUniversalOperator.chainsFunctor 0))

lemma realizeInSimplex_affineMap (k l n : ℕ) (p : Fin (k + 1) → StandardSimplex l)
    (c : Chains (StandardSimplex k) (n + 1)) :
    ((realSingularChainMap (AffineSimplex.simplexRealizeMap p)
      (AffineSimplex.simplexRealizeMap p).continuous).f n).hom
        (realizeInSimplex k n c) =
      realizeInSimplex l n (mapVertices (AffineSimplex.simplexRealizeMap p) (n + 1) c) := by
  rw [realize_eq_aux, realize_eq_aux]
  exact SimplexSingularRealization.affineMap_realize k l n p c

theorem subdivision_realize (k n : ℕ) (c : Chains (StandardSimplex k) (n + 1)) :
    ((subdivision n).app (TopCat.of (StandardSimplex k))).hom (realizeInSimplex k n c) =
      realizeInSimplex k n (SingularSubdivision.subdivision (simplexCenters k) (n + 1) c) := by
  have h : (((subdivision n).app (TopCat.of (StandardSimplex k))).hom).comp
      (realizeInSimplex k n) = (realizeInSimplex k n).comp
        (SingularSubdivision.subdivision (simplexCenters k) (n + 1)) := by
    apply linearMap_ext
    intro p
    change ((subdivision n).app (TopCat.of (StandardSimplex k))).hom
      (realizeInSimplex k n (generator p)) = _
    rw [realizeInSimplex_generator, subdivision_generator]
    change ((realSingularChainMap (AffineSimplex.simplexRealizeMap p)
      (AffineSimplex.simplexRealizeMap p).continuous).f n).hom
        (realizeInSimplex n n (universalSubdivision n)) = _
    rw [realizeInSimplex_affineMap, mapVertices_universalSubdivision]
    rfl
  exact LinearMap.congr_fun h c

theorem subdivision_pow_realize (k n m : ℕ)
    (c : Chains (StandardSimplex k) (n + 1)) :
    ((((subdivision n).app (TopCat.of (StandardSimplex k))).hom) ^ m)
        (realizeInSimplex k n c) =
      realizeInSimplex k n
        (((SingularSubdivision.subdivision (simplexCenters k) (n + 1)) ^ m) c) := by
  induction m with
  | zero => rfl
  | succ m ih =>
      rw [pow_succ', Module.End.mul_apply, ih, subdivision_realize,
        pow_succ', Module.End.mul_apply]

end Problem340.ActualSingularSubdivision

end

end OAI
