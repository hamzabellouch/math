import OAI.Geometry.SingularHomology.SimplexSingularRealization
import OAI.Geometry.SingularHomology.SingularUniversalFinsupp

namespace OAI

noncomputable section

open CategoryTheory

namespace Problem340.SingularSubdivisionIterateRealization

open SingularSubdivision SingularUniversalOperator SimplexSingularRealization

abbrev degreeOperator (n : ℕ) :=
  operator n n (realize n n (universalSubdivision n))

theorem operator_realize (k n : ℕ) (c : Chains (Simplex k) (n + 1)) :
    ((degreeOperator n).app (TopCat.of (Simplex k))).hom (realize k n c) =
      realize k n (subdivision (simplexCenters k) (n + 1) c) := by
  have h : ((degreeOperator n).app (TopCat.of (Simplex k))).hom.comp (realize k n) =
      (realize k n).comp (subdivision (simplexCenters k) (n + 1)) := by
    apply linearMap_ext
    intro v
    change ((degreeOperator n).app (TopCat.of (Simplex k))).hom
      (realize k n (generator v)) = realize k n
        (subdivision (simplexCenters k) (n + 1) (generator v))
    rw [realize_generator]
    change ((degreeOperator n).app (TopCat.of (Simplex k))).hom
      (realSingularGenerator (AffineSimplex.simplexRealizeMap v) 1) = _
    rw [operator_realSingularGenerator, one_smul, affineMap_realize]
    congr 1
    rw [universalSubdivision,
      mapVertices_subdivision _ _ _ (affine_centers v), mapVertices_generator]
    congr 2
    funext i
    exact AffineSimplex.simplexRealizeMap_vertex v i
  exact LinearMap.congr_fun h c

theorem operator_pushforward {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (n : ℕ) (f : C(X, Y)) (c : (realSingularChainComplex X).X n) :
    ((degreeOperator n).app (TopCat.of Y)).hom
      (((realSingularChainMap f f.continuous).f n).hom c) =
      ((realSingularChainMap f f.continuous).f n).hom
        (((degreeOperator n).app (TopCat.of X)).hom c) := by
  exact congrArg (fun g : (chainsFunctor n).obj (TopCat.of X) ⟶
      (chainsFunctor n).obj (TopCat.of Y) => g.hom c)
    ((degreeOperator n).naturality (TopCat.ofHom f))

theorem iterate_pushforward_realize {X : Type} [TopologicalSpace X]
    (k n r : ℕ) (f : C(Simplex k, X)) (c : Chains (Simplex k) (n + 1)) :
    ((((degreeOperator n).app (TopCat.of X)).hom)^[r])
      (((realSingularChainMap f f.continuous).f n).hom (realize k n c)) =
      ((realSingularChainMap f f.continuous).f n).hom
        (realize k n (((subdivision (simplexCenters k) (n + 1))^[r]) c)) := by
  induction r with
  | zero => rfl
  | succ r ih =>
      rw [Function.iterate_succ_apply', ih, operator_pushforward,
        operator_realize, Function.iterate_succ_apply']

theorem iterate_simplexChain {X : Type} [TopologicalSpace X]
    (n r : ℕ) (σ : C(Simplex n, X)) :
    ((((degreeOperator n).app (TopCat.of X)).hom)^[r])
      (SingularChainFormulas.simplexChain σ) =
      ((realSingularChainMap σ σ.continuous).f n).hom
        (realize n n (((subdivision (simplexCenters n) (n + 1))^[r])
          (generator (standardVertices n)))) := by
  have h := iterate_pushforward_realize n n r σ (generator (standardVertices n))
  rw [realize_standardVertices, SingularChainFormulas.simplexChain_map] at h
  simpa only [ContinuousMap.comp_id] using h

end Problem340.SingularSubdivisionIterateRealization

end

end OAI
