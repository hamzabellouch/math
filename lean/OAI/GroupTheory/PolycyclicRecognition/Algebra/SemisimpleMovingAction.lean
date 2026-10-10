import OAI.GroupTheory.PolycyclicRecognition.Algebra.InnerCentralizerProduct
import OAI.GroupTheory.PolycyclicRecognition.Algebra.LinearConjugationCentralizer

namespace OAI

/-! # Equivariance of the centralizer product decomposition -/

noncomputable section
namespace PolycyclicRecognition
attribute [local instance] LieRing.ofAssociativeRing polynomialSubalgebraGroup
variable {L : Type} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]

omit [FiniteDimensional ℝ L] in
theorem lieEquiv_map_ad_eq_zero (T : L ≃ₗ⁅ℝ⁆ L) (x : L)
    (hx : LieAlgebra.ad ℝ L x = 0) : LieAlgebra.ad ℝ L (T x) = 0 := by
  apply LinearMap.ext
  intro y
  have hh : ⁅x, T.symm y⁆ = 0 := LinearMap.congr_fun hx (T.symm y)
  change ⁅T x, y⁆ = 0
  rw [← T.apply_symm_apply y, ← T.map_lie, hh, map_zero]

omit [FiniteDimensional ℝ L] in
theorem commuting_lieEquiv_preserves_movingCenter (S T : L ≃ₗ⁅ℝ⁆ L)
    (hST : Commute S.toLinearMap T.toLinearMap) (x : L)
    (hx : x ∈ semisimpleMovingCenter S) : T x ∈ semisimpleMovingCenter S := by
  refine ⟨lieEquiv_map_ad_eq_zero T x hx.1, ?_⟩
  obtain ⟨y, hy⟩ := hx.2
  refine ⟨T y, ?_⟩
  have hh : S (T y) = T (S y) := LinearMap.congr_fun hST.eq y
  change S (T y) - T y = T x
  rw [hh, ← map_sub]
  exact congrArg T hy

omit [FiniteDimensional ℝ L] in
theorem commuting_lieEquiv_preserves_innerCentralizer (S T : L ≃ₗ⁅ℝ⁆ L)
    (hST : Commute S.toLinearMap T.toLinearMap) (x : L)
    (hx : x ∈ innerCentralizerLieSubalgebra S) : T x ∈ innerCentralizerLieSubalgebra S := by
  have hh : S (T x) = T (S x) := LinearMap.congr_fun hST.eq x
  change LieAlgebra.ad ℝ L (S (T x) - T x) = 0
  rw [hh, ← map_sub]
  exact lieEquiv_map_ad_eq_zero T _ hx

theorem semisimple_projection_commutes (S T : L ≃ₗ⁅ℝ⁆ L)
    (hS : Module.End.IsSemisimple S.toLinearMap)
    (hST : Commute S.toLinearMap T.toLinearMap) (x : L) :
    semisimpleOneProjection S.toLinearMap hS (T x) =
      T (semisimpleOneProjection S.toLinearMap hS x) :=
  LinearMap.congr_fun (semisimpleKernelProjection_commute (S.toLinearMap - 1) T.toLinearMap
    (semisimple_sub_one S.toLinearMap hS) (hST.sub_left (Commute.one_left _))).eq x

variable [P : PolynomialExponentialCoordinates L]

def semisimpleMovingGroupAction (S T : L ≃ₗ⁅ℝ⁆ L)
    (hST : Commute S.toLinearMap T.toLinearMap) :
    MulAut (semisimpleMovingCenter S) :=
  polynomialSubalgebraEquiv _ _ T
    (commuting_lieEquiv_preserves_movingCenter S T hST)
    (commuting_lieEquiv_preserves_movingCenter S T.symm
      (linear_commute_symm T.toLinearEquiv S.toLinearMap hST))

def innerCentralizerGroupAction (S T : L ≃ₗ⁅ℝ⁆ L)
    (hST : Commute S.toLinearMap T.toLinearMap) :
    MulAut (innerCentralizerLieSubalgebra S) :=
  polynomialSubalgebraEquiv _ _ T
    (commuting_lieEquiv_preserves_innerCentralizer S T hST)
    (commuting_lieEquiv_preserves_innerCentralizer S T.symm
      (linear_commute_symm T.toLinearEquiv S.toLinearMap hST))

theorem movingGroupProjection_equivariant (S T : L ≃ₗ⁅ℝ⁆ L)
    (hS : Module.End.IsSemisimple S.toLinearMap)
    (hST : Commute S.toLinearMap T.toLinearMap) (x : innerCentralizerLieSubalgebra S) :
    innerCentralizerMovingGroupProjection S hS (innerCentralizerGroupAction S T hST x) =
      semisimpleMovingGroupAction S T hST (innerCentralizerMovingGroupProjection S hS x) := by
  apply Subtype.ext
  change T x - semisimpleOneProjection S.toLinearMap hS (T x) =
    T ((x : L) - semisimpleOneProjection S.toLinearMap hS x)
  rw [semisimple_projection_commutes S T hS hST, map_sub]

end PolycyclicRecognition

end

end OAI
