import OAI.GroupTheory.PolycyclicRecognition.Algebra.SemisimpleCentralDecomposition

namespace OAI

/-! # The Lie algebra of the inner centralizer

Vectors centralizing S modulo the center form a Lie subalgebra. Their brackets
are actually fixed by S, which makes the fixed projection a Lie homomorphism.
-/

noncomputable section
namespace PolycyclicRecognition
attribute [local instance] LieRing.ofAssociativeRing
variable {L : Type} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]

omit [FiniteDimensional ℝ L] in
theorem bracket_fixed_of_central_differences (S : L ≃ₗ⁅ℝ⁆ L) (x y : L)
    (hx : LieAlgebra.ad ℝ L (S x - x) = 0)
    (hy : LieAlgebra.ad ℝ L (S y - y) = 0) : S ⁅x, y⁆ = ⁅x, y⁆ := by
  have hx' : ⁅S x, S y⁆ = ⁅x, S y⁆ := by
    have hh : ⁅S x - x, S y⁆ = 0 := LinearMap.congr_fun hx (S y)
    rw [sub_lie, sub_eq_zero] at hh
    exact hh
  have hy' : ⁅x, S y⁆ = ⁅x, y⁆ := by
    have hh : ⁅S y - y, x⁆ = 0 := LinearMap.congr_fun hy x
    have hh' : ⁅x, S y - y⁆ = 0 := by rw [← lie_skew, hh, neg_zero]
    rwa [lie_sub, sub_eq_zero] at hh'
  rw [S.map_lie, hx', hy']

def innerCentralizerLieSubalgebra (S : L ≃ₗ⁅ℝ⁆ L) : LieSubalgebra ℝ L where
  toSubmodule := ((LieAlgebra.ad ℝ L).toLinearMap.comp (S.toLinearMap - 1)).ker
  lie_mem' := by
    intro x y hx hy
    change LieAlgebra.ad ℝ L (S x - x) = 0 at hx
    change LieAlgebra.ad ℝ L (S y - y) = 0 at hy
    change LieAlgebra.ad ℝ L (S ⁅x, y⁆ - ⁅x, y⁆) = 0
    rw [bracket_fixed_of_central_differences S x y hx hy, sub_self, map_zero]

theorem fixed_projection_bracket (S : L ≃ₗ⁅ℝ⁆ L)
    (hS : Module.End.IsSemisimple S.toLinearMap) (x y : L)
    (hx : LieAlgebra.ad ℝ L (S x - x) = 0)
    (hy : LieAlgebra.ad ℝ L (S y - y) = 0) :
    semisimpleOneProjection S.toLinearMap hS ⁅x, y⁆ =
      ⁅semisimpleOneProjection S.toLinearMap hS x, semisimpleOneProjection S.toLinearMap hS y⁆ := by
  let P := semisimpleOneProjection S.toLinearMap hS
  have hpx : S (P x) = P x := sub_eq_zero.mp
    (semisimpleKernelProjection_mem _ (semisimple_sub_one S.toLinearMap hS) x)
  have hpy : S (P y) = P y := sub_eq_zero.mp
    (semisimpleKernelProjection_mem _ (semisimple_sub_one S.toLinearMap hS) y)
  have hx0 := semisimple_central_difference_of_ad_sub_zero S hS x hx
  have hy0 := semisimple_central_difference_of_ad_sub_zero S hS y hy
  have hbr : ⁅x, y⁆ = ⁅P x, P y⁆ := by
    have ha : ⁅x - P x, y⁆ = 0 := LinearMap.congr_fun hx0 y
    have hb : ⁅y - P y, P x⁆ = 0 := LinearMap.congr_fun hy0 (P x)
    have hb' : ⁅P x, y - P y⁆ = 0 := by rw [← lie_skew, hb, neg_zero]
    rw [sub_lie, sub_eq_zero] at ha
    rw [lie_sub, sub_eq_zero] at hb'
    exact ha.trans hb'
  have hfix : S ⁅P x, P y⁆ = ⁅P x, P y⁆ := by rw [S.map_lie, hpx, hpy]
  have hp : P ⁅P x, P y⁆ = ⁅P x, P y⁆ :=
    Submodule.projection_apply_of_mem_left _ (sub_eq_zero.mpr hfix)
  change P ⁅x, y⁆ = ⁅P x, P y⁆
  rw [hbr, hp]

def innerCentralizerFixedProjection (S : L ≃ₗ⁅ℝ⁆ L)
    (hS : Module.End.IsSemisimple S.toLinearMap) : innerCentralizerLieSubalgebra S →ₗ⁅ℝ⁆ L where
  toFun x := semisimpleOneProjection S.toLinearMap hS x
  map_add' x y := (semisimpleOneProjection S.toLinearMap hS).map_add x y
  map_smul' r x := (semisimpleOneProjection S.toLinearMap hS).map_smul r x
  map_lie' {x y} := fixed_projection_bracket S hS x y x.property y.property

def innerCentralizerCentralProjection (S : L ≃ₗ⁅ℝ⁆ L)
    (hS : Module.End.IsSemisimple S.toLinearMap) : innerCentralizerLieSubalgebra S →ₗ⁅ℝ⁆ L where
  toLinearMap := (innerCentralizerLieSubalgebra S).subtype -
    (innerCentralizerFixedProjection S hS).toLinearMap
  map_lie' := by
    intro x y
    let P := semisimpleOneProjection S.toLinearMap hS
    have hfix : S ⁅(x : L), (y : L)⁆ = ⁅(x : L), (y : L)⁆ :=
      bracket_fixed_of_central_differences S x y x.property y.property
    have hp : P ⁅(x : L), (y : L)⁆ = ⁅(x : L), (y : L)⁆ :=
      Submodule.projection_apply_of_mem_left _ (sub_eq_zero.mpr hfix)
    have hz : LieAlgebra.ad ℝ L ((x : L) - P x) = 0 :=
      semisimple_central_difference_of_ad_sub_zero S hS x x.property
    have hbr : ⁅(x : L) - P x, (y : L) - P y⁆ = 0 :=
      LinearMap.congr_fun hz ((y : L) - P y)
    change ⁅(x : L), (y : L)⁆ - P ⁅(x : L), (y : L)⁆ =
      ⁅(x : L) - P x, (y : L) - P y⁆
    rw [hp, sub_self, hbr]

theorem innerCentralizerCentralProjection_central (S : L ≃ₗ⁅ℝ⁆ L)
    (hS : Module.End.IsSemisimple S.toLinearMap) (x : innerCentralizerLieSubalgebra S) :
    LieAlgebra.ad ℝ L (innerCentralizerCentralProjection S hS x) = 0 :=
  semisimple_central_difference_of_ad_sub_zero S hS x x.property

theorem innerCentralizer_projection_decomposition (S : L ≃ₗ⁅ℝ⁆ L)
    (hS : Module.End.IsSemisimple S.toLinearMap) (x : innerCentralizerLieSubalgebra S) :
    innerCentralizerFixedProjection S hS x + innerCentralizerCentralProjection S hS x = (x : L) := by
  change semisimpleOneProjection S.toLinearMap hS x +
    ((x : L) - semisimpleOneProjection S.toLinearMap hS x) = (x : L)
  abel

end PolycyclicRecognition

end

end OAI
