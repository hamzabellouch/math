import OAI.GroupTheory.PolycyclicRecognition.Algebra.SemisimpleInnerFixedRepresentative

namespace OAI

/-! # The fixed and central parts of a semisimple inner centralizer

The canonical fixed projection separates the center from the fixed subgroup.
The moving part of any inner-centralizing vector is genuinely central.
-/

noncomputable section
namespace PolycyclicRecognition
attribute [local instance] LieRing.ofAssociativeRing
variable {L : Type} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]

omit [FiniteDimensional ℝ L] in
private theorem ad_kernel_invariant (S : L ≃ₗ⁅ℝ⁆ L) (x : L)
    (hx : LieAlgebra.ad ℝ L x = 0) : LieAlgebra.ad ℝ L (S x) = 0 := by
  apply LinearMap.ext
  intro y
  have hxy : ⁅x, S.symm y⁆ = 0 := LinearMap.congr_fun hx (S.symm y)
  change ⁅S x, y⁆ = 0
  calc
    _ = S ⁅x, S.symm y⁆ := by rw [S.map_lie, S.apply_symm_apply]
    _ = 0 := by rw [hxy, map_zero]

def semisimpleOneProjection (S : Module.End ℝ L) (hS : S.IsSemisimple) : Module.End ℝ L :=
  semisimpleKernelProjection (S - 1) (semisimple_sub_one S hS)

theorem semisimple_central_difference_of_ad_sub_zero (S : L ≃ₗ⁅ℝ⁆ L)
    (hS : Module.End.IsSemisimple S.toLinearMap) (x : L)
    (hx : LieAlgebra.ad ℝ L (S x - x) = 0) :
    LieAlgebra.ad ℝ L (x - semisimpleOneProjection S.toLinearMap hS x) = 0 := by
  let Z : Submodule ℝ L := (LieAlgebra.ad ℝ L).ker.toSubmodule
  let B : Module.End ℝ L := S.toLinearMap - 1
  have hZ (z : L) (hz : z ∈ Z) : B z ∈ Z := by
    change LieAlgebra.ad ℝ L z = 0 at hz
    change LieAlgebra.ad ℝ L (S z - z) = 0
    rw [map_sub, ad_kernel_invariant S z hz, hz, sub_self]
  exact semisimple_sub_projection_mem_of_apply_mem B (semisimple_sub_one S.toLinearMap hS) Z hZ hx

variable [C : PolynomialExponentialCoordinates L] [LieRing.IsNilpotent L]

theorem semisimple_inner_centralizer_central_difference (S : L ≃ₗ⁅ℝ⁆ L)
    (hS : Module.End.IsSemisimple S.toLinearMap) (x : L)
    (hx : Commute S.toLinearMap (polynomialInnerLieEquiv x).toLinearMap) :
    LieAlgebra.ad ℝ L (x - semisimpleOneProjection S.toLinearMap hS x) = 0 := by
  obtain ⟨y, hy, hiy⟩ := semisimple_inner_fixed_representative S hS x hx
  have he : LieAlgebra.ad ℝ L y = LieAlgebra.ad ℝ L x :=
    polynomial_inner_eq_implies_ad_eq y x hiy
  let Z : Submodule ℝ L := (LieAlgebra.ad ℝ L).ker.toSubmodule
  let B : Module.End ℝ L := S.toLinearMap - 1
  have hz : x - y ∈ Z := by
    change LieAlgebra.ad ℝ L (x - y) = 0
    rw [map_sub, he, sub_self]
  have hZ (z : L) (hz : z ∈ Z) : B z ∈ Z := by
    change LieAlgebra.ad ℝ L z = 0 at hz
    change LieAlgebra.ad ℝ L (S z - z) = 0
    rw [map_sub, ad_kernel_invariant S z hz, hz, sub_self]
  have hBy : B y = 0 := sub_eq_zero.mpr hy
  have hBx : B x ∈ Z := by
    have hh := hZ (x - y) hz
    rw [map_sub, hBy, sub_zero] at hh
    exact hh
  exact semisimple_sub_projection_mem_of_apply_mem B (semisimple_sub_one S.toLinearMap hS) Z hZ hBx

end PolycyclicRecognition

end

end OAI
