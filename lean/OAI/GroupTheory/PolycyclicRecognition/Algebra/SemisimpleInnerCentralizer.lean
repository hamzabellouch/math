import OAI.GroupTheory.PolycyclicRecognition.Algebra.SemisimpleInnerFixedRepresentative
import Mathlib.GroupTheory.Subgroup.Center

namespace OAI

/-! # The kernel of a semisimple action centralizer

An inner automorphism centralizes a semisimple S exactly when its defining
element is a product of a central element and an S-fixed element.
-/

noncomputable section
namespace PolycyclicRecognition
variable {L : Type} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [C : PolynomialExponentialCoordinates L] [LieRing.IsNilpotent L]

omit [LieRing.IsNilpotent L] in
private theorem central_quotient_of_inner_eq (x y : L)
    (h : (polynomialInnerLieEquiv x).toLinearMap = (polynomialInnerLieEquiv y).toLinearMap) :
    x * y⁻¹ ∈ Subgroup.center L := by
  have hh : MulAut.conj x = MulAut.conj y := by
    apply DFunLike.ext
    intro z
    have hz : polynomialInnerLieEquiv x z = polynomialInnerLieEquiv y z :=
      LinearMap.congr_fun h z
    change x * z * x⁻¹ = y * z * y⁻¹
    simpa only [polynomialInnerLieEquiv_apply] using hz
  have hq : MulAut.conj (x * y⁻¹) = 1 := by
    rw [map_mul, map_inv, hh, mul_inv_cancel]
  apply Subgroup.mem_center_iff.mpr
  intro z
  have hz := congrArg (fun f : MulAut L => f z) hq
  change (x * y⁻¹) * z * (x * y⁻¹)⁻¹ = z at hz
  exact (mul_inv_eq_iff_eq_mul.mp hz).symm

theorem semisimple_inner_centralizer_decomposition (S : L ≃ₗ⁅ℝ⁆ L)
    (hS : Module.End.IsSemisimple S.toLinearMap) (x : L)
    (hcomm : Commute S.toLinearMap (polynomialInnerLieEquiv x).toLinearMap) :
    ∃ z y : L, z ∈ Subgroup.center L ∧ S y = y ∧ x = z * y := by
  obtain ⟨y, hy, hi⟩ := semisimple_inner_fixed_representative S hS x hcomm
  exact ⟨x * y⁻¹, y, central_quotient_of_inner_eq x y hi.symm, hy, by group⟩

theorem semisimple_inner_centralizer_iff (S : L ≃ₗ⁅ℝ⁆ L)
    (hS : Module.End.IsSemisimple S.toLinearMap) (x : L) :
    Commute S.toLinearMap (polynomialInnerLieEquiv x).toLinearMap ↔
      ∃ z y : L, z ∈ Subgroup.center L ∧ S y = y ∧ x = z * y := by
  refine ⟨semisimple_inner_centralizer_decomposition S hS x, ?_⟩
  rintro ⟨z, y, hz, hy, rfl⟩
  have hzconj : MulAut.conj z = 1 := by
    apply DFunLike.ext
    intro w
    change z * w * z⁻¹ = w
    rw [← Subgroup.mem_center_iff.mp hz w]
    group
  have hxy : (polynomialInnerLieEquiv (z * y)).toLinearMap =
      (polynomialInnerLieEquiv y).toLinearMap := by
    apply LinearMap.ext
    intro w
    change polynomialInnerLieEquiv (z * y) w = polynomialInnerLieEquiv y w
    rw [polynomialInnerLieEquiv_apply, polynomialInnerLieEquiv_apply]
    change (MulAut.conj (z * y)) w = (MulAut.conj y) w
    rw [map_mul, hzconj, one_mul]
  rw [hxy]
  apply LinearMap.ext
  intro w
  let s := PolynomialExponentialCoordinates.groupAutomorphism (P := C) S
  change S (polynomialInnerLieEquiv y w) = polynomialInnerLieEquiv y (S w)
  rw [polynomialInnerLieEquiv_apply, polynomialInnerLieEquiv_apply]
  change s (y * w * y⁻¹) = y * s w * y⁻¹
  rw [map_mul, map_mul, map_inv]
  change S y * s w * (S y)⁻¹ = y * s w * y⁻¹
  rw [hy]

end PolycyclicRecognition

end

end OAI
