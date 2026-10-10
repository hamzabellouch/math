import OAI.GroupTheory.PolycyclicRecognition.Algebra.PolynomialInnerLogarithm
import OAI.GroupTheory.PolycyclicRecognition.Algebra.SemisimpleKernelProjection
import OAI.GroupTheory.PolycyclicRecognition.Algebra.PolynomialDerivationAction

namespace OAI

/-! # Fixed representatives of inner automorphisms centralizing a semisimple map

An element whose inner action centralizes S differs, by a central element,
from an S-fixed element. The representative is the canonical linear fixed
projection, so it preserves all invariant subspaces as well.
-/

noncomputable section
namespace PolycyclicRecognition
attribute [local instance] LieRing.ofAssociativeRing
variable {L : Type} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [C : PolynomialExponentialCoordinates L] [LieRing.IsNilpotent L]

theorem semisimple_inner_fixed_representative_preserves (S : L ≃ₗ⁅ℝ⁆ L)
    (hS : Module.End.IsSemisimple S.toLinearMap) (x : L)
    (hcomm : Commute S.toLinearMap (polynomialInnerLieEquiv x).toLinearMap) :
    ∃ y : L, S y = y ∧
      (polynomialInnerLieEquiv y).toLinearMap = (polynomialInnerLieEquiv x).toLinearMap ∧
      ∀ T : L ≃ₗ⁅ℝ⁆ L, Commute T.toLinearMap S.toLinearMap → T x = x → T y = y := by
  let s := PolynomialExponentialCoordinates.groupAutomorphism (P := C) S
  have hi : (polynomialInnerLieEquiv (S x)).toLinearMap =
      (polynomialInnerLieEquiv x).toLinearMap := by
    apply LinearMap.ext
    intro z
    have hh : S (polynomialInnerLieEquiv x (S.symm z)) =
        polynomialInnerLieEquiv x (S (S.symm z)) :=
      LinearMap.congr_fun hcomm.eq (S.symm z)
    rw [S.apply_symm_apply, polynomialInnerLieEquiv_apply,
      polynomialInnerLieEquiv_apply] at hh
    have hs : s (x * S.symm z * x⁻¹) = S x * z * (S x)⁻¹ := by
      rw [map_mul, map_mul, map_inv]
      change S x * S (S.symm z) * (S x)⁻¹ = S x * z * (S x)⁻¹
      rw [S.apply_symm_apply]
    change S (x * S.symm z * x⁻¹) = x * z * x⁻¹ at hh
    change s (x * S.symm z * x⁻¹) = x * z * x⁻¹ at hh
    rw [hs] at hh
    change polynomialInnerLieEquiv (S x) z = polynomialInnerLieEquiv x z
    simpa only [polynomialInnerLieEquiv_apply] using hh
  have had := polynomial_inner_eq_implies_ad_eq (S x) x hi
  let Z : Submodule ℝ L := (LieAlgebra.ad ℝ L).ker.toSubmodule
  have hZ (z : L) (hz : z ∈ Z) : S z ∈ Z := by
    change LieAlgebra.ad ℝ L z = 0 at hz
    change LieAlgebra.ad ℝ L (S z) = 0
    apply LinearMap.ext
    intro w
    have hzw : ⁅z, S.symm w⁆ = 0 := LinearMap.congr_fun hz (S.symm w)
    change ⁅S z, w⁆ = 0
    calc
      _ = S ⁅z, S.symm w⁆ := by rw [S.map_lie, S.apply_symm_apply]
      _ = 0 := by rw [hzw, map_zero]
  let B : Module.End ℝ L := S.toLinearMap - 1
  have hB : B.IsSemisimple := semisimple_sub_one S.toLinearMap hS
  let P := semisimpleKernelProjection B hB
  have hx : B x ∈ Z := by
    change LieAlgebra.ad ℝ L (S x - x) = 0
    rw [map_sub, had, sub_self]
  have hd : x - P x ∈ Z := semisimple_sub_projection_mem_of_apply_mem B hB Z
    (fun z hz => Z.sub_mem (hZ z hz) hz) hx
  refine ⟨P x, sub_eq_zero.mp (semisimpleKernelProjection_mem B hB x), ?_, ?_⟩
  · apply polynomial_inner_eq_of_ad_eq
    change LieAlgebra.ad ℝ L (x - P x) = 0 at hd
    rw [map_sub, sub_eq_zero] at hd
    exact hd.symm
  · intro T hTS hTx
    have hPT : Commute P T.toLinearMap := semisimpleKernelProjection_commute B T.toLinearMap hB
      (hTS.symm.sub_left (Commute.one_left _))
    have hh : P (T x) = T (P x) := LinearMap.congr_fun hPT.eq x
    rw [hTx] at hh
    exact hh.symm

theorem semisimple_inner_fixed_representative (S : L ≃ₗ⁅ℝ⁆ L)
    (hS : Module.End.IsSemisimple S.toLinearMap) (x : L)
    (hcomm : Commute S.toLinearMap (polynomialInnerLieEquiv x).toLinearMap) :
    ∃ y : L, S y = y ∧
      (polynomialInnerLieEquiv y).toLinearMap = (polynomialInnerLieEquiv x).toLinearMap := by
  obtain ⟨y, hy, hi, _⟩ := semisimple_inner_fixed_representative_preserves S hS x hcomm
  exact ⟨y, hy, hi⟩

end PolycyclicRecognition

end

end OAI
