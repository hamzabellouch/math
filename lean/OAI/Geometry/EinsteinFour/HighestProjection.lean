import OAI.Geometry.EinsteinFour.HighestSquare
import OAI.Geometry.EinsteinFour.HighestCondition
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension

namespace OAI

/-! The orthogonal projection is constructed from the actual tensor subspace. -/

namespace PositiveEinsteinFour.HighestHessian

noncomputable section

open scoped BigOperators
open Bianchi TraceHessian

abbrev HessianSpace := EuclideanSpace ℝ TensorIndex

def hessianVector (X : Hessian) : HessianSpace := WithLp.toLp 2 (tensorCoordinates X)

def vectorHessian (v : HessianSpace) : Hessian := fun i j a b => v (i, j, a, b)

@[simp] theorem vectorHessian_hessianVector (X : Hessian) :
    vectorHessian (hessianVector X) = X := rfl

@[simp] theorem hessianVector_vectorHessian (v : HessianSpace) :
    hessianVector (vectorHessian v) = v := by
  ext p
  rcases p with ⟨i, j, a, b⟩
  rfl

theorem hessianVector_injective : Function.Injective hessianVector := by
  intro X Y h
  simpa only [vectorHessian_hessianVector] using congrArg vectorHessian h

theorem hessianVector_inner (X Y : Hessian) :
    inner ℝ (hessianVector X) (hessianVector Y) = hessianPairing X Y := by
  simpa [hessianVector, PiLp.inner_apply, RCLike.inner_apply, mul_comm] using
    tensorCoordinates_pairing X Y

/-- The explicit twenty-one-coordinate map, regarded as a linear map into
the Euclidean space of all four-slot tensors. -/
def highestLinearMap : (Fin 21 → ℝ) →ₗ[ℝ] HessianSpace where
  toFun c := hessianVector (highest c)
  map_add' c d := by
    ext p
    rcases p with ⟨i, j, a, b⟩
    change highest (c + d) i j a b = highest c i j a b + highest d i j a b
    rw [highest_add]
    rfl
  map_smul' r c := by
    ext p
    rcases p with ⟨i, j, a, b⟩
    change highest (r • c) i j a b = r * highest c i j a b
    rw [highest_smul]
    rfl

def highestSubspace : Submodule ℝ HessianSpace := highestLinearMap.range

/-- The actual orthogonal projection onto the symmetry/trace/Bianchi subspace. -/
def highestProjection (X : Hessian) : Hessian :=
  vectorHessian (highestSubspace.starProjection (hessianVector X))

theorem highestProjection_has_coordinates (X : Hessian) :
    ∃ c : Fin 21 → ℝ, highest c = highestProjection X := by
  have h := highestSubspace.starProjection_apply_mem (hessianVector X)
  obtain ⟨c, hc⟩ := h
  refine ⟨c, hessianVector_injective ?_⟩
  change hessianVector (highest c) =
    highestSubspace.starProjection (hessianVector X) at hc
  simpa only [highestProjection, hessianVector_vectorHessian] using hc

theorem highestProjection_condition (X : Hessian) : condition (highestProjection X) := by
  obtain ⟨c, hc⟩ := highestProjection_has_coordinates X
  rw [← hc]
  exact highest_condition c

theorem highestSubspace_mem (X : Hessian) (hX : condition X) :
    hessianVector X ∈ highestSubspace := by
  obtain ⟨c, rfl⟩ := exists_highest X hX
  exact ⟨c, rfl⟩

/-- Orthogonality is with respect to the original tensor Frobenius pairing. -/
theorem highestProjection_pairing_right (X Y : Hessian) (hY : condition Y) :
    hessianPairing (highestProjection X) Y = hessianPairing X Y := by
  have h := highestSubspace.starProjection_inner_eq_zero
    (hessianVector X) (hessianVector Y) (highestSubspace_mem Y hY)
  have hp : highestSubspace.starProjection (hessianVector X) =
      hessianVector (highestProjection X) := by
    simp only [highestProjection, hessianVector_vectorHessian]
  rw [hp, inner_sub_left, hessianVector_inner, hessianVector_inner] at h
  linarith

theorem highestProjection_pairing_left (X Y : Hessian) (hX : condition X) :
    hessianPairing X (highestProjection Y) = hessianPairing X Y := by
  rw [hessianPairing_comm X, highestProjection_pairing_right Y X hX,
    hessianPairing_comm Y]

theorem highestProjection_norm_split (X : Hessian) :
    hessianNormSq X = hessianNormSq (highestProjection X) +
      hessianNormSq (X - highestProjection X) := by
  have h := highestProjection_pairing_right X (highestProjection X)
    (highestProjection_condition X)
  rw [hessianPairing_self] at h
  rw [hessianNormSq_sub]
  linarith

theorem highestProjection_norm_le (X : Hessian) :
    hessianNormSq (highestProjection X) ≤ hessianNormSq X := by
  have h := highestProjection_norm_split X
  have hn : 0 ≤ hessianNormSq (X - highestProjection X) := by
    unfold hessianNormSq
    exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  linarith

theorem totalPlus_condition (s : Fin 3) (X : Hessian) (hX : condition X) :
    condition (totalPlus s X) := by
  obtain ⟨c, rfl⟩ := exists_highest X hX
  rw [totalPlus_highest]
  exact highest_condition _

theorem totalMinus_condition (s : Fin 3) (X : Hessian) (hX : condition X) :
    condition (totalMinus s X) := by
  obtain ⟨c, rfl⟩ := exists_highest X hX
  rw [totalMinus_highest]
  exact highest_condition _

private theorem plusProjection_pairing (s : Fin 3) (X L : Hessian) (hX : condition X) :
    hessianPairing (totalPlus s X) (totalPlus s (highestProjection L)) =
      hessianPairing (totalPlus s X) (totalPlus s L) := by
  have hXX := totalPlus_condition s (totalPlus s X) (totalPlus_condition s X hX)
  have hp := highestProjection_pairing_left (totalPlus s (totalPlus s X)) L hXX
  have h₁ := totalPlus_skew s (totalPlus s X) (highestProjection L)
  have h₂ := totalPlus_skew s (totalPlus s X) L
  linarith

private theorem minusProjection_pairing (s : Fin 3) (X L : Hessian) (hX : condition X) :
    hessianPairing (totalMinus s X) (totalMinus s (highestProjection L)) =
      hessianPairing (totalMinus s X) (totalMinus s L) := by
  have hXX := totalMinus_condition s (totalMinus s X) (totalMinus_condition s X hX)
  have hp := highestProjection_pairing_left (totalMinus s (totalMinus s X)) L hXX
  have h₁ := totalMinus_skew s (totalMinus s X) (highestProjection L)
  have h₂ := totalMinus_skew s (totalMinus s X) L
  linarith

/-- The mixed curvature term retains the whole unsymmetrized weight tensor. -/
theorem curvaturePairing_highestProjection (t u : Fin 3 → ℝ)
    (X L : Hessian) (hX : condition X) :
    curvaturePairing t u X (highestProjection L) = curvaturePairing t u X L := by
  simp only [curvaturePairing, highestProjection_pairing_left X L hX,
    plusProjection_pairing _ X L hX, minusProjection_pairing _ X L hX]

/-- The weighted square with a constructed projection, without a projected
tensor or a projection identity among its hypotheses. -/
theorem weighted_highestProjection_square (X L : Hessian) (hX : condition X)
    (t u : Fin 3 → ℝ) (x y m : ℝ) (hm : 0 < m)
    (ht : ∀ s, -x ≤ t s) (hu : ∀ s, -y ≤ u s) (hxy : x + y ≤ 2) :
    0 ≤ (m / 6) * curvaturePairing t u X X + curvaturePairing t u X L / 6 +
      curvaturePairing t u (highestProjection L) (highestProjection L) / (24 * m) := by
  have h := weighted_curvature_square_nonneg_of_condition X (highestProjection L)
    hX (highestProjection_condition L) t u x y m hm ht hu hxy
  rwa [curvaturePairing_highestProjection t u X L hX] at h

/-- The unsymmetrized weight derivative tensor `dm ⊗ ∇T`. -/
def weightTensor (a : Vec) (Z : Tensor) : Hessian :=
  fun i j b c => a i * Z.matrix b c j

theorem weightTensor_norm (a : Vec) (Z : Tensor) :
    hessianNormSq (weightTensor a Z) = ‖a‖ ^ 2 * Z.squaredNorm := by
  have h (b c : Fin 3) :
      (∑ i : Fin 4, ∑ j : Fin 4, (a i * Z.matrix b c j) ^ 2) =
        ‖a‖ ^ 2 * ‖Z.matrix b c‖ ^ 2 := by
    simp only [mul_pow, ← Finset.mul_sum, ← Finset.sum_mul,
      EuclideanSpace.real_norm_sq_eq]
  unfold hessianNormSq weightTensor
  simp_rw [h]
  simp only [← Finset.mul_sum, Tensor.squaredNorm]

end
end PositiveEinsteinFour.HighestHessian

end OAI
