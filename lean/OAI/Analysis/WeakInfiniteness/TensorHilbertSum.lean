import Mathlib
import OAI.Analysis.WeakInfiniteness.FreeTwistedNorm

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace

namespace WeakPureInfiniteness

section TensorHilbertSum

variable {H G : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def tensorSequence (ξ : H) : GroupHilbert G →L[ℂ] HilbertValued.HilbertSum G H :=
  lp.mapCLM 2 (fun _ => (ContinuousLinearMap.id ℂ ℂ).smulRight ξ) (norm_nonneg ξ)
    (fun _ => by simp [ContinuousLinearMap.norm_smulRight_apply])

@[simp]
lemma tensorSequence_apply (ξ : H) (η : GroupHilbert G) (g : G) :
    tensorSequence ξ η g = η g • ξ := rfl

def tensorSequenceBilinear : H →ₗ[ℂ] GroupHilbert G →ₗ[ℂ] HilbertValued.HilbertSum G H where
  toFun ξ := (tensorSequence ξ).toLinearMap
  map_add' ξ ζ := by ext η g; simp [smul_add]
  map_smul' c ξ := by ext η g; simp [smul_smul, mul_comm]

def tensorToHilbertSumMap : (H ⊗[ℂ] GroupHilbert G) →ₗ[ℂ] HilbertValued.HilbertSum G H :=
  TensorProduct.lift tensorSequenceBilinear

@[simp]
lemma tensorToHilbertSumMap_tmul (ξ : H) (η : GroupHilbert G) :
    tensorToHilbertSumMap (ξ ⊗ₜ[ℂ] η) = tensorSequence ξ η := rfl

lemma tensorToHilbertSumMap_inner (x y : H ⊗[ℂ] GroupHilbert G) :
    inner ℂ (tensorToHilbertSumMap x) (tensorToHilbertSumMap y) = inner ℂ x y := by
  induction x using TensorProduct.inductionOn with
  | tmul ξ η =>
    induction y using TensorProduct.inductionOn with
    | tmul ζ θ =>
      simp only [tensorToHilbertSumMap_tmul, lp.inner_eq_tsum, tensorSequence_apply,
        inner_smul_left, inner_smul_right, TensorProduct.inner_tmul, RCLike.inner_apply]
      rw [← tsum_mul_left]
      apply tsum_congr
      intro g
      ring
    | add y z hy hz => simp only [map_add, inner_add_right, hy, hz]
  | add x z hx hz => simp only [map_add, inner_add_left, hx, hz]

def tensorToHilbertSum : (H ⊗[ℂ] GroupHilbert G) →ₗᵢ[ℂ] HilbertValued.HilbertSum G H :=
  LinearMap.isometryOfInner (E := H ⊗[ℂ] GroupHilbert G)
    (E' := HilbertValued.HilbertSum G H) (𝕜 := ℂ) tensorToHilbertSumMap
    (fun x y => tensorToHilbertSumMap_inner x y)

variable [Group G]

lemma tensorToHilbertSum_intertwining (π : G →* H ≃ₗᵢ[ℂ] H) (s : G)
    (z : H ⊗[ℂ] GroupHilbert G) :
    tensorToHilbertSum (TensorProduct.mapL
      (π s).toContinuousLinearEquiv.toContinuousLinearMap (leftRegular s) z) =
      HilbertValued.twistedRegular π s (tensorToHilbertSum z) := by
  induction z using TensorProduct.inductionOn with
  | tmul ξ η =>
    ext g
    change (((leftRegular s : GroupHilbert G →L[ℂ] GroupHilbert G) η) g) • π s ξ =
      π s (η (s⁻¹ * g) • ξ)
    simp
  | add z w hz hw => simp only [map_add, hz, hw]

end TensorHilbertSum

theorem norm_freeTensor_sum_le {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (π : FreeTwo →* H ≃ₗᵢ[ℂ] H) :
    ‖∑ s : FreeLetter, TensorProduct.mapL
      (π (freeLetter s)).toContinuousLinearEquiv.toContinuousLinearMap
      (leftRegular (freeLetter s) : GroupHilbert FreeTwo →L[ℂ] GroupHilbert FreeTwo)‖ ≤ 2 * Real.sqrt 3 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro z
  have he : tensorToHilbertSum ((∑ s : FreeLetter, TensorProduct.mapL
      (π (freeLetter s)).toContinuousLinearEquiv.toContinuousLinearMap
      (leftRegular (freeLetter s) : GroupHilbert FreeTwo →L[ℂ] GroupHilbert FreeTwo)) z) =
      (∑ s : FreeLetter, HilbertValued.twistedRegular π (freeLetter s))
        (tensorToHilbertSum z) := by
    simp only [sum_apply, map_sum, tensorToHilbertSum_intertwining]
  rw [← (tensorToHilbertSum (H := H) (G := FreeTwo)).norm_map, he]
  exact (ContinuousLinearMap.le_opNorm _ _).trans
    (by
      simpa using mul_le_mul_of_nonneg_right (norm_freeTwisted_sum_le π)
        (norm_nonneg (tensorToHilbertSum z)))

end WeakPureInfiniteness
end

end OAI
