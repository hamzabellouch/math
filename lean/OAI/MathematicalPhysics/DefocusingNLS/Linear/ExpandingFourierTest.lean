import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingMultiplication
import OAI.MathematicalPhysics.DefocusingNLS.Linear.PeriodicSchwartzPairing

namespace OAI

/-! # Bounded Schwartz frequency tests on the expanding Fourier space -/

open scoped SchwartzMap

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

theorem summable_expandingFourierTest (a k L : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L)
    (φ : 𝓢(E, ℂ)) (f : FourierL2) :
    Summable (fun n => expandingFourierCoefficient a k L f n * φ (L⁻¹ • (n : E))) := by
  apply ((summable_norm_expandingFourierCoefficient a k L ha ha1 hk hL f).mul_right
    (SchwartzMap.seminorm ℂ 0 0 φ)).of_norm_bounded
  intro n
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (φ.norm_le_seminorm ℂ _) (norm_nonneg _)

noncomputable def expandingFourierTest (a k L : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L)
    (φ : 𝓢(E, ℂ)) : FourierL2 →L[ℂ] ℂ := by
  let F : FourierL2 →ₗ[ℂ] ℂ :=
    { toFun := fun f => ∑' n, expandingFourierCoefficient a k L f n * φ (L⁻¹ • (n : E))
      map_add' := by
        intro f g
        simp only [expandingFourierCoefficient_add, add_mul]
        exact (summable_expandingFourierTest a k L ha ha1 hk hL φ f).tsum_add
          (summable_expandingFourierTest a k L ha ha1 hk hL φ g)
      map_smul' := by
        intro c f
        simp only [expandingFourierCoefficient_smul, mul_assoc, tsum_mul_left,
          smul_eq_mul, RingHom.id_apply] }
  refine F.mkContinuous (expandingEmbeddingBound a k * SchwartzMap.seminorm ℂ 0 0 φ) ?_
  intro f
  change ‖∑' n, expandingFourierCoefficient a k L f n * φ (L⁻¹ • (n : E))‖ ≤ _
  apply (norm_tsum_le_tsum_norm
    (summable_expandingFourierTest a k L ha ha1 hk hL φ f).norm).trans
  calc
    _ ≤ ∑' n, ‖expandingFourierCoefficient a k L f n‖ * SchwartzMap.seminorm ℂ 0 0 φ := by
      apply Summable.tsum_le_tsum
        (fun n => by
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left (φ.norm_le_seminorm ℂ _) (norm_nonneg _))
        (summable_expandingFourierTest a k L ha ha1 hk hL φ f).norm
        ((summable_norm_expandingFourierCoefficient a k L ha ha1 hk hL f).mul_right _)
    _ = (∑' n, ‖expandingFourierCoefficient a k L f n‖) * SchwartzMap.seminorm ℂ 0 0 φ :=
      tsum_mul_right
    _ ≤ _ := by
      simpa only [mul_assoc, mul_left_comm, mul_comm] using
        mul_le_mul_of_nonneg_right
          (tsum_norm_expandingFourierCoefficient_le a k L ha ha1 hk hL f)
          (apply_nonneg (SchwartzMap.seminorm ℂ 0 0) φ)

@[simp] theorem expandingFourierTest_apply (a k L : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L)
    (φ : 𝓢(E, ℂ)) (f : FourierL2) :
    expandingFourierTest a k L ha ha1 hk hL φ f =
      ∑' n, expandingFourierCoefficient a k L f n * φ (L⁻¹ • (n : E)) := rfl

theorem expandingFourierTest_norm_le (a k L : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L) (φ : 𝓢(E, ℂ)) :
    ‖expandingFourierTest a k L ha ha1 hk hL φ‖ ≤
      expandingEmbeddingBound a k * SchwartzMap.seminorm ℂ 0 0 φ := by
  unfold expandingFourierTest
  apply LinearMap.mkContinuous_norm_le
  unfold expandingEmbeddingBound
  positivity

end DefocusingNLS

end OAI
