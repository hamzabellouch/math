import Mathlib

namespace OAI

noncomputable section

open scoped InnerProduct

namespace Problem367.OrthogonalBlocks

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

theorem pow_mem_of_mem
    (A : E →L[𝕜] E) (K : Submodule 𝕜 E)
    (hAK : ∀ x ∈ K, A x ∈ K) {x : E} (hx : x ∈ K) (n : ℕ) :
    (A ^ n) x ∈ K := by
  induction n with
  | zero => simpa using hx
  | succ n ih =>
      rw [pow_succ', mul_apply_eq_comp]
      exact hAK _ ih

theorem opNorm_le_of_orthogonal_blocks
    (A : E →L[𝕜] E) (K : Submodule 𝕜 E) [K.HasOrthogonalProjection]
    (hAK : ∀ x ∈ K, A x ∈ K) (hAKo : ∀ x ∈ Kᗮ, A x ∈ Kᗮ)
    {c d : ℝ} (hc : 0 ≤ c) (_hd : 0 ≤ d)
    (hK : ∀ x ∈ K, ‖A x‖ ≤ c * ‖x‖)
    (hKo : ∀ x ∈ Kᗮ, ‖A x‖ ≤ d * ‖x‖) :
    ‖A‖ ≤ max c d := by
  have hM : 0 ≤ max c d := hc.trans (le_max_left _ _)
  apply A.opNorm_le_bound hM
  intro x
  obtain ⟨y, hy, z, hz, rfl⟩ := K.exists_add_mem_mem_orthogonal x
  have hyz : inner 𝕜 y z = 0 := Submodule.inner_right_of_mem_orthogonal hy hz
  have hAyz : inner 𝕜 (A y) (A z) = 0 :=
    Submodule.inner_right_of_mem_orthogonal (hAK y hy) (hAKo z hz)
  have hAy : ‖A y‖ ≤ max c d * ‖y‖ :=
    (hK y hy).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  have hAz : ‖A z‖ ≤ max c d * ‖z‖ :=
    (hKo z hz).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hM (norm_nonneg _))).mp
  calc
    ‖A (y + z)‖ ^ 2 = ‖A y‖ ^ 2 + ‖A z‖ ^ 2 := by
      rw [map_add]
      simpa only [pow_two] using
        norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (A y) (A z) hAyz
    _ ≤ (max c d * ‖y‖) ^ 2 + (max c d * ‖z‖) ^ 2 :=
      add_le_add
        ((sq_le_sq₀ (norm_nonneg _) (mul_nonneg hM (norm_nonneg _))).mpr hAy)
        ((sq_le_sq₀ (norm_nonneg _) (mul_nonneg hM (norm_nonneg _))).mpr hAz)
    _ = (max c d * ‖y + z‖) ^ 2 := by
      have hnorm : ‖y + z‖ ^ 2 = ‖y‖ ^ 2 + ‖z‖ ^ 2 := by
        simpa only [pow_two] using
          norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero y z hyz
      rw [mul_pow, mul_pow, mul_pow, hnorm]
      ring

theorem norm_pow_le_of_orthogonal_blocks
    (A : E →L[𝕜] E) (K : Submodule 𝕜 E) [K.HasOrthogonalProjection]
    (hAK : ∀ x ∈ K, A x ∈ K) (hAKo : ∀ x ∈ Kᗮ, A x ∈ Kᗮ)
    (n : ℕ) {c d : ℝ} (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hK : ∀ x ∈ K, ‖(A ^ n) x‖ ≤ c * ‖x‖)
    (hKo : ∀ x ∈ Kᗮ, ‖(A ^ n) x‖ ≤ d * ‖x‖) :
    ‖A ^ n‖ ≤ max c d := by
  apply opNorm_le_of_orthogonal_blocks (A ^ n) K
    (fun x hx => pow_mem_of_mem A K hAK hx n)
    (fun x hx => pow_mem_of_mem A Kᗮ hAKo hx n) hc hd hK hKo

end Problem367.OrthogonalBlocks

end

end OAI
