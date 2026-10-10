import Mathlib

namespace OAI

noncomputable section
namespace Problem340.Prediction

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

theorem norm_fderiv_iterate_le {G : E → E} {B : ℝ}
    (hG : Differentiable 𝕜 G) (hB : 0 ≤ B)
    (hbound : ∀ x, ‖fderiv 𝕜 G x‖ ≤ B) (m : ℕ) (x : E) :
    ‖fderiv 𝕜 (G^[m]) x‖ ≤ B ^ m := by
  induction m generalizing x with
  | zero =>
      simpa using ContinuousLinearMap.norm_id_le (𝕜 := 𝕜) (E := E)
  | succ m hm =>
      rw [Function.iterate_succ, fderiv_comp x (hG.iterate m (G x)) (hG x)]
      calc
        ‖(fderiv 𝕜 (G^[m]) (G x)).comp (fderiv 𝕜 G x)‖
            ≤ ‖fderiv 𝕜 (G^[m]) (G x)‖ * ‖fderiv 𝕜 G x‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ B ^ m * B := mul_le_mul (hm (G x)) (hbound x)
          (norm_nonneg _) (pow_nonneg hB _)
        _ = B ^ (m + 1) := (pow_succ B m).symm

theorem differentiableAt_iterate_and_norm_le_on {G : E → E} {B : ℝ} {s : Set E}
    (hG : ∀ x ∈ s, DifferentiableAt 𝕜 G x) (hmap : Set.MapsTo G s s)
    (hB : 0 ≤ B) (hbound : ∀ x ∈ s, ‖fderiv 𝕜 G x‖ ≤ B)
    (m : ℕ) (x : E) (hx : x ∈ s) :
    DifferentiableAt 𝕜 (G^[m]) x ∧ ‖fderiv 𝕜 (G^[m]) x‖ ≤ B ^ m := by
  induction m generalizing x with
  | zero =>
      constructor
      · exact differentiableAt_id
      · simpa using ContinuousLinearMap.norm_id_le (𝕜 := 𝕜) (E := E)
  | succ m hm =>
      obtain ⟨hd, hn⟩ := hm (G x) (hmap hx)
      rw [Function.iterate_succ]
      refine ⟨hd.comp x (hG x hx), ?_⟩
      rw [fderiv_comp x hd (hG x hx)]
      calc
        ‖(fderiv 𝕜 (G^[m]) (G x)).comp (fderiv 𝕜 G x)‖
            ≤ ‖fderiv 𝕜 (G^[m]) (G x)‖ * ‖fderiv 𝕜 G x‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ B ^ m * B := mul_le_mul hn (hbound x hx)
          (norm_nonneg _) (pow_nonneg hB _)
        _ = B ^ (m + 1) := (pow_succ B m).symm

theorem norm_fderiv_projection_iterate_le {G : E → E} {B : ℝ}
    (hG : Differentiable 𝕜 G) (hB : 0 ≤ B)
    (hbound : ∀ x, ‖fderiv 𝕜 G x‖ ≤ B) (p : E →L[𝕜] F) (hp : ‖p‖ ≤ 1)
    (m : ℕ) (x : E) :
    ‖fderiv 𝕜 (p ∘ G^[m]) x‖ ≤ B ^ m := by
  rw [fderiv_comp x p.differentiableAt (hG.iterate m x), p.fderiv]
  calc
    ‖p.comp (fderiv 𝕜 (G^[m]) x)‖ ≤ ‖p‖ * ‖fderiv 𝕜 (G^[m]) x‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * B ^ m := mul_le_mul hp (norm_fderiv_iterate_le hG hB hbound m x)
      (norm_nonneg _) (by norm_num)
    _ = B ^ m := one_mul _

theorem exists_iterate_fderiv_bound_of_compact {G : E → E} {s : Set E}
    (hG : ContDiff 𝕜 1 G) (hs : IsCompact s) (hmap : Set.MapsTo G s s) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ m : ℕ, ∀ x ∈ s, ‖fderiv 𝕜 (G^[m]) x‖ ≤ B ^ m := by
  obtain ⟨C, hC⟩ := hs.exists_bound_of_continuousOn
    (hG.continuous_fderiv (by norm_num)).continuousOn
  refine ⟨max 1 C, le_max_left _ _, ?_⟩
  intro m x hx
  exact (differentiableAt_iterate_and_norm_le_on
    (fun y _ => hG.differentiable (by norm_num) y) hmap
    (le_trans (by norm_num) (le_max_left _ _))
    (fun y hy => (hC y hy).trans (le_max_right _ _)) m x hx).2

theorem norm_fderiv_projection_iterate_le_on {G : E → E} {B : ℝ} {s : Set E}
    (hG : ∀ x ∈ s, DifferentiableAt 𝕜 G x) (hmap : Set.MapsTo G s s)
    (hB : 0 ≤ B) (hbound : ∀ x ∈ s, ‖fderiv 𝕜 G x‖ ≤ B)
    (p : E →L[𝕜] F) (hp : ‖p‖ ≤ 1) (m : ℕ) (x : E) (hx : x ∈ s) :
    ‖fderiv 𝕜 (p ∘ G^[m]) x‖ ≤ B ^ m := by
  obtain ⟨hd, hn⟩ := differentiableAt_iterate_and_norm_le_on hG hmap hB hbound m x hx
  rw [fderiv_comp x p.differentiableAt hd, p.fderiv]
  calc
    ‖p.comp (fderiv 𝕜 (G^[m]) x)‖ ≤ ‖p‖ * ‖fderiv 𝕜 (G^[m]) x‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * B ^ m := mul_le_mul hp hn (norm_nonneg _) (by norm_num)
    _ = B ^ m := one_mul _

end Problem340.Prediction

end

end OAI
