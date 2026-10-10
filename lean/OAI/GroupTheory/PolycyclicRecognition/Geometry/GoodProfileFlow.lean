import OAI.GroupTheory.PolycyclicRecognition.Geometry.ProfileFlowConvergence
import OAI.GroupTheory.PolycyclicRecognition.Analysis.RescaledProfiles

namespace OAI

/-! # Good profile control along the actual converging horizontal flow -/

noncomputable section

namespace PolycyclicRecognition

open Set Filter
open scoped Topology

/-- Uniform approximation on the fixed profile compact extends to the
actual varying flow. The only additional error tends to zero with that flow. -/
theorem good_profile_along_flow
    {U V W A ι : Type*} {l : Filter ι} [TopologicalSpace U] [LocallyCompactSpace U]
    [TopologicalSpace V] [LocallyCompactSpace V] [NormedAddCommGroup W]
    (f : C(V, W)) (Ψ : ι → C(U, V)) (Ψ₀ : C(U, V))
    (hΨ : Tendsto Ψ l (𝓝 Ψ₀)) (K : Set U) (hK : IsCompact K)
    (Z : Set V) (hZ : ∀ᶠ r in l, ∀ u ∈ K, Ψ r u ∈ Z)
    (profile : ι → A → V → W) (good : ι → Set A) (ζ : ι → ℝ)
    (hgood : ∀ r a, a ∈ good r → ∀ z ∈ Z, ‖profile r a z - f z‖ ≤ ζ r)
    {η : ℝ} (hη : 0 < η) :
    ∀ᶠ r in l, ∀ a ∈ good r, ∀ u ∈ K,
      ‖profile r a (Ψ r u) - f (Ψ₀ u)‖ ≤ ζ r + η := by
  have hf : Tendsto (fun r => f.comp (Ψ r)) l (𝓝 (f.comp Ψ₀)) :=
    (ContinuousMap.continuous_postcomp f).continuousAt.tendsto.comp hΨ
  have hu := (ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn.mp hf) K hK
  have he := (Metric.tendstoUniformlyOn_iff.mp hu) η hη
  filter_upwards [hZ, he] with r hr hclose
  intro a ha u huK
  calc
    ‖profile r a (Ψ r u) - f (Ψ₀ u)‖ ≤
        ‖profile r a (Ψ r u) - f (Ψ r u)‖ + ‖f (Ψ r u) - f (Ψ₀ u)‖ :=
      (by simpa only [dist_eq_norm] using dist_triangle (profile r a (Ψ r u)) (f (Ψ r u)) (f (Ψ₀ u)))
    _ ≤ ζ r + η := add_le_add (hgood r a ha _ (hr u huK))
      (by simpa only [ContinuousMap.comp_apply, dist_eq_norm, norm_sub_rev] using (hclose u huK).le)

/-- Recover the physical-scale image height from the actual normalized
profile, with its prescribed common center. -/
theorem height_bound_of_rescaled_profile
    {G W Z : Type*} [Group G] [NormedAddCommGroup W] [NormedSpace ℝ W]
    (J : G → W) (x n : G) (s : ℝ) (φ : Z → G) (z : Z) (w : W) {ε : ℝ}
    (h : ‖rescaledMapProfile J x n s φ z - w‖ ≤ ε) :
    ‖J (x * n * φ z) - J x - Real.exp s • w‖ ≤ Real.exp s * ε := by
  have he : J (x * n * φ z) - J x - Real.exp s • w =
      Real.exp s • (rescaledMapProfile J x n s φ z - w) := by
    simp only [rescaledMapProfile, smul_sub, smul_smul,
      mul_inv_cancel₀ (Real.exp_ne_zero s), one_smul]
  rw [he, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos s)]
  exact mul_le_mul_of_nonneg_left h (Real.exp_pos s).le

end PolycyclicRecognition

end

end OAI
