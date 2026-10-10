import OAI.GroupTheory.PolycyclicRecognition.Analysis.RescaledProfiles

namespace OAI

/-! # Anchor bounds and compact containment for sampled map profiles -/

noncomputable section

namespace PolycyclicRecognition

open Set
open scoped NNReal

variable {G W Z : Type*} [Group G] [PseudoMetricSpace G] [IsIsometricSMul G G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [Zero Z]

/-- A bound at the identity extends to a pointwise bound by the actual
scaled chart distance. -/
theorem rescaledMapProfile_norm_le
    {K : ℝ≥0} {J : G → W} (hJ : LipschitzWith K J)
    (x k : G) (r : ℝ) (φ : Z → G) (hφ : φ 0 = 1) (z : Z) :
    ‖rescaledMapProfile J x k r φ z‖ ≤
      (K : ℝ) * (dist 1 (φ z) / Real.exp r) + ‖rescaledMapProfile J x k r φ 0‖ := by
  calc
    _ = ‖(rescaledMapProfile J x k r φ z - rescaledMapProfile J x k r φ 0) +
        rescaledMapProfile J x k r φ 0‖ := by rw [sub_add_cancel]
    _ ≤ ‖rescaledMapProfile J x k r φ z - rescaledMapProfile J x k r φ 0‖ +
        ‖rescaledMapProfile J x k r φ 0‖ := norm_add_le _ _
    _ ≤ _ := by
      rw [← dist_eq_norm]
      apply add_le_add _ (le_refl _)
      simpa only [hφ, dist_comm] using rescaledMapProfile_dist_le hJ x k r φ z 0

/-- The profile value at the identity is controlled by the suffix length. -/
theorem rescaledMapProfile_zero_norm_le
    {K : ℝ≥0} {J : G → W} (hJ : LipschitzWith K J)
    (x k : G) (r : ℝ) (φ : Z → G) (hφ : φ 0 = 1) :
    ‖rescaledMapProfile J x k r φ 0‖ ≤ (K : ℝ) * (dist 1 k / Real.exp r) := by
  have hh := hJ.dist_le_mul (x * k) x
  have he : dist (x * k) x = dist 1 k := by
    simpa only [mul_one, dist_comm] using dist_mul_left x k 1
  rw [he] at hh
  simp only [rescaledMapProfile, hφ, mul_one, norm_smul, Real.norm_eq_abs,
    abs_inv, abs_of_pos (Real.exp_pos r), ← dist_eq_norm]
  calc
    _ ≤ (Real.exp r)⁻¹ * ((K : ℝ) * dist 1 k) :=
      mul_le_mul_of_nonneg_left hh (inv_nonneg.mpr (Real.exp_pos r).le)
    _ = _ := by ring

variable [TopologicalSpace Z] [IsTopologicalGroup G] [ProperSpace W]

/-- Once equicontinuity is proved, only the anchor and pointwise chart
radius bounds are needed to contain all sampled profiles in one compact
set for locally uniform convergence. -/
theorem exists_compact_containing_rescaled_profiles
    {A : Type*} {K : ℝ≥0} (J : ℕ → A → G → W)
    (hJ : ∀ i u, LipschitzWith K (J i u)) (x k : ℕ → A → G)
    (scale : ℕ → ℝ) (φ : ℕ → Z → G) (hφ : ∀ i, Continuous (φ i))
    (hzero : ∀ i, φ i 0 = 1)
    (hequi : Equicontinuous (fun p : ℕ × A =>
      rescaledMapProfile (J p.1 p.2) (x p.1 p.2) (k p.1 p.2) (scale p.1) (φ p.1)))
    (B : ℝ) (hanchor : ∀ i u,
      ‖rescaledMapProfile (J i u) (x i u) (k i u) (scale i) (φ i) 0‖ ≤ B)
    (hradius : ∀ z, ∃ D : ℝ, ∀ i, dist 1 (φ i z) / Real.exp (scale i) ≤ D) :
    ∃ S : Set C(Z, W), IsCompact S ∧ ∀ i u,
      (⟨rescaledMapProfile (J i u) (x i u) (k i u) (scale i) (φ i),
        continuous_rescaledMapProfile (hJ i u).continuous _ _ _ (hφ i)⟩ : C(Z, W)) ∈ S := by
  let F : (ℕ × A) → C(Z, W) := fun p =>
    ⟨rescaledMapProfile (J p.1 p.2) (x p.1 p.2) (k p.1 p.2) (scale p.1) (φ p.1),
      continuous_rescaledMapProfile (hJ p.1 p.2).continuous _ _ _ (hφ p.1)⟩
  obtain ⟨S, hS, hmem⟩ := exists_compact_containing_profiles F hequi (0 : W) (by
    intro z
    obtain ⟨D, hD⟩ := hradius z
    refine ⟨(K : ℝ) * D + B, ?_⟩
    intro p
    simp only [dist_zero_right]
    exact (rescaledMapProfile_norm_le (hJ p.1 p.2) (x p.1 p.2) (k p.1 p.2)
      (scale p.1) (φ p.1) (hzero p.1) z).trans
      (add_le_add (mul_le_mul_of_nonneg_left (hD p.1) K.coe_nonneg) (hanchor p.1 p.2)))
  exact ⟨S, hS, fun i u => hmem (i, u)⟩

end PolycyclicRecognition

end

end OAI
