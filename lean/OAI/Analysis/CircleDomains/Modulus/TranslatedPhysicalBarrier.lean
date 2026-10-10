import OAI.Analysis.CircleDomains.Modulus.PhysicalSmallBarrier

namespace OAI

/-! Translating a physical barrier preserves its energy and derivative
bounds; the plateau and support move to the selected trace center. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ContDiff ENNReal
noncomputable section
namespace CircleDomainRigidity

 def translatedPhysicalBarrier (Φ : EuclideanPlane → ℝ) (c : EuclideanPlane) : EuclideanPlane → ℝ :=
    fun x => Φ (x-c)

 theorem translatedPhysicalBarrier_fderiv {Φ : EuclideanPlane → ℝ}
    (hΦ : Differentiable ℝ Φ) (c x : EuclideanPlane) :
    fderiv ℝ (translatedPhysicalBarrier Φ c) x = fderiv ℝ Φ (x-c) := by
  have h := (hΦ (x-c)).hasFDerivAt.comp x ((hasFDerivAt_id x).sub_const c)
  change fderiv ℝ (fun y => Φ (y-c)) x = _
  simpa only [id_eq, Function.comp_def, ContinuousLinearMap.comp_id] using h.fderiv

 theorem translatedPhysicalBarrier_energy {Φ : EuclideanPlane → ℝ}
    (hΦ : Differentiable ℝ Φ) (c : EuclideanPlane) :
    (∫ x, ‖planeCovectorGradient (fderiv ℝ (translatedPhysicalBarrier Φ c) x)‖^2) =
      ∫ x, ‖planeCovectorGradient (fderiv ℝ Φ x)‖^2 := by
  simp_rw [translatedPhysicalBarrier_fderiv hΦ]
  exact integral_sub_right_eq_self (fun x => ‖planeCovectorGradient (fderiv ℝ Φ x)‖^2) c

 theorem translatedPhysicalBarrier_data {Φ : EuclideanPlane → ℝ}
    (hΦ : ContDiff ℝ ∞ Φ) (hs : HasCompactSupport Φ)
    {r R M₁ M₂ : ℝ} (hsR : tsupport Φ ⊆ ball 0 R)
    (hunit : ∀ x, Φ x ∈ Icc (0 : ℝ) 1) (hone : ∀ x ∈ ball 0 r, Φ x = 1)
    (hD : ∀ x, ‖fderiv ℝ Φ x‖ ≤ M₁)
    (hDD : ∀ x y, ‖fderiv ℝ Φ x-fderiv ℝ Φ y‖ ≤ M₂*‖x-y‖)
    (c : EuclideanPlane) :
    ContDiff ℝ ∞ (translatedPhysicalBarrier Φ c) ∧
      HasCompactSupport (translatedPhysicalBarrier Φ c) ∧
      tsupport (translatedPhysicalBarrier Φ c) ⊆ ball c R ∧
      (∀ x, translatedPhysicalBarrier Φ c x ∈ Icc (0 : ℝ) 1) ∧
      (∀ x ∈ ball c r, translatedPhysicalBarrier Φ c x = 1) ∧
      (∀ x, ‖fderiv ℝ (translatedPhysicalBarrier Φ c) x‖ ≤ M₁) ∧
      (∀ x y, ‖fderiv ℝ (translatedPhysicalBarrier Φ c) x-
        fderiv ℝ (translatedPhysicalBarrier Φ c) y‖ ≤ M₂*‖x-y‖) := by
  have he : translatedPhysicalBarrier Φ c = Φ ∘ Homeomorph.addRight (-c) := by
    funext x
    change Φ (x-c) = Φ (x + -c)
    rw [sub_eq_add_neg]
  refine ⟨hΦ.comp (contDiff_id.sub contDiff_const), ?_, ?_, fun x => hunit _, ?_, ?_, ?_⟩
  · rw [he]
    exact hs.comp_homeomorph _
  · rw [he, tsupport_comp_eq_preimage]
    intro x hx
    have h := hsR hx
    change x + -c ∈ ball (0 : EuclideanPlane) R at h
    simpa only [mem_ball, dist_zero_right, dist_eq_norm, sub_eq_add_neg, neg_zero, add_zero] using h
  · intro x hx
    exact hone _ (by simpa only [mem_ball, dist_eq_norm, sub_zero] using hx)
  · intro x
    rw [translatedPhysicalBarrier_fderiv (hΦ.differentiable (by simp))]
    exact hD _
  · intro x y
    rw [translatedPhysicalBarrier_fderiv (hΦ.differentiable (by simp)),
      translatedPhysicalBarrier_fderiv (hΦ.differentiable (by simp))]
    simpa only [sub_sub_sub_cancel_right] using hDD (x-c) (y-c)

end CircleDomainRigidity

end

end OAI
