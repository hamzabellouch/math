import OAI.Geometry.RCD.Metric.BoundedPositiveMeasure
import OAI.Geometry.RCD.Sobolev.CompactLipschitzTests

namespace OAI

/-! # Finite local representation of positive compact Lipschitz functionals -/

open Set Metric MeasureTheory
open scoped NNReal BoundedContinuousFunction CompactlySupported

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem exists_local_positive_test_measure (p : X) {R : ℝ} (hR : 0 < R)
    (F : compactLipschitzTests (ball p (3 * R)) →ₗ[ℝ] ℝ)
    (hF : ∀ f : compactLipschitzTests (ball p (3 * R)), 0 ≤ (f : X →ᵇ ℝ) → 0 ≤ F f) :
    ∃ σ : Measure X, IsFiniteMeasure σ ∧
      ∀ f : compactLipschitzTests (ball p R),
        (∫ x, (f : X →ᵇ ℝ) x ∂σ) = F
          ⟨f, f.property.choose, f.property.choose_spec.1, f.property.choose_spec.2.1,
            f.property.choose_spec.2.2.trans (ball_subset_ball (by linarith))⟩ := by
  have hinc : compactLipschitzTests (ball p R) ≤ compactLipschitzTests (ball p (3 * R)) := by
    rintro f ⟨L, hL, hc, hs⟩
    exact ⟨L, hL, hc, hs.trans (ball_subset_ball (by linarith))⟩
  let ι := Submodule.inclusion hinc
  have hχs : tsupport (radialCutoff p R) ⊆ ball p (3 * R) := by
    have hs : tsupport (radialCutoff p R) ⊆ closedBall p (2 * R) := by
      apply closure_minimal _ isClosed_closedBall
      intro x hx
      by_contra hn
      exact hx (radialCutoff_eq_zero p hR
        (not_le.mp (by simpa only [mem_closedBall, dist_comm] using hn)).le)
    exact hs.trans (closedBall_subset_ball (by linarith))
  let cχ : C_c(X, ℝ) := ⟨⟨radialCutoff p R, (radialCutoff_lipschitz p hR).continuous⟩,
    radialCutoff_hasCompactSupport p hR⟩
  let χ : compactLipschitzTests (ball p (3 * R)) :=
    ⟨cχ.toBoundedContinuousFunction, _, radialCutoff_lipschitz p hR,
      radialCutoff_hasCompactSupport p hR, hχs⟩
  have hχ0 : 0 ≤ (χ : X →ᵇ ℝ) := fun x => (radialCutoff_bounds p R x).1
  have hM : 0 ≤ F χ := hF χ hχ0
  have hbound (f : compactLipschitzTests (ball p R)) :
      (F.comp ι) f ≤ F χ * ‖(f : X →ᵇ ℝ) ⊔ 0‖ := by
    let C := ‖(f : X →ᵇ ℝ) ⊔ 0‖
    have hC : 0 ≤ C := norm_nonneg _
    have hn : 0 ≤ ((C • χ - ι f : compactLipschitzTests (ball p (3 * R))) : X →ᵇ ℝ) := by
      intro x
      change 0 ≤ C * radialCutoff p R x - (f : X →ᵇ ℝ) x
      by_cases hx : (f : X →ᵇ ℝ) x = 0
      · rw [hx, sub_zero]
        exact mul_nonneg hC (radialCutoff_bounds p R x).1
      · have hxb := f.property.choose_spec.2.2 (subset_tsupport _ hx)
        rw [radialCutoff_eq_one p hR (by simpa only [dist_comm] using (mem_ball.mp hxb).le), mul_one]
        exact sub_nonneg.mpr ((le_max_left ((f : X →ᵇ ℝ) x) 0).trans
          (((f : X →ᵇ ℝ) ⊔ 0).apply_le_norm x))
    have hp := hF (C • χ - ι f) hn
    have hadd := F.map_add (C • χ - ι f) (ι f)
    have heq : C • χ - ι f + ι f = C • χ := by
      apply Subtype.ext
      ext x
      change C * (χ : X →ᵇ ℝ) x - (f : X →ᵇ ℝ) x + (f : X →ᵇ ℝ) x = C * (χ : X →ᵇ ℝ) x
      ring
    rw [heq, F.map_smul] at hadd
    change C * F χ = F (C • χ - ι f) + F (ι f) at hadd
    change F (ι f) ≤ F χ * C
    linarith
  obtain ⟨σ, hσ, hrep⟩ := exists_finite_measure_of_positive_bound
    (compactLipschitzTests (ball p R)) (F.comp ι) hM hbound
  exact ⟨σ, hσ, fun f => hrep f f.property.choose_spec.2.1⟩

end RegularPointCoordinates

end

end OAI
