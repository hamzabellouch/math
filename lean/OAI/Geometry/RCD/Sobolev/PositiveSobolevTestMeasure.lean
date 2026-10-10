import OAI.Geometry.RCD.Sobolev.CompactSobolevTests
import OAI.Geometry.RCD.Sobolev.NestedPositiveTestMeasure

namespace OAI

/-! # Positive measures representing every continuous compact Sobolev test -/

open Set Filter Metric MeasureTheory
open scoped NNReal BoundedContinuousFunction

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) [IsFiniteMeasureOnCompacts μ] (hQ : QuadraticCheegerEnergy μ)

theorem exists_positive_sobolev_test_measure (p : X) {R : ℝ} (hR : 0 < R)
    (F : compactSobolevTests μ hQ (ball p (3 * R / 2)) →ₗ[ℝ] ℝ)
    (hF : ∀ f : compactSobolevTests μ hQ (ball p (3 * R / 2)), 0 ≤ (f : X →ᵇ ℝ) → 0 ≤ F f) :
    ∃ σ : Measure X, IsFiniteMeasure σ ∧
      ∀ f : compactSobolevTests μ hQ (ball p R),
        (∫ x, (f : X →ᵇ ℝ) x ∂σ) = F
          ⟨f, f.property.1, f.property.2.1.trans (ball_subset_ball (by linarith)), f.property.2.2⟩ := by
  have hinc : compactSobolevTests μ hQ (ball p R) ≤ compactSobolevTests μ hQ (ball p (3 * R / 2)) := by
    rintro f ⟨hc, hs, hu⟩
    exact ⟨hc, hs.trans (ball_subset_ball (by linarith)), hu⟩
  let ι := Submodule.inclusion hinc
  obtain ⟨b, hb0, hb1⟩ := exists_nested_lipschitz_majorant p hR
  let χ : compactSobolevTests μ hQ (ball p (3 * R / 2)) :=
    ⟨b, b.property.choose_spec.2.1, b.property.choose_spec.2.2,
      compactTestSobolev μ hQ (ball p (3 * R / 2)) b,
      compactTestSobolev_coe μ hQ (ball p (3 * R / 2)) b⟩
  have hχ0 : 0 ≤ (χ : X →ᵇ ℝ) := hb0
  have hχ1 : ∀ x ∈ ball p R, 1 ≤ (χ : X →ᵇ ℝ) x := hb1
  have hM : 0 ≤ F χ := hF χ hχ0
  have hbound (f : compactSobolevTests μ hQ (ball p R)) :
      (F.comp ι) f ≤ F χ * ‖(f : X →ᵇ ℝ) ⊔ 0‖ := by
    let C := ‖(f : X →ᵇ ℝ) ⊔ 0‖
    have hC : 0 ≤ C := norm_nonneg _
    have hn : 0 ≤ ((C • χ - ι f : compactSobolevTests μ hQ (ball p (3 * R / 2))) : X →ᵇ ℝ) := by
      intro x
      change 0 ≤ C * (χ : X →ᵇ ℝ) x - (f : X →ᵇ ℝ) x
      by_cases hx : (f : X →ᵇ ℝ) x = 0
      · rw [hx, sub_zero]
        exact mul_nonneg hC (hχ0 x)
      · have hxs := f.property.2.1 (subset_tsupport _ hx)
        have hfC : (f : X →ᵇ ℝ) x ≤ C := (le_max_left _ _).trans
          (((f : X →ᵇ ℝ) ⊔ 0).apply_le_norm x)
        have hmajor := mul_le_mul_of_nonneg_left (hχ1 x hxs) hC
        linarith
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
    (compactSobolevTests μ hQ (ball p R)) (F.comp ι) hM hbound
  exact ⟨σ, hσ, fun f => hrep f f.property.1⟩

end RegularPointCoordinates

end

end OAI
