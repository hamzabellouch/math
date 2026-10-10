import OAI.Geometry.RCD.Sobolev.PositiveCompactTestMeasure

namespace OAI

/-! # Positive test measures with the interior ratio needed for Poisson data -/

open Set Metric MeasureTheory
open scoped NNReal BoundedContinuousFunction CompactlySupported

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem positive_test_measure_of_majorant {S T : Set X} (hST : S ⊆ T)
    (F : compactLipschitzTests T →ₗ[ℝ] ℝ)
    (hF : ∀ f : compactLipschitzTests T, 0 ≤ (f : X →ᵇ ℝ) → 0 ≤ F f)
    (χ : compactLipschitzTests T) (hχ0 : 0 ≤ (χ : X →ᵇ ℝ))
    (hχ1 : ∀ x ∈ S, 1 ≤ (χ : X →ᵇ ℝ) x) :
    ∃ σ : Measure X, IsFiniteMeasure σ ∧
      ∀ f : compactLipschitzTests S,
        (∫ x, (f : X →ᵇ ℝ) x ∂σ) = F
          ⟨f, f.property.choose, f.property.choose_spec.1, f.property.choose_spec.2.1,
            f.property.choose_spec.2.2.trans hST⟩ := by
  have hinc : compactLipschitzTests S ≤ compactLipschitzTests T := by
    rintro f ⟨L, hL, hc, hs⟩
    exact ⟨L, hL, hc, hs.trans hST⟩
  let ι := Submodule.inclusion hinc
  have hM : 0 ≤ F χ := hF χ hχ0
  have hbound (f : compactLipschitzTests S) :
      (F.comp ι) f ≤ F χ * ‖(f : X →ᵇ ℝ) ⊔ 0‖ := by
    let C := ‖(f : X →ᵇ ℝ) ⊔ 0‖
    have hC : 0 ≤ C := norm_nonneg _
    have hn : 0 ≤ ((C • χ - ι f : compactLipschitzTests T) : X →ᵇ ℝ) := by
      intro x
      change 0 ≤ C * (χ : X →ᵇ ℝ) x - (f : X →ᵇ ℝ) x
      by_cases hx : (f : X →ᵇ ℝ) x = 0
      · rw [hx, sub_zero]
        exact mul_nonneg hC (hχ0 x)
      · have hxs := f.property.choose_spec.2.2 (subset_tsupport _ hx)
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
    (compactLipschitzTests S) (F.comp ι) hM hbound
  exact ⟨σ, hσ, fun f => hrep f f.property.choose_spec.2.1⟩

private def nestedCutoff (p : X) (R : ℝ) (x : X) : ℝ :=
  2 * radialCutoff p (2 * R / 3) x

omit [MeasurableSpace X] [BorelSpace X] [ProperSpace X] in
private theorem nestedCutoff_lipschitz (p : X) {R : ℝ} (hR : 0 < R) :
    ∃ L : ℝ≥0, LipschitzWith L (nestedCutoff p R) := by
  have hs : 0 < 2 * R / 3 := by positivity
  exact ⟨_, (lipschitzWith_smul (2 : ℝ)).comp (radialCutoff_lipschitz p hs)⟩

omit [MeasurableSpace X] [BorelSpace X] in
private theorem nestedCutoff_compact (p : X) {R : ℝ} (hR : 0 < R) :
    HasCompactSupport (nestedCutoff p R) :=
  (radialCutoff_hasCompactSupport p (show 0 < 2 * R / 3 by positivity)).mul_left

omit [MeasurableSpace X] [BorelSpace X] [ProperSpace X] in
private theorem nestedCutoff_support (p : X) {R : ℝ} (hR : 0 < R) :
    tsupport (nestedCutoff p R) ⊆ ball p (3 * R / 2) := by
  have hs : 0 < 2 * R / 3 := by positivity
  have hc : tsupport (radialCutoff p (2 * R / 3)) ⊆ closedBall p (2 * (2 * R / 3)) := by
    apply closure_minimal _ isClosed_closedBall
    intro x hx
    by_contra hnot
    exact hx (radialCutoff_eq_zero p hs (le_of_lt (by
      simpa only [mem_closedBall, not_le, dist_comm] using hnot)))
  exact (tsupport_smul_subset_right (fun _ => (2 : ℝ)) (radialCutoff p (2 * R / 3))).trans
    (hc.trans (closedBall_subset_ball (by linarith)))

omit [MeasurableSpace X] [BorelSpace X] [ProperSpace X] in
private theorem nestedCutoff_nonneg (p : X) (R : ℝ) (x : X) : 0 ≤ nestedCutoff p R x :=
  mul_nonneg (by norm_num) (radialCutoff_bounds p (2 * R / 3) x).1

omit [MeasurableSpace X] [BorelSpace X] [ProperSpace X] in
private theorem nestedCutoff_lower (p : X) {R : ℝ} (hR : 0 < R) (x : X)
    (hx : x ∈ ball p R) : 1 ≤ nestedCutoff p R x := by
  have hd : dist p x < R := by simpa only [mem_ball, dist_comm] using hx
  have hs : 0 < 2 * R / 3 := by positivity
  have hdiv : dist p x / (2 * R / 3) ≤ (3 / 2 : ℝ) := by
    apply (div_le_iff₀ hs).mpr
    linarith
  change 1 ≤ 2 * radialCutoff p (2 * R / 3) x
  unfold radialCutoff clipUnit
  have ha : (1 / 2 : ℝ) ≤ 2 - dist p x / (2 * R / 3) := by linarith
  have hm : (1 / 2 : ℝ) ≤ min (max (2 - dist p x / (2 * R / 3)) 0) 1 :=
    le_min (ha.trans (le_max_left _ _)) (by norm_num)
  linarith

omit [MeasurableSpace X] [BorelSpace X] in
theorem exists_nested_lipschitz_majorant (p : X) {R : ℝ} (hR : 0 < R) :
    ∃ χ : compactLipschitzTests (ball p (3 * R / 2)),
      (0 ≤ (χ : X →ᵇ ℝ)) ∧ ∀ x ∈ ball p R, 1 ≤ (χ : X →ᵇ ℝ) x := by
  obtain ⟨L, hL⟩ := nestedCutoff_lipschitz p hR
  let cv : C_c(X, ℝ) := ⟨⟨nestedCutoff p R, hL.continuous⟩, nestedCutoff_compact p hR⟩
  let χ : compactLipschitzTests (ball p (3 * R / 2)) :=
    ⟨cv.toBoundedContinuousFunction, L, hL, nestedCutoff_compact p hR, nestedCutoff_support p hR⟩
  refine ⟨χ, fun x => nestedCutoff_nonneg p R x, fun x hx => nestedCutoff_lower p hR x hx⟩

theorem exists_nested_positive_test_measure (p : X) {R : ℝ} (hR : 0 < R)
    (F : compactLipschitzTests (ball p (3 * R / 2)) →ₗ[ℝ] ℝ)
    (hF : ∀ f : compactLipschitzTests (ball p (3 * R / 2)), 0 ≤ (f : X →ᵇ ℝ) → 0 ≤ F f) :
    ∃ σ : Measure X, IsFiniteMeasure σ ∧
      ∀ f : compactLipschitzTests (ball p R),
        (∫ x, (f : X →ᵇ ℝ) x ∂σ) = F
          ⟨f, f.property.choose, f.property.choose_spec.1, f.property.choose_spec.2.1,
            f.property.choose_spec.2.2.trans (ball_subset_ball (by linarith))⟩ := by
  obtain ⟨χ, hχ0, hχ1⟩ := exists_nested_lipschitz_majorant p hR
  exact positive_test_measure_of_majorant (ball_subset_ball (by linarith)) F hF χ hχ0 hχ1

end RegularPointCoordinates

end

end OAI
