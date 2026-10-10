import OAI.Geometry.RCD.Sobolev.SubsolutionLevelDecay

namespace OAI

/-! # Small normalized L² mass bounds a weak subsolution on the half ball -/

open Set Metric Filter MeasureTheory
open scoped NNReal ENNReal Topology

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

/-- Vanishing level energies imply the upper bound on the fixed half ball. -/
theorem NoncollapsedRCD.subsolution_small_l2_upper_bound {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2 ≤ n) (Λ : ℝ) (hΛ : 0 ≤ Λ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (x : X) (R : ℝ), 0 < R → -1 ≤ K*R^2 →
      ∀ (u : SobolevSpace (hausdorff n X) hX.quadratic) (a : ℝ), 0 ≤ a → a*R^2 ≤ Λ →
      IsWeakSubsolutionOn (hausdorff n X) hX.quadratic (ball x R) u a →
      (∫ y in ball x R, (SobolevSpace.toLp (hausdorff n X) hX.quadratic u y)^2
        ∂hausdorff n X) ≤ δ*(hausdorff n X).real (ball x R) →
      ∀ᵐ y ∂(hausdorff n X).restrict (ball x (R/2)),
        SobolevSpace.toLp (hausdorff n X) hX.quadratic u y ≤ 1 := by
  obtain ⟨δ,hδ,hdecay⟩ := hX.subsolution_level_energies_tendsto_zero hn Λ hΛ
  refine ⟨δ,hδ,?_⟩
  intro x R hR hcurv u a ha haR hu hsmall
  let μ := hausdorff n X
  let U := SobolevSpace.toLp μ hX.quadratic u
  have hlim := hdecay x R hR hcurv u a ha haR hu hsmall
  have hI : Integrable (fun y => (max (U y-1) 0)^2) μ :=
    ((upperLevelPart_lipschitz 1).comp_memLp (upperLevelPart_zero zero_le_one)
      (Lp.memLp U)).integrable_sq
  have hbound (i : ℕ) : (∫ y in ball x (R/2), (max (U y-1) 0)^2 ∂μ) ≤
      ∫ y in closedBall x (R/2+R/(4*2^i)),
        (max (U y-(1-(2^i:ℝ)⁻¹)) 0)^2 ∂μ := by
    have hk : 0 ≤ 1-(2^i:ℝ)⁻¹ := (dyadic_level_gap_bounds hR i).1
    have hk1 : 1-(2^i:ℝ)⁻¹ ≤ 1 := by
      have hh : 0 ≤ (2^i:ℝ)⁻¹ := by positivity
      linarith
    have hki : Integrable (fun y => (max (U y-(1-(2^i:ℝ)⁻¹)) 0)^2) μ :=
      ((upperLevelPart_lipschitz _).comp_memLp (upperLevelPart_zero hk)
        (Lp.memLp U)).integrable_sq
    calc
      _ ≤ ∫ y in ball x (R/2), (max (U y-(1-(2^i:ℝ)⁻¹)) 0)^2 ∂μ := by
        apply integral_mono_ae hI.integrableOn hki.integrableOn
        exact Eventually.of_forall fun y => (sq_le_sq₀ (le_max_right _ _) (le_max_right _ _)).mpr
          (max_le_max (by linarith) le_rfl)
      _ ≤ _ := setIntegral_mono_set hki.integrableOn
        (Eventually.of_forall fun y => sq_nonneg _)
        (Eventually.of_forall ((ball_subset_closedBall).trans
          (closedBall_subset_closedBall (le_add_of_nonneg_right (by positivity)))))
  have hz : (∫ y in ball x (R/2), (max (U y-1) 0)^2 ∂μ) = 0 :=
    le_antisymm (ge_of_tendsto hlim (Eventually.of_forall hbound))
      (integral_nonneg fun y => sq_nonneg _)
  filter_upwards [(integral_eq_zero_iff_of_nonneg (fun y => sq_nonneg _) hI.integrableOn).mp hz]
    with y hy
  have hh : max (U y-1) 0 = 0 := sq_eq_zero_iff.mp hy
  have hle := le_max_left (U y-1) 0
  rw [hh] at hle
  linarith

end RegularPointCoordinates

end

end OAI
