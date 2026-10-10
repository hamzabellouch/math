import OAI.Geometry.RCD.Sobolev.PoissonCaccioppoli

namespace OAI

/-! # Caccioppoli control of Poisson energy on an interior ball -/

open Set Metric Filter MeasureTheory
open scoped NNReal ENNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

/-- The actual square gradient has its expected amplitude/source bound. -/
theorem NoncollapsedRCD.poisson_ball_energy {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (p : X) (r : ℝ) (hr : 0 < r)
    (f : SobolevSpace (hausdorff n X) hX.quadratic) (c : ℝ) (A : ℝ≥0)
    (hf : IsConstantLaplacianOn (hausdorff n X) hX.quadratic (ball p (4*r)) f c)
    (hA : ∀ᵐ x ∂hausdorff n X, |SobolevSpace.toLp (hausdorff n X) hX.quadratic f x| ≤ A) :
    (∫ x in ball p r, localGamma (hausdorff n X) hX.quadratic f f x ∂hausdorff n X) ≤
      (2*|c| *A+4*(A:ℝ)^2*(r⁻¹)^2)*(hausdorff n X).real (ball p (4*r)) := by
  let μ := hausdorff n X
  let : IsLocallyFiniteMeasure μ := locallyFinite_of_finiteOnBounded μ hX.finiteOnBounded
  let χ := radialCutoff p r
  have hχ := radialCutoff_lipschitz p hr
  have hs := radialCutoff_hasCompactSupport p hr
  let η := SobolevSpace.ofLipschitzCompact μ hX.quadratic hχ hs
  have hη : SobolevSpace.toLp μ hX.quadratic η =ᵐ[μ] χ :=
    SobolevSpace.ofLipschitzCompact_coe μ hX.quadratic hχ hs
  have hb : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1 := radialCutoff_bounds p r
  have hsupport : tsupport χ ⊆ ball p (4*r) := by
    have hh : tsupport χ ⊆ closedBall p (2*r) := by
      apply closure_minimal _ isClosed_closedBall
      intro x hx
      by_contra hn
      apply hx
      apply radialCutoff_eq_zero p hr
      have hd : ¬ dist x p ≤ 2*r := hn
      rw [dist_comm]
      exact (lt_of_not_ge hd).le
    exact hh.trans (closedBall_subset_ball (by linarith))
  have he := hf.cutoff_energy_le μ hX.quadratic
    (hX.finiteOnBounded _ isBounded_ball).ne f η c hχ hs hb hsupport hη hA
  have hηb : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hX.quadratic η x| ≤ (1:ℝ≥0) := by
    filter_upwards [hη] with x hx
    rw [hx,abs_of_nonneg (hb x).1]
    exact (hb x).2
  have hi : Integrable (fun x => (χ x)^2*(SobolevSpace.minimalSlope μ hX.quadratic f x)^2) μ := by
    apply (bounded_square_weight_integrable μ (SobolevSpace.toLp μ hX.quadratic η)
      (SobolevSpace.minimalSlope μ hX.quadratic f) hηb).congr
    filter_upwards [hη] with x hx
    rw [hx]
  have hEq : (∫ x in ball p r, localGamma μ hX.quadratic f f x ∂μ) =
      ∫ x in ball p r, (χ x)^2*(SobolevSpace.minimalSlope μ hX.quadratic f x)^2 ∂μ := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae (localGamma_self μ hX.quadratic f),
      ae_restrict_mem measurableSet_ball] with x hx hm
    have hc : χ x = 1 := radialCutoff_eq_one p hr (by rw [dist_comm]; exact le_of_lt hm)
    simp only [hc,one_pow,one_mul,hx]
  rw [hEq]
  calc
    _ ≤ ∫ x, (χ x)^2*(SobolevSpace.minimalSlope μ hX.quadratic f x)^2 ∂μ :=
      setIntegral_le_integral hi (Eventually.of_forall fun x => by positivity)
    _ ≤ _ := by
      simpa only [NNReal.coe_mk] using! he

end RegularPointCoordinates

end

end OAI
