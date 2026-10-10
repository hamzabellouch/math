import OAI.Geometry.RCD.Metric.RescaledBallVolume
import OAI.Geometry.RCD.Harmonic.HarmonicMeanValueInput
import OAI.Geometry.RCD.Sobolev.PoissonGradientInput
import Mathlib.Topology.Compactness.Lindelof

namespace OAI

/-! # The harmonic L² gradient input from the existing Poisson and mean inputs

A fixed small ball around each interior point has uniformly comparable
volume. The harmonic mean estimate bounds its values, and the constant-zero
case of the Poisson gradient estimate bounds its gradient. A countable open
subcover combines the local almost-everywhere estimates.
-/

open Set Metric MeasureTheory Filter
open scoped ENNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

private theorem curvature_mul_scale {K R a s : ℝ}
    (ha : 0 ≤ a) (hs : 0 ≤ s) (hs1 : s ≤ 1) (h : -a ≤ K * R ^ 2) :
    -a ≤ K * (s * R) ^ 2 := by
  have hs2 : s ^ 2 ≤ 1 := by nlinarith only [hs, hs1]
  calc
    -a ≤ -a * s ^ 2 := by nlinarith only [hs2, ha]
    _ ≤ (K * R ^ 2) * s ^ 2 := mul_le_mul_of_nonneg_right h (sq_nonneg s)
    _ = _ := by ring

private theorem curvature_unit_scale {K R a s : ℝ}
    (ha : 0 ≤ a) (hs : 0 ≤ s) (hsa : s ≤ 1 / (a + 1))
    (h : -a ≤ K * R ^ 2) : -1 ≤ K * (s * R) ^ 2 := by
  have hs1 : s ≤ 1 := hsa.trans ((div_le_one (by linarith)).mpr (by linarith))
  have hs2 : s ^ 2 ≤ s := by nlinarith only [hs, hs1]
  have hsa' : s * (a + 1) ≤ 1 := (le_div_iff₀ (by linarith)).mp hsa
  have has2 : a * s ^ 2 ≤ 1 := by nlinarith only [hsa', hs2, ha, hs]
  calc
    -1 ≤ -a * s ^ 2 := by linarith only [has2]
    _ ≤ (K * R ^ 2) * s ^ 2 := mul_le_mul_of_nonneg_right h (sq_nonneg s)
    _ = _ := by ring

private theorem harmonicTargetNorm_le_of_volume {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) {p q : X} {R r D : ℝ}
    (hR : 0 < R) (hr : 0 < r) (hD : 0 ≤ D)
    (hsub : ball q r ⊆ ball p R)
    (hvol : (hausdorff n X).real (ball p R) ≤ D * (hausdorff n X).real (ball q r))
    (w : SobolevSpace (hausdorff n X) hX.quadratic) :
    harmonicTargetNorm hX q r w ≤ Real.sqrt D * harmonicTargetNorm hX p R w := by
  have hfinR := (hX.finiteOnBounded (ball p R) isBounded_ball).ne
  have hfinr := (hX.finiteOnBounded (ball q r) isBounded_ball).ne
  have hposR := ENNReal.toReal_pos (hX.fullSupport p R hR).ne' hfinR
  have hposr := ENNReal.toReal_pos (hX.fullSupport q r hr).ne' hfinr
  have hnormR : (harmonicTargetNorm hX p R w) ^ 2 =
      ((hausdorff n X).real (ball p R))⁻¹ *
        ∫ x in ball p R, (SobolevSpace.toLp (hausdorff n X) hX.quadratic w x) ^ 2
          ∂hausdorff n X := normalized_sobolev_mean_sq _ _ _ hfinR w
  have hnormr : (harmonicTargetNorm hX q r w) ^ 2 =
      ((hausdorff n X).real (ball q r))⁻¹ *
        ∫ x in ball q r, (SobolevSpace.toLp (hausdorff n X) hX.quadratic w x) ^ 2
          ∂hausdorff n X := normalized_sobolev_mean_sq _ _ _ hfinr w
  have hb := average_nonneg_le_of_subset (hausdorff n X) hsub hposr hposR
    (Lp.memLp (SobolevSpace.toLp (hausdorff n X) hX.quadratic w)).integrable_sq.integrableOn
    (fun _ => sq_nonneg _) (sq_nonneg (harmonicTargetNorm hX p R w)) hvol hnormR.ge
  rw [← hnormr] at hb
  have hleft : 0 ≤ harmonicTargetNorm hX q r w := norm_nonneg _
  have hright : 0 ≤ Real.sqrt D * harmonicTargetNorm hX p R w :=
    mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  apply (sq_le_sq₀ hleft hright).mp
  rwa [mul_pow, Real.sq_sqrt hD]

/-- The harmonic L² gradient estimate is redundant once the Poisson gradient and harmonic mean-value estimates have been supplied. -/
theorem harmonicGradientInput_of_poisson_and_mean {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X)
    (hpoisson : LocalPoissonGradientInput hX) (hmean : LocalHarmonicL2MeanValueInput hX) :
    LocalHarmonicL2GradientInput hX := by
  classical
  let := hX.separable
  intro hn a τ ha hτ hτ1
  let δ := min ((1 - τ) / 2) (1 / (a + 1))
  have hδ : 0 < δ := lt_min (by linarith only [hτ1]) (by positivity)
  have hδa : δ ≤ 1 / (a + 1) := min_le_right _ _
  have hδ1 : δ ≤ 1 := hδa.trans ((div_le_one (by positivity)).mpr (by linarith only [ha]))
  have hδτ : δ + τ ≤ 1 := by
    have hh : δ ≤ (1 - τ) / 2 := min_le_left _ _
    linarith only [hh, hτ1]
  obtain ⟨D, hD, hvol⟩ := hX.rescaled_ball_volume_factor hn ha hδ hδ1
  obtain ⟨M, hM, hmean⟩ := hmean hn a ha
  obtain ⟨P, hP, hpoisson⟩ := hpoisson hn
  let F := 16 * P * M * Real.sqrt D / δ
  have hF : 0 ≤ F := by dsimp only [F]; positivity
  refine ⟨1 + F, by linarith only [hF], ?_⟩
  intro p R hR hcurv w hw
  let ρ := δ * R / 16
  have hρ : 0 < ρ := by dsimp only [ρ]; positivity
  have hscale : ρ = (δ / 16) * R := by dsimp only [ρ]; ring
  have hcurvρ : -1 ≤ K * ρ ^ 2 := by
    rw [hscale]
    apply curvature_unit_scale ha (by positivity) _ hcurv
    exact (show δ / 16 ≤ δ by linarith only [hδ]).trans hδa
  have hcurvδ : -a ≤ K * (δ * R) ^ 2 := curvature_mul_scale ha hδ.le hδ1 hcurv
  let A := M * Real.sqrt D * harmonicTargetNorm hX p R w
  have hA : 0 ≤ A := by
    dsimp only [A]
    exact mul_nonneg (mul_nonneg (zero_le_one.trans hM) (Real.sqrt_nonneg _)) (norm_nonneg _)
  have hlocal (q : ball p (τ * R)) :
      ∀ᵐ x ∂(hausdorff n X).restrict (ball q.val (4 * ρ)),
        localGamma (hausdorff n X) hX.quadratic w w x ≤
          ((1 + F) / R) ^ 2 * (((hausdorff n X).real (ball p R))⁻¹ *
            ∫ y in ball p R, (SobolevSpace.toLp (hausdorff n X) hX.quadratic w y) ^ 2
              ∂hausdorff n X) := by
    have hq : dist q.val p < τ * R := q.property
    have hqR : dist q.val p ≤ R := by nlinarith only [hq, hτ1, hR]
    have hsub : ball q.val (δ * R) ⊆ ball p R := by
      apply Metric.ball_subset_ball'
      nlinarith only [hq, hδτ, hR]
    have hsub8 : ball q.val (8 * ρ) ⊆ ball q.val (δ * R / 2) := by
      apply ball_subset_ball
      dsimp only [ρ]
      ring_nf
      exact le_rfl
    have hsub8full : ball q.val (8 * ρ) ⊆ ball p R :=
      hsub8.trans ((ball_subset_ball (by
        have hh := mul_pos hδ hR
        linarith only [hh] : δ * R / 2 ≤ δ * R)).trans hsub)
    have hnorm := harmonicTargetNorm_le_of_volume hX hR (mul_pos hδ hR)
      (zero_le_one.trans hD) hsub (hvol p R hR hcurv q.val hqR) w
    have hvalues : ∀ᵐ x ∂(hausdorff n X).restrict (ball q.val (8 * ρ)),
        |SobolevSpace.toLp (hausdorff n X) hX.quadratic w x| ≤ A := by
      filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub8
        (hmean q.val (δ * R) (mul_pos hδ hR) hcurvδ w (hw.mono _ _ hsub))] with x hx
      exact hx.trans (by dsimp only [A]; nlinarith only [hnorm, hM])
    have hp := hpoisson q.val ρ hρ hcurvρ w 0 A hA
      ((isConstantLaplacianOn_zero_iff _ _ _ _).mpr (hw.mono _ _ hsub8full)) hvalues
    have hnormsq := normalized_sobolev_mean_sq (hausdorff n X) hX.quadratic (ball p R)
      (hX.finiteOnBounded _ isBounded_ball).ne w
    have heq : (P * (A / ρ + |(0 : ℝ)| * ρ)) ^ 2 =
        (F / R) ^ 2 * (harmonicTargetNorm hX p R w) ^ 2 := by
      dsimp only [A, F, ρ]
      simp only [abs_zero, zero_mul, add_zero]
      field_simp
    have hcoeff : (F / R) ^ 2 ≤ ((1 + F) / R) ^ 2 := by
      apply pow_le_pow_left₀ (div_nonneg hF hR.le)
      apply div_le_div_of_nonneg_right _ hR.le
      linarith
    filter_upwards [hp] with x hx
    rw [heq] at hx
    have hh := hx.trans (mul_le_mul_of_nonneg_right hcoeff
      (sq_nonneg (harmonicTargetNorm hX p R w)))
    simpa only [harmonicTargetNorm, hnormsq] using hh
  let U : ball p (τ * R) → Set X := fun q => ball q.val (4 * ρ)
  obtain ⟨s, hs, hcover⟩ := (HereditarilyLindelofSpace.isLindelof (ball p (τ * R))).elim_countable_subcover
    U (fun _ => isOpen_ball) (by
      intro x hx
      exact mem_iUnion.mpr ⟨⟨x, hx⟩, mem_ball_self (by positivity)⟩)
  exact ae_restrict_of_ae_restrict_of_subset hcover
    ((ae_restrict_biUnion_iff U hs _).mpr (fun q _ => hlocal q))

end RegularPointCoordinates

end

end OAI
