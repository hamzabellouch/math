import OAI.Geometry.RCD.Harmonic.HarmonicUnitMean
import OAI.Geometry.RCD.Metric.RescaledBallVolume
import OAI.Geometry.RCD.Harmonic.HarmonicMeanValueInput
import OAI.Geometry.RCD.Harmonic.FirstOrderLocalization
import Mathlib.Topology.Compactness.Lindelof

namespace OAI

/-! # The published harmonic mean-value input from RCD calculus

The local level-set iteration proves Jiang's half-ball L² estimate at unit
rescaled curvature. A fixed-radius interior cover and the CD ball-volume
comparison give the stated estimate for every bounded curvature parameter.
-/

open Set Metric Filter MeasureTheory
open scoped ENNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

private theorem small_radius_curvature {K R a s : ℝ}
    (ha : 0 ≤ a) (hs : 0 ≤ s) (hsa : s ≤ 1/(a+1))
    (h : -a ≤ K*R^2) : -1 ≤ K*(s*R)^2 := by
  have hs1 : s ≤ 1 := hsa.trans ((div_le_one (by linarith)).mpr (by linarith))
  have hs2 : s^2 ≤ s := by nlinarith
  have hsa' : s*(a+1) ≤ 1 := (le_div_iff₀ (by linarith)).mp hsa
  have has2 : a*s^2 ≤ 1 := by nlinarith
  calc
    -1 ≤ -a*s^2 := by linarith
    _ ≤ (K*R^2)*s^2 := mul_le_mul_of_nonneg_right h (sq_nonneg s)
    _ = _ := by ring

omit [ProperSpace X] in
private theorem target_norm_le_of_ball_volume {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) {p q : X} {R r D : ℝ}
    (hR : 0 < R) (hr : 0 < r) (hD : 0 ≤ D)
    (hsub : ball q r ⊆ ball p R)
    (hvol : (hausdorff n X).real (ball p R) ≤ D*(hausdorff n X).real (ball q r))
    (w : SobolevSpace (hausdorff n X) hX.quadratic) :
    harmonicTargetNorm hX q r w ≤ Real.sqrt D*harmonicTargetNorm hX p R w := by
  have hfinR := (hX.finiteOnBounded (ball p R) isBounded_ball).ne
  have hfinr := (hX.finiteOnBounded (ball q r) isBounded_ball).ne
  have hposR := ENNReal.toReal_pos (hX.fullSupport p R hR).ne' hfinR
  have hposr := ENNReal.toReal_pos (hX.fullSupport q r hr).ne' hfinr
  have hnormR : (harmonicTargetNorm hX p R w)^2 =
      ((hausdorff n X).real (ball p R))⁻¹*
        ∫ x in ball p R, (SobolevSpace.toLp (hausdorff n X) hX.quadratic w x)^2
          ∂hausdorff n X := normalized_sobolev_mean_sq _ _ _ hfinR w
  have hnormr : (harmonicTargetNorm hX q r w)^2 =
      ((hausdorff n X).real (ball q r))⁻¹*
        ∫ x in ball q r, (SobolevSpace.toLp (hausdorff n X) hX.quadratic w x)^2
          ∂hausdorff n X := normalized_sobolev_mean_sq _ _ _ hfinr w
  have hb := average_nonneg_le_of_subset (hausdorff n X) hsub hposr hposR
    (Lp.memLp (SobolevSpace.toLp (hausdorff n X) hX.quadratic w)).integrable_sq.integrableOn
    (fun _ => sq_nonneg _) (sq_nonneg (harmonicTargetNorm hX p R w)) hvol hnormR.ge
  rw [← hnormr] at hb
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  rwa [mul_pow,Real.sq_sqrt hD]

/-- The precise half-ball harmonic L²-to-L∞ input is a theorem of the
retained RCD structure, with no mean-value or gradient assumption. -/
theorem NoncollapsedRCD.harmonicMeanValueInput {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) : LocalHarmonicL2MeanValueInput hX := by
  classical
  let := hX.separable
  intro hn a ha
  obtain ⟨M,hM,hunit⟩ := hX.harmonic_unit_mean_value hn
  let δ := min (1/4) (1/(a+1))
  have hδ : 0 < δ := lt_min (by norm_num) (by positivity)
  have hδa : δ ≤ 1/(a+1) := min_le_right _ _
  have hδquarter : δ ≤ 1/4 := min_le_left _ _
  have hδ1 : δ ≤ 1 := by linarith
  obtain ⟨D,hD,hvolume⟩ := hX.rescaled_ball_volume_factor hn ha hδ hδ1
  let C := 1+M*Real.sqrt D
  have hM0 : 0 ≤ M := zero_le_one.trans hM
  have hD0 : 0 ≤ D := zero_le_one.trans hD
  have hC : 1 ≤ C := le_add_of_nonneg_right (mul_nonneg hM0 (Real.sqrt_nonneg _))
  refine ⟨C,hC,?_⟩
  intro p R hR hcurv u hu
  have hδR : 0 < δ*R := mul_pos hδ hR
  have hcurvsmall : -1 ≤ K*(δ*R)^2 := small_radius_curvature ha hδ.le hδa hcurv
  have hlocal (q : ball p (R/2)) :
      ∀ᵐ y ∂(hausdorff n X).restrict (ball q.val (δ*R/2)),
        |SobolevSpace.toLp (hausdorff n X) hX.quadratic u y| ≤
          C*harmonicTargetNorm hX p R u := by
    have hq : dist q.val p < R/2 := q.property
    have hqR : dist q.val p ≤ R := by linarith
    have hsub : ball q.val (δ*R) ⊆ ball p R := by
      apply Metric.ball_subset_ball'
      nlinarith
    have hnorm := target_norm_le_of_ball_volume hX hR hδR hD0 hsub
      (hvolume p R hR hcurv q.val hqR) u
    filter_upwards [hunit q.val (δ*R) hδR hcurvsmall u (hu.mono _ _ hsub)] with y hy
    have hm := mul_le_mul_of_nonneg_left hnorm hM0
    have hT : 0 ≤ harmonicTargetNorm hX p R u := norm_nonneg _
    exact hy.trans (by dsimp only [C]; nlinarith only [hm,hT])
  let U : ball p (R/2) → Set X := fun q => ball q.val (δ*R/2)
  obtain ⟨s,hs,hcover⟩ := (HereditarilyLindelofSpace.isLindelof (ball p (R/2))).elim_countable_subcover
    U (fun _ => isOpen_ball) (by
      intro x hx
      exact mem_iUnion.mpr ⟨⟨x,hx⟩,mem_ball_self (by positivity)⟩)
  exact ae_restrict_of_ae_restrict_of_subset hcover
    ((ae_restrict_biUnion_iff U hs _).mpr (fun q _ => hlocal q))

end RegularPointCoordinates

end

end OAI
