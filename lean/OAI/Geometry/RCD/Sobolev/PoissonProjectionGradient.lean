import OAI.Geometry.RCD.Sobolev.PoissonCommonRegion
import OAI.Geometry.RCD.Harmonic.ActualProjectionUnits
import OAI.Geometry.RCD.Coordinates.AffineFitPerturbation

namespace OAI

/-! # The actual harmonic residual and its physical gradient bound -/

open Set Metric MeasureTheory
open scoped ENNReal InnerProductSpace

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

/-- A sharp L² bound for the actual two-center projection yields a harmonic
Sobolev residual with the corresponding physical gradient bound. -/
theorem poisson_projection_gradient {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [IsFiniteMeasureOnCompacts (hausdorff n X)]
    (hgradient : LocalHarmonicL2GradientInput hX) (hn : 2 ≤ n)
    {P : ℝ} (hP : 0 < P) :
    ∃ Q : ℝ, 0 < Q ∧ ∀ {κ root B J C : ℝ} {first center : X}
      (S1 : DyadicDistanceSources (hausdorff n X) hX.quadratic n κ first root)
      (S2 : DyadicDistanceSources (hausdorff n X) hX.quadratic n κ center root)
      (T1 : DyadicDistanceReplacements (hausdorff n X) hX.quadratic S1 B J C)
      (T2 : DyadicDistanceReplacements (hausdorff n X) hX.quadratic S2 B J C) (i : ℕ),
      let s := distanceSourceRadius root i
      let I := ball center ((1 / 2048) * s)
      dist center first ≤ s / 4 → -1 ≤ K * s ^ 2 →
      ∀ (u : Fin n → SobolevSpace (hausdorff n X) hX.quadratic)
        (eta : SobolevSpace (hausdorff n X) hX.quadratic),
      (∀ j, IsSobolevHarmonicOn (hausdorff n X) hX.quadratic I (u j)) →
      (SobolevSpace.toLp (hausdorff n X) hX.quadratic eta =ᵐ[
        (hausdorff n X).restrict I] fun _ => (1 : ℝ)) →
      ∀ source : ℝ, 0 ≤ source →
      ‖normalizeLocalL2 (hausdorff n X) I (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
        (affineResidual (hausdorff n X) hX.quadratic
          (radiusScaledColumns (hausdorff n X) hX.quadratic s u) I
          (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
          (SobolevSpace.restrictLp (hausdorff n X) hX.quadratic I
            ((s ^ 2)⁻¹ • (T2.replacement i - T1.replacement i))))‖ ≤ P * source →
      ∃ (c : ℝ) (b : Euclidean n) (w : SobolevSpace (hausdorff n X) hX.quadratic),
        w = T2.replacement i - T1.replacement i -
          (c • eta + sobolevColumnMap (hausdorff n X) hX.quadratic u b) ∧
        IsSobolevHarmonicOn (hausdorff n X) hX.quadratic I w ∧
        SobolevSpace.restrictLp (hausdorff n X) hX.quadratic I w =
          affineResidual (hausdorff n X) hX.quadratic u I
            (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
            (SobolevSpace.restrictLp (hausdorff n X) hX.quadratic I (T2.replacement i - T1.replacement i)) ∧
        ∀ᵐ x ∂(hausdorff n X).restrict (ball center ((1 / 4096) * s)),
          localGamma (hausdorff n X) hX.quadratic w w x ≤ Q ^ 2 * s ^ 2 * source ^ 2 := by
  obtain ⟨Cg, hCg, hgrad⟩ := hgradient hn ((1 / 2048 : ℝ) ^ 2) (1 / 2)
    (sq_nonneg _) (by norm_num) (by norm_num)
  refine ⟨2048 * Cg * P, mul_pos (mul_pos (by norm_num) (by linarith)) hP, ?_⟩
  intro κ root B J C first center S1 S2 T1 T2 i s I hroom hcurv u eta hu heta source hsource hbound
  let μ := hausdorff n X
  let hQ := hX.quadratic
  let v := T2.replacement i - T1.replacement i
  have hs : 0 < s := distanceSourceRadius_pos S1.radius_pos i
  have hv : IsSobolevHarmonicOn μ hQ I v :=
    common_replacement_difference_harmonic μ hQ T1 T2 i center
      (by change (1 / 2048 : ℝ) * s + dist center first ≤ s; linarith)
      (by change (1 / 2048 : ℝ) * s + dist center center ≤ s; simp only [dist_self]; linarith)
  have hηharm := isSobolevHarmonicOn_of_local_constant μ hQ I measurableSet_ball eta 1 heta
  have hfin : μ I ≠ ∞ := ne_of_lt (hX.finiteOnBounded _ isBounded_ball)
  obtain ⟨F, c, b, hF, hFharm, hFrep⟩ := affineProjection_harmonic_representative μ hQ
    u I hfin hu eta hηharm (restrictLp_eq_one_of_representative μ hQ eta I hfin heta)
    (SobolevSpace.restrictLp μ hQ I v)
  let w := v - F
  have hwharm : IsSobolevHarmonicOn μ hQ I w := by
    simpa only [w, sub_eq_add_neg, neg_one_smul] using hv.add μ hQ (hFharm.smul μ hQ (-1))
  have hproj : SobolevSpace.restrictLp μ hQ I w = affineResidual μ hQ u I hfin
      (SobolevSpace.restrictLp μ hQ I v) := by
    change SobolevSpace.restrictLp μ hQ I (v - F) = _
    rw [map_sub, hFrep]
    rfl
  have hscaled := radius_scaled_projection μ hQ hs.ne' u I hfin v w hproj
  rw [← hscaled, map_smul, normalizeLocalL2_smul, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr (sq_pos_of_pos hs))] at hbound
  have hsize : ‖normalizeLocalL2 μ I hfin (SobolevSpace.restrictLp μ hQ I w)‖ ≤
      P * s ^ 2 * source := by
    have hh := mul_le_mul_of_nonneg_left hbound (sq_nonneg s)
    calc
      _ = s ^ 2 * ((s ^ 2)⁻¹ * ‖normalizeLocalL2 μ I hfin (SobolevSpace.restrictLp μ hQ I w)‖) := by
        field_simp [hs.ne']
      _ ≤ s ^ 2 * (P * source) := hh
      _ = _ := by ring
  have hlocalcurv : -((1 / 2048 : ℝ) ^ 2) ≤ K * ((1 / 2048) * s) ^ 2 := by
    have hh := mul_le_mul_of_nonneg_left hcurv (sq_nonneg (1 / 2048 : ℝ))
    nlinarith only [hh]
  have hg := hgrad center ((1 / 2048) * s) (by positivity) hlocalcurv w hwharm
  change ∀ᵐ x ∂μ.restrict (ball center ((1 / 2) * ((1 / 2048) * s))),
    localGamma μ hQ w w x ≤ _ at hg
  rw [show (1 / 2 : ℝ) * ((1 / 2048) * s) = (1 / 4096) * s by ring] at hg
  have hsquare := (sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ P * s ^ 2 * source)).mpr hsize
  rw [← normalized_sobolev_mean_sq μ hQ I hfin] at hg
  refine ⟨c, b, w, by dsimp only [w, v]; rw [hF], hwharm, hproj, ?_⟩
  filter_upwards [hg] with x hx
  apply hx.trans
  have hh := mul_le_mul_of_nonneg_left hsquare (sq_nonneg (Cg / ((1 / 2048) * s)))
  convert hh using 1
  field_simp [hs.ne']

end RegularPointCoordinates

end

end OAI
