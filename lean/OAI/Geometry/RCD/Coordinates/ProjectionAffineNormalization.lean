import OAI.Geometry.RCD.Harmonic.ScaledHarmonicAffine
import OAI.Geometry.RCD.Coordinates.ExactNormalizationComparison
import OAI.Geometry.RCD.Coordinates.LinearNormalization
import OAI.Geometry.RCD.Harmonic.RadialVolumeUnits
import OAI.Geometry.RCD.Metric.VolumeRigidityInput
import OAI.Geometry.RCD.Harmonic.FirstOrderLocalization

namespace OAI

/-! # Affine nondegeneracy at the two actual projection radii -/

open Set Metric MeasureTheory
open scoped ENNReal InnerProductSpace

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

/-- A splitting frame normalized on the large ball gives both affine
bounds needed by the actual projection. The small-ball normalizer is
constructed from the positive Gram, then compared to that same large frame. -/
theorem projection_affine_bounds {K : ℝ} {n : ℕ} {hX : NoncollapsedRCD K n X}
    [IsFiniteMeasureOnCompacts (hausdorff n X)]
    (hgradient : LocalHarmonicL2GradientInput hX)
    (hmean : LocalHarmonicL2MeanValueInput hX) (hn : 2 ≤ n)
    {κ : ℝ} (hκ : 0 ≤ κ) :
    ∃ H : ℝ, 0 ≤ H ∧ ∀ (p : X) (s R : ℝ), 0 < s → s / 4096 ≤ R → R ≤ s →
      -κ ≤ K * R ^ 2 →
      ∀ (u : Fin n → SobolevSpace (hausdorff n X) hX.quadratic) (V W : X → Euclidean n)
        (N : Euclidean n ≃L[ℝ] Euclidean n) (epsilon : ℝ), 0 ≤ epsilon →
      (n : ℝ) ^ 2 * (((5 / 3 : ℝ) * (16384 : ℝ) ^ n) * epsilon) ≤ 1 / 2 →
      (∀ j, IsSobolevHarmonicOn (hausdorff n X) hX.quadratic (ball p (2 * s)) (u j)) →
      ContinuousOn V (ball p (2 * s)) → V p = 0 →
      (∀ j, SobolevSpace.toLp (hausdorff n X) hX.quadratic (u j) =ᵐ[
        (hausdorff n X).restrict (ball p (2 * s))] fun x => V x j) →
      FirstOrderSplittingOn (hausdorff n X) hX.quadratic p (2 * s) epsilon
        (transformedColumn (hausdorff n X) hX.quadratic u N) W →
      IsExactMeanNormalization (hausdorff n X) hX.quadratic
        (sobolevColumnMap (hausdorff n X) hX.quadratic u) (ball p (2 * s)) measurableSet_ball N →
      (∀ t : ℝ, 0 < t → t ≤ 2 * s →
        |(hausdorff n X).real (ball p t) / (euclideanUnitVolume n * t ^ n) - 1| ≤ 1 / 4) →
      ∀ eta : SobolevSpace (hausdorff n X) hX.quadratic,
      (SobolevSpace.toLp (hausdorff n X) hX.quadratic eta =ᵐ[
        (hausdorff n X).restrict (ball p R)] fun _ => (1 : ℝ)) →
      ∀ c a, |c| + s * ‖N.symm a‖ ≤ H *
        ‖normalizeLocalL2 (hausdorff n X) (ball p R)
          (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
          (affineCoordinateMap (hausdorff n X) hX.quadratic u (ball p R)
            (ne_of_lt (hX.finiteOnBounded _ isBounded_ball)) (c, a))‖ := by
  obtain ⟨Cg, Cm, hCg, hCm, hbound⟩ := scaled_harmonic_affine_nondegeneracy hgradient hmean hn hκ
  refine ⟨8193 * (Cm + Cg), by linarith, ?_⟩
  intro p s R hs hRlo hRhi hcurv u V W N epsilon hepsilon hsmall hu hV hcenter hrep hfirst hN hvolume eta heta c a
  let μ := hausdorff n X
  let hQ := hX.quadratic
  let Cvol := (5 / 3 : ℝ) * (16384 : ℝ) ^ n
  have hCvol : 0 ≤ Cvol := by dsimp only [Cvol]; positivity
  let U := sobolevColumnMap μ hQ u
  have hR : 0 < R := lt_of_lt_of_le (by positivity : 0 < s / 4096) hRlo
  have hsub : ball p (R / 2) ⊆ ball p (2 * s) := ball_subset_ball (by linarith)
  have hpos : 0 < μ.real (ball p (R / 2)) :=
    (quarter_volume_bounds (by positivity : 0 < R / 2) (euclideanUnitVolume_pos n)
      (hvolume (R / 2) (by positivity) (by linarith))).1
  have hsmallpos : 0 < μ.real (ball p (s / 8192)) :=
    (quarter_volume_bounds (by positivity : 0 < s / 8192) (euclideanUnitVolume_pos n)
      (hvolume (s / 8192) (by positivity) (by linarith))).1
  have hvol : μ.real (ball p (2 * s)) ≤ Cvol * μ.real (ball p (R / 2)) := by
    have hh := radial_fraction_volume_ratio (by positivity : 0 < 2 * s)
      (by norm_num : (0 : ℝ) < 1 / 16384) (euclideanUnitVolume_pos n)
      (hvolume (2 * s) (by positivity) le_rfl)
      (hvolume ((1 / 16384) * (2 * s)) (by positivity) (by linarith))
    have heq : (1 / 16384 : ℝ) * (2 * s) = s / 8192 := by ring
    have hpow : ((1 / 16384 : ℝ) ^ n)⁻¹ = (16384 : ℝ) ^ n := by simp
    rw [heq, hpow] at hh
    have hi := (div_le_iff₀ hsmallpos).mp hh
    exact hi.trans (mul_le_mul_of_nonneg_left
      (measureReal_mono (ball_subset_ball (by linarith : s / 8192 ≤ R / 2))
        (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))) hCvol)
  have hcompare (v : Euclidean n) : ‖N.symm v‖ ^ 2 ≤
      2 * ⟪v, sobolevMeanGram μ hQ U (ball p (R / 2)) measurableSet_ball v⟫_ℝ := by
    have hh := (exact_normalization_subball_bounds μ hQ u N hfirst hN
      (ball p (R / 2)) measurableSet_ball hsub
      (ne_of_gt (hX.fullSupport p (R / 2) (by positivity)))
      (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
      (ne_of_gt (hX.fullSupport p (2 * s) (by positivity)))
      (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
      hCvol hepsilon hvol v).1
    rw [meanGram_energy_of_exact_normalization μ hQ U (ball p (2 * s)) measurableSet_ball N hN] at hh
    have hmul := mul_le_mul_of_nonneg_right hsmall (sq_nonneg ‖N.symm v‖)
    change (n : ℝ) ^ 2 * (Cvol * epsilon) * ‖N.symm v‖ ^ 2 ≤ (1 / 2) * ‖N.symm v‖ ^ 2 at hmul
    nlinarith only [hh, hmul]
  obtain ⟨Ninner, hinner⟩ := exists_exact_mean_normalization μ hQ U (ball p (R / 2))
    measurableSet_ball (by
      intro v hv
      have hnv : N.symm v ≠ 0 := by
        intro hz
        apply hv
        have hh := congrArg N hz
        simpa only [N.apply_symm_apply, map_zero] using hh
      have hp := sq_pos_of_pos (norm_pos_iff.mpr hnv)
      nlinarith only [hcompare v, hp])
  have hframe (v : Euclidean n) : ‖N.symm v‖ ≤ 2 * ‖Ninner.symm v‖ := by
    have hh := hcompare v
    rw [meanGram_energy_of_exact_normalization μ hQ U (ball p (R / 2)) measurableSet_ball Ninner hinner] at hh
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
    nlinarith [sq_nonneg ‖Ninner.symm v‖]
  have hRsub : ball p R ⊆ ball p (2 * s) := ball_subset_ball (by linarith)
  have hh := hbound p R hR hcurv u V (fun j => (hu j).mono μ hQ hRsub)
    (hV.mono hRsub) hcenter
    (fun j => ae_restrict_of_ae_restrict_of_subset hRsub (hrep j)) Ninner hinner eta heta c a
  let alpha := ‖normalizeLocalL2 μ (ball p R) (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
    (affineCoordinateMap μ hQ u (ball p R) (ne_of_lt (hX.finiteOnBounded _ isBounded_ball)) (c, a))‖
  have hconstant : |c| ≤ (Cm + Cg) * alpha := by
    change |c| + R * ‖Ninner.symm a‖ ≤ (Cm + Cg) * alpha at hh
    nlinarith [mul_nonneg hR.le (norm_nonneg (Ninner.symm a))]
  have hlinear : R * ‖Ninner.symm a‖ ≤ (Cm + Cg) * alpha := by
    change |c| + R * ‖Ninner.symm a‖ ≤ (Cm + Cg) * alpha at hh
    linarith [abs_nonneg c]
  have hterm : s * ‖N.symm a‖ ≤ 8192 * (R * ‖Ninner.symm a‖) := by
    have hx := mul_le_mul_of_nonneg_left (hframe a) hs.le
    have hy := mul_le_mul_of_nonneg_right hRlo (norm_nonneg (Ninner.symm a))
    nlinarith only [hx, hy]
  have hfinal := mul_le_mul_of_nonneg_left hlinear (by norm_num : (0 : ℝ) ≤ 8192)
  change |c| + s * ‖N.symm a‖ ≤ 8193 * (Cm + Cg) * alpha
  nlinarith only [hconstant, hterm, hfinal]

end RegularPointCoordinates

end

end OAI
