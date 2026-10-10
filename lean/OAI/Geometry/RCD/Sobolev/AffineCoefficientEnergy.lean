import OAI.Geometry.RCD.Coordinates.ExactNormalizationComparison
import OAI.Geometry.RCD.Sobolev.HarmonicGradientInput
import OAI.Geometry.RCD.Metric.InwardLocality

namespace OAI

/-! # Coefficient bounds from exact normalization and harmonic energy -/

open Set Metric MeasureTheory
open scoped ENNReal InnerProductSpace

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

/-- Exact mean normalization on the half ball and the harmonic
gradient estimate give affine nondegeneracy with a uniform constant.
The affine constant is allowed to be arbitrary. -/
theorem LocalHarmonicL2GradientInput.affine_coefficient
    {K : ℝ} {n : ℕ} {hX : NoncollapsedRCD K n X}
    (hinput : LocalHarmonicL2GradientInput hX) (hn : 2 ≤ n)
    {κ : ℝ} (hκ : 0 ≤ κ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (p : X) (R : ℝ), 0 < R → -κ ≤ K * R ^ 2 →
      ∀ (u : Fin n → SobolevSpace (hausdorff n X) hX.quadratic)
        (N : Euclidean n ≃L[ℝ] Euclidean n),
      IsExactMeanNormalization (hausdorff n X) hX.quadratic
        (sobolevColumnMap (hausdorff n X) hX.quadratic u)
        (ball p (R / 2)) measurableSet_ball N →
      ∀ (a : Euclidean n) (w : SobolevSpace (hausdorff n X) hX.quadratic) (c : ℝ),
      IsSobolevHarmonicOn (hausdorff n X) hX.quadratic (ball p R) w →
      SobolevSpace.toLp (hausdorff n X) hX.quadratic
        (w - sobolevColumnMap (hausdorff n X) hX.quadratic u a) =ᵐ[
          (hausdorff n X).restrict (ball p R)] (fun _ => c) →
      ‖N.symm a‖ ^ 2 ≤ (C / R) ^ 2 *
        ‖normalizeLocalL2 (hausdorff n X) (ball p R)
          (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
          (SobolevSpace.restrictLp (hausdorff n X) hX.quadratic (ball p R) w)‖ ^ 2 := by
  obtain ⟨C, hC, hgrad⟩ := hinput hn κ (1 / 2) hκ (by norm_num) (by norm_num)
  refine ⟨C, hC, ?_⟩
  intro p R hR hcurv u N hN a w c hw hc
  let μ := hausdorff n X
  let hQ := hX.quadratic
  let s := ball p (R / 2)
  have hs : MeasurableSet s := measurableSet_ball
  have hfin : μ s ≠ ∞ := ne_of_lt (hX.finiteOnBounded _ isBounded_ball)
  have hpos : 0 < μ.real s := ENNReal.toReal_pos
    (ne_of_gt (hX.fullSupport p _ (by positivity))) hfin
  let : IsFiniteMeasure (μ.restrict s) := ⟨by simpa only [Measure.restrict_apply_univ] using hfin.lt_top⟩
  have hsub : s ⊆ ball p R := ball_subset_ball (by linarith)
  have heq := localGamma_self_eq_of_constant_difference μ hQ s w
    (sobolevColumnMap μ hQ u a) c (ae_restrict_of_ae_restrict_of_subset hsub hc)
  have hg := hgrad p R hR hcurv w hw
  rw [show (1 / 2 : ℝ) * R = R / 2 by ring] at hg
  have hi : (∫ x in s, localGamma μ hQ (sobolevColumnMap μ hQ u a)
      (sobolevColumnMap μ hQ u a) x ∂μ) ≤
      (C / R) ^ 2 * (μ.real (ball p R))⁻¹ *
        (∫ x in ball p R, (SobolevSpace.toLp μ hQ w x) ^ 2 ∂μ) * μ.real s := by
    calc
      _ ≤ ∫ _x in s, (C / R) ^ 2 * ((μ.real (ball p R))⁻¹ *
          ∫ x in ball p R, (SobolevSpace.toLp μ hQ w x) ^ 2 ∂μ) ∂μ := by
        apply integral_mono_ae (localGamma_memL1 μ hQ _ _).integrableOn (integrable_const _)
        filter_upwards [heq, hg] with x hx hbound
        exact hx.symm.trans_le hbound
      _ = _ := by simp only [integral_const, smul_eq_mul, Measure.real,
          Measure.restrict_apply_univ]; ring
  have hnrm := exact_mean_inverse_norm_sq μ hQ (sobolevColumnMap μ hQ u)
    s hs N hN a
  rw [real_inner_comm, sobolevMeanGram_inner] at hnrm
  rw [hnrm, normalized_sobolev_mean_sq]
  have hh := mul_le_mul_of_nonneg_left hi (inv_nonneg.mpr hpos.le)
  convert hh using 1
  field_simp [hpos.ne']
  rfl

end RegularPointCoordinates

end

end OAI
