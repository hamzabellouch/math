import Mathlib
import OAI.Probability.GaussianRegression.Main
import OAI.Probability.MemoryPrecision.CubeContinuation

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter EuclideanGeometry
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise

noncomputable section
universe u v

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise
namespace MemoryPrecision
open NoiselessRegression

def UnitBallVolume (m : ℕ) : ℝ :=
  let exponent : ℝ≥0∞ := @OfNat.ofNat ℝ≥0∞ 2
    (@instOfNatAtLeastTwo ℝ≥0∞ 2 ENNReal.instAddCommMonoidWithOne.toNatCast
      (Mathlib.Meta.NormNum.instAtLeastTwo (nat_lit 0)))
  let euclideanGroup := PiLp.normedAddCommGroup exponent (fun _ : Fin m => ℝ)
  letI : MeasurableSpace (Space m) := WithLp.measurableSpace exponent (Fin m → ℝ)
  let euclideanVolume := @volume (Space m) (@measureSpaceOfInnerProductSpace (Space m)
    euclideanGroup (PiLp.innerProductSpace (𝕜 := ℝ) (fun _ : Fin m => ℝ))
    (space_finiteDimensional m) inferInstance inferInstance)
  (euclideanVolume (@Metric.ball (Space m)
    (PiLp.instPseudoMetricSpace (p := exponent) (β := fun _ : Fin m => ℝ))
    (WithLp.toLp exponent (fun _ : Fin m => (0 : ℝ))) 1)).toReal

def CoordinateUnit (m : ℕ) : Space m :=
  let exponent : ℝ≥0∞ := @OfNat.ofNat ℝ≥0∞ 2
    (@instOfNatAtLeastTwo ℝ≥0∞ 2 ENNReal.instAddCommMonoidWithOne.toNatCast
      (Mathlib.Meta.NormNum.instAtLeastTwo (nat_lit 0)))
  WithLp.toLp exponent (fun j : Fin m => if (j:ℕ) = 0 then (1:ℝ) else 0)

lemma gaussianVariance_nonneg (δ : ℝ) : 0 ≤ δ^2 := sq_nonneg δ

def GaussianKernel (m : ℕ) (δ : ℝ) (y : Space m) : ℝ :=
  let exponent : ℝ≥0∞ := @OfNat.ofNat ℝ≥0∞ 2
    (@instOfNatAtLeastTwo ℝ≥0∞ 2 ENNReal.instAddCommMonoidWithOne.toNatCast
      (Mathlib.Meta.NormNum.instAtLeastTwo (nat_lit 0)))
  ∏ index, gaussianPDFReal 0 ⟨δ^2, gaussianVariance_nonneg δ⟩
    (@WithLp.ofLp exponent (Fin m → ℝ) y index)

def RadialMixture (m : ℕ) (δ r : ℝ) : ℝ :=
  UnitBallVolume m * r^m * (r / δ^2) * GaussianKernel m δ (r • CoordinateUnit m)

def GaussianAmplitude (m : ℕ) (δ : ℝ) : ℝ :=
  (1 / Real.sqrt (2 * Real.pi * δ^2)) ^ m

lemma coordinateUnit_norm (m : ℕ) (hm : 1 ≤ m) : ‖CoordinateUnit m‖ = 1 := by
  have he : ‖CoordinateUnit m‖^2 = 1 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    change (∑ j : Fin m, (if (j:ℕ) = 0 then (1:ℝ) else 0)^2) = 1
    let j : Fin m := ⟨0, by omega⟩
    rw [Finset.sum_eq_single j]
    · simp [j]
    · intro b _ hb
      have hb0 : (b:ℕ) ≠ 0 := by intro h; apply hb; exact Fin.ext h
      simp [hb0]
    · simp
  nlinarith [norm_nonneg (CoordinateUnit m)]

lemma gaussianKernel_radial (m : ℕ) (δ : ℝ) (y : Space m) :
    GaussianKernel m δ y = GaussianAmplitude m δ *
      Real.exp (-‖y‖^2 / (2*δ^2)) := by
  change (∏ j, (Real.sqrt (2*Real.pi*δ^2))⁻¹ *
    Real.exp (-(y j - 0)^2 / (2*δ^2))) = _
  simp only [sub_zero, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
  rw [← Real.exp_sum]
  unfold GaussianAmplitude
  simp only [one_div, Fintype.card_fin]
  congr 1
  congr 1
  rw [EuclideanSpace.real_norm_sq_eq, ← Finset.sum_div, Finset.sum_neg_distrib]

lemma gaussianKernel_nonneg (m : ℕ) (δ : ℝ) (y : Space m) :
    0 ≤ GaussianKernel m δ y :=
  Finset.prod_nonneg (fun _ _ => gaussianPDFReal_nonneg _ _ _)

lemma gaussianKernel_continuous (m : ℕ) (δ : ℝ) : Continuous (GaussianKernel m δ) := by
  have he : GaussianKernel m δ = fun y => GaussianAmplitude m δ *
      Real.exp (-‖y‖^2 / (2*δ^2)) := funext (gaussianKernel_radial m δ)
  rw [he]
  fun_prop

lemma unitBallVolume_pos (m : ℕ) : 0 < UnitBallVolume m := by
  exact ENNReal.toReal_pos (Metric.measure_ball_pos volume 0 zero_lt_one).ne'
    measure_ball_lt_top.ne

lemma volume_ball_eq (m : ℕ) (hm : 1 ≤ m) (x : Space m) {r : ℝ} (hr : 0 < r) :
    (volume : Measure (Space m)) (Metric.ball x r) =
      ENNReal.ofReal (UnitBallVolume m * r^m) := by
  have : NeZero m := ⟨by omega⟩
  rw [Measure.addHaar_ball volume x hr.le]
  simp only [finrank_euclideanSpace, Fintype.card_fin]
  rw [ENNReal.ofReal_mul (unitBallVolume_pos m).le, mul_comm,
    UnitBallVolume, ENNReal.ofReal_toReal measure_ball_lt_top.ne]
  rfl

lemma gaussianKernel_radial_line (m : ℕ) (hm : 1 ≤ m) (δ r : ℝ) :
    GaussianKernel m δ (r • CoordinateUnit m) =
      GaussianAmplitude m δ * Real.exp (-r^2/(2*δ^2)) := by
  rw [gaussianKernel_radial, norm_smul, coordinateUnit_norm m hm, mul_one,
    Real.norm_eq_abs, sq_abs]

lemma gaussianRadial_deriv (m : ℕ) (hm : 1 ≤ m) {δ : ℝ} (hδ : 0 < δ) (r : ℝ) :
    HasDerivAt (fun r : ℝ => -GaussianKernel m δ (r • CoordinateUnit m))
      ((r/δ^2)*GaussianKernel m δ (r • CoordinateUnit m)) r := by
  simp_rw [gaussianKernel_radial_line m hm]
  have ht := ((((hasDerivAt_id r).pow 2).neg.div_const (2*δ^2)).exp.const_mul
    (GaussianAmplitude m δ)).neg
  convert! ht using 1
  simp [id]
  field_simp

lemma gaussianRadial_tendsto (m : ℕ) (hm : 1 ≤ m) {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun r : ℝ => -GaussianKernel m δ (r • CoordinateUnit m)) atTop (𝓝 0) := by
  simp_rw [gaussianKernel_radial_line m hm]
  have he : Tendsto (fun r : ℝ => -r^2/(2*δ^2)) atTop atBot := by
    have hsq : Tendsto (fun r : ℝ => r^2) atTop atTop := tendsto_pow_atTop (by norm_num)
    exact Filter.Tendsto.atBot_div_const (by positivity) (tendsto_neg_atTop_atBot.comp hsq)
  have ht := (Real.tendsto_exp_atBot.comp he).const_mul (GaussianAmplitude m δ)
  simpa using ht.neg

lemma gaussianRadial_tail (m : ℕ) (hm : 1 ≤ m) {δ ρ : ℝ}
    (hδ : 0 < δ) (hρ : 0 ≤ ρ) :
    (∫ r in Set.Ioi ρ, (r/δ^2)*GaussianKernel m δ (r • CoordinateUnit m)) =
      GaussianKernel m δ (ρ • CoordinateUnit m) := by
  have h := integral_Ioi_of_hasDerivAt_of_nonneg'
    (fun r (_ : r ∈ Set.Ici ρ) => gaussianRadial_deriv m hm hδ r)
    (fun _ hr => mul_nonneg (div_nonneg (le_trans hρ hr.le) (sq_nonneg δ))
      (gaussianKernel_nonneg m δ _)) (gaussianRadial_tendsto m hm hδ)
  simpa using h

lemma gaussianKernel_integral (m : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    (∫ y : Space m, GaussianKernel m δ y) = 1 := by
  rw [← (PiLp.volume_preserving_toLp (Fin m)).integral_comp
    (show MeasurableEmbedding (WithLp.toLp 2 : (Fin m → ℝ) → Space m) from
      (MeasurableEquiv.toLp 2 (Fin m → ℝ)).measurableEmbedding)]
  change (∫ y : Fin m → ℝ, ∏ j, gaussianPDFReal 0 ⟨δ^2,sq_nonneg δ⟩ (y j)) = 1
  rw [integral_fintype_prod_volume_eq_pow, integral_gaussianPDFReal_eq_one 0
    (show (⟨δ^2,sq_nonneg δ⟩ : ℝ≥0) ≠ 0 from by
      intro h; have := congrArg (fun x : ℝ≥0 => (x:ℝ)) h; change δ^2 = 0 at this; nlinarith)]
  simp

lemma gaussianKernel_lintegral (m : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    (∫⁻ y : Space m, ENNReal.ofReal (GaussianKernel m δ y)) = 1 := by
  rw [← ofReal_integral_eq_lintegral_ofReal
    (integrable_of_integral_eq_one (gaussianKernel_integral m hδ))
    (Eventually.of_forall (gaussianKernel_nonneg m δ)), gaussianKernel_integral m hδ]
  simp

lemma gaussianRadial_integrable (m : ℕ) (hm : 1 ≤ m) {δ ρ : ℝ}
    (hδ : 0 < δ) (hρ : 0 ≤ ρ) :
    IntegrableOn (fun r : ℝ => (r/δ^2)*GaussianKernel m δ (r • CoordinateUnit m)) (Ioi ρ) :=
  integrableOn_Ioi_deriv_of_nonneg'
    (fun r (_ : r ∈ Set.Ici ρ) => gaussianRadial_deriv m hm hδ r)
    (fun _ hr => mul_nonneg (div_nonneg (le_trans hρ hr.le) (sq_nonneg δ))
      (gaussianKernel_nonneg m δ _)) (gaussianRadial_tendsto m hm hδ)

lemma gaussianRadial_ltail (m : ℕ) (hm : 1 ≤ m) {δ ρ : ℝ}
    (hδ : 0 < δ) (hρ : 0 ≤ ρ) :
    (∫⁻ r in Ioi ρ, ENNReal.ofReal ((r/δ^2)*GaussianKernel m δ (r • CoordinateUnit m))) =
      ENNReal.ofReal (GaussianKernel m δ (ρ • CoordinateUnit m)) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (gaussianRadial_integrable m hm hδ hρ)
    ((ae_restrict_mem measurableSet_Ioi).mono (fun r hr =>
      mul_nonneg (div_nonneg (le_trans hρ hr.le) (sq_nonneg δ)) (gaussianKernel_nonneg m δ _))),
    gaussianRadial_tail m hm hδ hρ]

lemma gaussianKernel_ball_mixture (m : ℕ) (hm : 1 ≤ m) {δ : ℝ} (hδ : 0 < δ)
    (y : Space m) :
    ENNReal.ofReal (GaussianKernel m δ y) =
      ∫⁻ r in Ioi 0, (Metric.ball (0 : Space m) r).indicator
        (fun _ => ENNReal.ofReal ((r/δ^2)*GaussianKernel m δ (r • CoordinateUnit m))) y := by
  have he (r : ℝ) : (Metric.ball (0 : Space m) r).indicator
        (fun _ => ENNReal.ofReal ((r/δ^2)*GaussianKernel m δ (r • CoordinateUnit m))) y =
      (Ioi ‖y‖).indicator
        (fun r => ENNReal.ofReal ((r/δ^2)*GaussianKernel m δ (r • CoordinateUnit m))) r := by
    have hb : y ∈ Metric.ball (0 : Space m) r ↔ ‖y‖ < r := by simp
    by_cases h : ‖y‖ < r
    · rw [Set.indicator_of_mem (hb.mpr h), Set.indicator_of_mem (show r ∈ Ioi ‖y‖ from h)]
    · rw [Set.indicator_of_notMem (mt hb.mp h), Set.indicator_of_notMem (show r ∉ Ioi ‖y‖ from h)]
  simp_rw [he]
  rw [lintegral_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
    inter_eq_left.mpr (Ioi_subset_Ioi (norm_nonneg y)), gaussianRadial_ltail m hm hδ (norm_nonneg y),
    gaussianKernel_radial_line m hm, gaussianKernel_radial]

lemma radialMixture_nonneg (m : ℕ) (δ : ℝ) {r : ℝ} (hr : 0 < r) :
    0 ≤ RadialMixture m δ r := by
  unfold RadialMixture
  exact mul_nonneg (mul_nonneg (mul_nonneg (unitBallVolume_pos m).le (pow_nonneg hr.le _))
    (div_nonneg hr.le (sq_nonneg δ))) (gaussianKernel_nonneg m δ _)

lemma radialMixture_measurable (m : ℕ) (δ : ℝ) : Measurable (RadialMixture m δ) := by
  unfold RadialMixture
  exact (continuous_const.mul (continuous_id.pow _ ) |>.mul
    (continuous_id.div_const _) |>.mul
      ((gaussianKernel_continuous m δ).comp (continuous_id.smul continuous_const))).measurable

lemma radialMixture_lintegral (m : ℕ) (hm : 1 ≤ m) {δ : ℝ} (hδ : 0 < δ) :
    (∫⁻ r in Ioi 0, ENNReal.ofReal (RadialMixture m δ r)) = 1 := by
  have hmeas : Measurable (fun z : Space m × ℝ =>
      (Metric.ball (0 : Space m) z.2).indicator
        (fun _ => ENNReal.ofReal ((z.2/δ^2)*GaussianKernel m δ (z.2 • CoordinateUnit m))) z.1) := by
    have he : (fun z : Space m × ℝ => (Metric.ball (0 : Space m) z.2).indicator
        (fun _ => ENNReal.ofReal ((z.2/δ^2)*GaussianKernel m δ (z.2 • CoordinateUnit m))) z.1) =
      {z : Space m × ℝ | ‖z.1‖ < z.2}.indicator
        (fun z => ENNReal.ofReal ((z.2/δ^2)*GaussianKernel m δ (z.2 • CoordinateUnit m))) := by
      ext z
      by_cases hz : ‖z.1‖ < z.2
      · rw [Set.indicator_of_mem (show z.1 ∈ Metric.ball (0 : Space m) z.2 by simpa using hz),
          Set.indicator_of_mem (show z ∈ {z : Space m × ℝ | ‖z.1‖ < z.2} from hz)]
      · rw [Set.indicator_of_notMem (show z.1 ∉ Metric.ball (0 : Space m) z.2 by simpa using hz),
          Set.indicator_of_notMem (show z ∉ {z : Space m × ℝ | ‖z.1‖ < z.2} from hz)]
    rw [he]
    have hk : Measurable (GaussianKernel m δ) := (gaussianKernel_continuous m δ).measurable
    exact (by fun_prop : Measurable (fun z : Space m × ℝ =>
      ENNReal.ofReal ((z.2/δ^2)*GaussianKernel m δ (z.2 • CoordinateUnit m)))).indicator
      (measurableSet_lt (by fun_prop) (by fun_prop))
  have he := gaussianKernel_lintegral m hδ
  simp_rw [gaussianKernel_ball_mixture m hm hδ] at he
  rw [lintegral_lintegral_swap hmeas.aemeasurable] at he
  convert he using 1
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
  rw [lintegral_indicator Metric.isOpen_ball.measurableSet, setLIntegral_const,
    volume_ball_eq m hm 0 hr]
  unfold RadialMixture
  rw [← ENNReal.ofReal_mul (mul_nonneg (div_nonneg hr.le (sq_nonneg δ))
    (gaussianKernel_nonneg m δ _))]
  congr 1
  ring

lemma radialMixture_integral (m : ℕ) (hm : 1 ≤ m) {δ : ℝ} (hδ : 0 < δ) :
    (∫ r in Ioi 0, RadialMixture m δ r) = 1 := by
  rw [integral_eq_lintegral_of_nonneg_ae
    ((ae_restrict_mem measurableSet_Ioi).mono (fun r hr => radialMixture_nonneg m δ hr))
    (radialMixture_measurable m δ).aestronglyMeasurable, radialMixture_lintegral m hm hδ]
  simp

lemma radialMixture_tail (m : ℕ) (hm : 1 ≤ m) {δ : ℝ} (hδ : 0 < δ) (y : Space m) :
    GaussianKernel m δ y =
      ∫ r in Ioi ‖y‖, RadialMixture m δ r / (UnitBallVolume m * r^m) := by
  rw [integral_congr_ae (show (fun r => RadialMixture m δ r / (UnitBallVolume m * r^m)) =ᵐ[
    volume.restrict (Ioi ‖y‖)] (fun r => (r/δ^2)*GaussianKernel m δ (r • CoordinateUnit m)) from by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
      have hr0 : 0 < r := lt_of_le_of_lt (norm_nonneg y) hr
      unfold RadialMixture
      field_simp [(unitBallVolume_pos m).ne', hr0.ne']), gaussianRadial_tail m hm hδ (norm_nonneg y),
    gaussianKernel_radial_line m hm, gaussianKernel_radial]
end MemoryPrecision


end

end OAI
