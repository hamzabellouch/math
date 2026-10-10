import OAI.Probability.InvariantIsing.Pressure.RandomCoefficientGG
import OAI.Probability.InvariantIsing.Arrays.OverlapBounds
import OAI.Probability.IsingPerceptron.MonomialGgAtMinimum
import OAI.Probability.IsingPerceptron.BoundedTiltAverage

namespace OAI

/-! The deterministic spectral-diagonal perturbation estimate at a parameter minimum. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

lemma bounded_nonnegative_cgf_bounds {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [IsProbabilityMeasure ν] (Y : X → ℝ) (hY : Measurable Y)
    (hbound : ∀ x, Y x ∈ Set.Icc (0 : ℝ) 1) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ cgf Y ν t ∧ cgf Y ν t ≤ t := by
  have he : Integrable (fun x => Real.exp (t * Y x)) ν :=
    exp_mul_integrable_of_bound ν hY
      (fun x => by rw [abs_of_nonneg (hbound x).1]; exact (hbound x).2) t
  have hlo : (1 : ℝ) ≤ ∫ x, Real.exp (t * Y x) ∂ν := by
    calc
      _ = ∫ _ : X, (1 : ℝ) ∂ν := by simp
      _ ≤ _ := integral_mono (integrable_const _) he (fun x =>
        Real.one_le_exp_iff.mpr (mul_nonneg ht (hbound x).1))
  have hhi : (∫ x, Real.exp (t * Y x) ∂ν) ≤ Real.exp t := by
    calc
      _ ≤ ∫ _ : X, Real.exp t ∂ν := integral_mono he (integrable_const _)
        (fun x => Real.exp_le_exp.mpr ((mul_le_mul_of_nonneg_left (hbound x).2 ht).trans_eq (mul_one _)))
      _ = _ := by simp
  constructor
  · exact Real.log_nonneg hlo
  · change Real.log (∫ x, Real.exp (t * Y x) ∂ν) ≤ t
    exact (Real.log_le_log (by linarith) hhi).trans_eq (Real.log_exp t)

lemma integrable_bounded_random_cgf {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (P : Measure Ω) [IsProbabilityMeasure P] (ν : Ω → Measure X) (hν : Measurable ν)
    [∀ ω, IsProbabilityMeasure (ν ω)] (Y : Ω × X → ℝ) (hY : Measurable Y)
    (B : ℝ) (hB : ∀ ω x, |Y (ω, x)| ≤ B) (t : ℝ) :
    Integrable (fun ω => cgf (fun x => Y (ω, x)) (ν ω) t) P := by
  have hm : Measurable (fun ω => cgf (fun x => Y (ω, x)) (ν ω) t) := by
    simpa only [cgf, mgf, referencePartition] using
      (measurable_random_referencePartition hν (hY.const_mul t)).log
  apply Integrable.of_bound hm.aestronglyMeasurable (|t| * B)
  exact ae_of_all _ fun ω => by
    have hYm : Measurable (fun x => t * Y (ω, x)) :=
      (hY.comp (measurable_const.prodMk measurable_id)).const_mul t
    have hb : ∀ x, |t * Y (ω, x)| ≤ |t| * B := fun x => by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hB ω x) (abs_nonneg _)
    have h := logMean_bounds (ν ω) hYm (b := 1) (by norm_num) hb
    simpa only [cgf, mgf, logMean, one_mul, div_one, Real.norm_eq_abs] using h

/-- Unlike the Gaussian perturbation, a diagonal coordinate is a bounded
observable of the random rotation. Its exact tilted fluctuation still follows
from convexity, the deterministic minimum, and three pointwise concentration
bounds. -/
theorem boundedObservable_energy_at_minimum {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X]
    (P : Measure Ω) [IsProbabilityMeasure P] (ν : Ω → Measure X) (hν : Measurable ν)
    [∀ ω, IsProbabilityMeasure (ν ω)] (Y : Ω × X → ℝ) (hY : Measurable Y)
    (B : ℝ) (hB : ∀ ω x, |Y (ω, x)| ≤ B)
    {v c a s δ K : ℝ} (hs : 0 < s) (hK : 0 < K)
    (hmin : ∀ t ∈ Set.Icc (v - s) (v + s),
      -(∫ ω, cgf (fun x => Y (ω, x)) (ν ω) v ∂P) + c * (v - a) ^ 2 ≤
      -(∫ ω, cgf (fun x => Y (ω, x)) (ν ω) t ∂P) + c * (t - a) ^ 2)
    (hconc : ∀ t ∈ ({v - s, v, v + s} : Set ℝ),
      (∫ ω, |cgf (fun x => Y (ω, x)) (ν ω) t -
        (∫ ω', cgf (fun x => Y (ω', x)) (ν ω') t ∂P)| ∂P) ≤ δ) :
    let E := fun ω => ∫ x, |Y (ω, x) - 2 * c * (v - a)|
      ∂(ν ω).tilted (fun x => v * Y (ω, x))
    Integrable E P ∧ (∫ ω, E ω ∂P) ≤ (2 * c + K ^ 2) / (2 * K) + c * s + 4 * δ / s := by
  apply expected_tilted_energy_at_minimum hν hY hs hK
  · exact ae_of_all _ fun ω t => exp_mul_integrable_of_bound (ν ω)
      (hY.comp (measurable_const.prodMk measurable_id)) (hB ω) t
  · exact integrable_bounded_random_cgf P ν hν Y hY B hB
  · exact hmin
  · exact hconc

end InvariantIsing

end

end OAI
