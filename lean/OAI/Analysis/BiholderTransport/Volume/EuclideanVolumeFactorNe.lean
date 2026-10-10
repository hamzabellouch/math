import Mathlib
import OAI.Analysis.BiholderTransport.Model

namespace OAI

section
section
noncomputable section
open Set Filter MeasureTheory Manifold Metric Bundle
open scoped Topology ContDiff ENNReal NNReal

namespace WeakMTWTransport

lemma euclideanVolumeFactor_ne_zero (n : ℕ) : euclideanVolumeFactor n≠0 := by
  have hdim : (Module.finrank ℝ (Model n):ℝ)=(n:ℝ) := by simp [Model]
  have hH : (Measure.hausdorffMeasure (n:ℝ) : Measure (Model n)).IsAddHaarMeasure := by
    rw [←hdim]; infer_instance
  exact ENNReal.div_ne_zero.mpr ⟨(measure_ball_pos volume (0:Model n) zero_lt_one).ne',
    measure_ball_lt_top.ne⟩

lemma euclideanVolumeFactor_ne_top (n : ℕ) : euclideanVolumeFactor n≠⊤ := by
  have hdim : (Module.finrank ℝ (Model n):ℝ)=(n:ℝ) := by simp [Model]
  have hH : (Measure.hausdorffMeasure (n:ℝ) : Measure (Model n)).IsAddHaarMeasure := by
    rw [←hdim]; infer_instance
  exact ENNReal.div_ne_top measure_ball_lt_top.ne
    (measure_ball_pos _ (0:Model n) zero_lt_one).ne'

instance metricVolume_model_haar (n : ℕ) :
    (metricVolume (M := Model n) n).IsAddHaarMeasure := by
  have hdim : (Module.finrank ℝ (Model n):ℝ)=(n:ℝ) := by simp [Model]
  have hH : (Measure.hausdorffMeasure (n:ℝ) : Measure (Model n)).IsAddHaarMeasure := by
    rw [←hdim]; infer_instance
  exact Measure.IsAddHaarMeasure.smul _ (euclideanVolumeFactor_ne_zero n)
    (euclideanVolumeFactor_ne_top n)

lemma lipschitzOn_metricVolume_image_le {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
    {C : ℝ≥0} {f : X → Y} {s : Set X} (hf : LipschitzOnWith C f s) (n : ℕ) :
    metricVolume n (f '' s)≤(C:ℝ≥0∞)^n*metricVolume n s := by
  have H := hf.hausdorffMeasure_image_le (d := (n:ℝ)) (by positivity)
  have hh := mul_le_mul_right H (euclideanVolumeFactor n)
  simpa only [metricVolume,Measure.smul_apply,smul_eq_mul,ENNReal.rpow_natCast,
    mul_assoc,mul_comm,mul_left_comm] using hh

end WeakMTWTransport
end
end
end

end OAI
