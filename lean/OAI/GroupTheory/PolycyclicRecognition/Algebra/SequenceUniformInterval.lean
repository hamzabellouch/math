import OAI.GroupTheory.PolycyclicRecognition.Analysis.UniformIntervalSamples
import OAI.GroupTheory.PolycyclicRecognition.Algebra.SequenceParameterDensity
import OAI.GroupTheory.PolycyclicRecognition.Algebra.SequenceSubexponentialOperations

namespace OAI

/-! # Successful parameter volume along the profile-scale sequence -/

noncomputable section

namespace PolycyclicRecognition

open Set Metric MeasureTheory Filter
open scoped Topology ENNReal NNReal

theorem subexponential_volume_of_uniform_samples_sequence {R : ℝ}
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop) (hR : 0 < R) (m : ℕ)
    (E : ℕ → Set (Fin m → ℝ)) (hER : ∀ r, E r ⊆ closedBall 0 R)
    (hprob : HasSubexponentialLowerBoundSeq scale
      (fun r => (Measure.pi (fun _ : Fin m => uniformIntervalLaw R) (E r)).toReal)) :
    HasSubexponentialLowerBoundSeq scale (fun r => (volume (E r)).toReal) := by
  let d : ℝ≥0 := ((ENNReal.ofReal (2 * R))⁻¹ ^ m).toNNReal
  have htop : (ENNReal.ofReal (2 * R))⁻¹ ^ m ≠ ∞ := by
    apply ENNReal.pow_ne_top
    exact ENNReal.inv_ne_top.mpr (by positivity)
  have hd : (d : ℝ≥0∞) = (ENNReal.ofReal (2 * R))⁻¹ ^ m := ENNReal.coe_toNNReal htop
  apply subexponential_volume_of_probability_sequence scale (fun _ => volume)
    (fun _ => Measure.pi (fun _ : Fin m => uniformIntervalLaw R)) E (fun _ => d)
    (fun r => ne_top_of_le_ne_top (measure_closedBall_lt_top.ne) (measure_mono (hER r)))
    (fun _ => by rw [hd]; exact uniformIntervalLaw_pi_le hR m) hprob
    (sequence_subexponential_upper_const hscale _) (Eventually.of_forall fun _ => ?_)
  exact ENNReal.toNNReal_pos (pow_ne_zero _ (ENNReal.inv_ne_zero.mpr ENNReal.ofReal_ne_top)) htop

end PolycyclicRecognition

end

end OAI
