import OAI.GroupTheory.PolycyclicRecognition.Analysis.FlatSwitchSamples
import OAI.GroupTheory.PolycyclicRecognition.Algebra.ParameterDensityMass
import Mathlib.Probability.ConditionalProbability

namespace OAI

/-! # Uniform interval sampling has a fixed density on the full parameter cube -/

noncomputable section

namespace PolycyclicRecognition

open Set Metric MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

def uniformIntervalLaw (R : ℝ) : Measure ℝ :=
  ProbabilityTheory.cond volume (closedBall 0 R)

theorem uniformIntervalLaw_isProbability {R : ℝ} (hR : 0 < R) :
    IsProbabilityMeasure (uniformIntervalLaw R) := by
  apply cond_isProbabilityMeasure_of_finite
  · simpa only [Real.volume_closedBall, ne_eq, ENNReal.ofReal_eq_zero] using
      (not_le.mpr (mul_pos (by norm_num : (0 : ℝ) < 2) hR))
  · rw [Real.volume_closedBall]
    exact ENNReal.ofReal_ne_top

theorem uniformIntervalLaw_pi_eq {R : ℝ} (hR : 0 < R) (m : ℕ) :
    Measure.pi (fun _ : Fin m => uniformIntervalLaw R) =
      (ENNReal.ofReal (2 * R))⁻¹ ^ m • volume.restrict (closedBall (0 : Fin m → ℝ) R) := by
  let _ := uniformIntervalLaw_isProbability hR
  apply Measure.pi_eq
  intro s hs
  rw [Measure.smul_apply, Measure.restrict_apply (MeasurableSet.univ_pi hs)]
  have hint : univ.pi s ∩ closedBall (0 : Fin m → ℝ) R =
      univ.pi (fun i => s i ∩ closedBall 0 R) := by
    rw [closedBall_pi _ hR.le]
    ext x
    simp only [mem_inter_iff, Set.mem_pi, mem_univ, forall_const, Pi.zero_apply]
    exact ⟨fun h i => ⟨h.1 i, h.2 i⟩, fun h => ⟨fun i => (h i).1, fun i => (h i).2⟩⟩
  rw [hint, volume_pi_pi]
  simp only [uniformIntervalLaw, ProbabilityTheory.cond, Measure.smul_apply,
    Measure.restrict_apply (hs _), smul_eq_mul, Real.volume_closedBall]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem uniformIntervalLaw_pi_le {R : ℝ} (hR : 0 < R) (m : ℕ) :
    Measure.pi (fun _ : Fin m => uniformIntervalLaw R) ≤
      (ENNReal.ofReal (2 * R))⁻¹ ^ m • (volume : Measure (Fin m → ℝ)) := by
  rw [uniformIntervalLaw_pi_eq hR]
  intro s
  simp only [Measure.smul_apply, smul_eq_mul]
  gcongr
  exact Measure.restrict_le_self

theorem uniformIntervalLaw_pi_ae_mem {R : ℝ} (hR : 0 < R) (m : ℕ) :
    ∀ᵐ x : Fin m → ℝ ∂Measure.pi (fun _ => uniformIntervalLaw R), x ∈ closedBall 0 R := by
  rw [uniformIntervalLaw_pi_eq hR]
  exact Measure.ae_smul_measure (ae_restrict_mem measurableSet_closedBall) _

theorem subexponential_volume_of_uniform_samples {R : ℝ} (hR : 0 < R) (m : ℕ)
    (E : ℝ → Set (Fin m → ℝ)) (hER : ∀ r, E r ⊆ closedBall 0 R)
    (hprob : HasSubexponentialLowerBound
      (fun r => (Measure.pi (fun _ : Fin m => uniformIntervalLaw R) (E r)).toReal)) :
    HasSubexponentialLowerBound (fun r => (volume (E r)).toReal) := by
  let d : ℝ≥0 := ((ENNReal.ofReal (2 * R))⁻¹ ^ m).toNNReal
  have htop : (ENNReal.ofReal (2 * R))⁻¹ ^ m ≠ ∞ := by
    apply ENNReal.pow_ne_top
    exact ENNReal.inv_ne_top.mpr (by positivity)
  have hd : (d : ℝ≥0∞) = (ENNReal.ofReal (2 * R))⁻¹ ^ m := ENNReal.coe_toNNReal htop
  apply subexponential_volume_of_probability (fun _ => volume)
    (fun _ => Measure.pi (fun _ : Fin m => uniformIntervalLaw R)) E (fun _ => d)
    (fun r => ne_top_of_le_ne_top (measure_closedBall_lt_top.ne) (measure_mono (hER r)))
    (fun _ => by rw [hd]; exact uniformIntervalLaw_pi_le hR m) hprob
    (subexponential_upper_const _) (Eventually.of_forall fun _ => ?_)
  exact ENNReal.toNNReal_pos (pow_ne_zero _ (ENNReal.inv_ne_zero.mpr ENNReal.ofReal_ne_top)) htop

end PolycyclicRecognition

end

end OAI
