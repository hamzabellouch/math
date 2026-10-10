import OAI.Probability.FreeIsing.Ising.CanonicalPosteriorStops

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal

namespace Problem367.IsingObservationFactor
open IsingObservationInnovation IsingCopyEnergy PosteriorCompensatorStopping

variable {d : ℕ} {beta : ℝ}
variable {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]

def copyResponseDriftDifference (beta : ℝ) (v : TreeVertex d)
    (t : ℝ≥0) (q : Joint d) : ℝ :=
  posterior beta v t q.2.1 * copyResponseEnergy beta v true t q -
    posterior beta v t q.2.2 * copyResponseEnergy beta v false t q

lemma copyResponseDriftDifference_progressive (beta : ℝ) (v : TreeVertex d) :
    IsStronglyProgressive ContinuousCopyBrownian.joinedFiltration
      (copyResponseDriftDifference beta v) := by
  have hl := isStronglyProgressive_infiniteGibbsSpinMean
    ContinuousCopyBrownian.joinedFiltration beta v _
    IsingConditionalCopyBounds.progressive_leftObservation
  have hr := isStronglyProgressive_infiniteGibbsSpinMean
    ContinuousCopyBrownian.joinedFiltration beta v _
    IsingConditionalCopyBounds.progressive_rightObservation
  exact (hl.mul (copyResponseEnergy_progressive beta v true)).sub
    (hr.mul (copyResponseEnergy_progressive beta v false))

lemma copyResponseEnergy_nonneg (beta : ℝ) (v : TreeVertex d) (j : Bool)
    (t : ℝ≥0) (q : Joint d) : 0 ≤ copyResponseEnergy beta v j t q :=
  tsum_nonneg (fun _ => sq_nonneg _)

theorem abs_copyResponseDriftDifference_le (beta : ℝ) (v : TreeVertex d)
    (t : ℝ≥0) (q : Joint d) :
    |copyResponseDriftDifference beta v t q| ≤
      copyResponseEnergy beta v true t q + copyResponseEnergy beta v false t q := by
  have hl : |posterior beta v t q.2.1| ≤ 1 := posterior_norm_le_one beta v t q.2.1
  have hr : |posterior beta v t q.2.2| ≤ 1 := posterior_norm_le_one beta v t q.2.2
  unfold copyResponseDriftDifference
  calc
    _ ≤ |posterior beta v t q.2.1 * copyResponseEnergy beta v true t q| +
        |posterior beta v t q.2.2 * copyResponseEnergy beta v false t q| := abs_sub _ _
    _ = |posterior beta v t q.2.1| * copyResponseEnergy beta v true t q +
        |posterior beta v t q.2.2| * copyResponseEnergy beta v false t q := by
      rw [abs_mul, abs_mul, abs_of_nonneg (copyResponseEnergy_nonneg beta v true t q),
        abs_of_nonneg (copyResponseEnergy_nonneg beta v false t q)]
    _ ≤ _ := add_le_add
      (mul_le_of_le_one_left (copyResponseEnergy_nonneg beta v true t q) hl)
      (mul_le_of_le_one_left (copyResponseEnergy_nonneg beta v false t q) hr)

theorem copyResponseDriftDifference_integrable
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (v : TreeVertex d) (T : ℝ≥0) :
    Integrable (fun p : ℝ × Joint d => copyResponseDriftDifference beta v p.1.toNNReal p.2)
      ((volume.restrict (Ioc (0 : ℝ) T)).prod (copies beta μ)) := by
  have hm := (stronglyMeasurable_joint_of_isStronglyProgressive
    (copyResponseDriftDifference_progressive beta v)).comp_measurable
      ((measurable_real_toNNReal.comp measurable_fst).prodMk measurable_snd)
  apply ((copyResponseEnergy_integrable hμ hb v true T).add
    (copyResponseEnergy_integrable hμ hb v false T)).mono' hm.aestronglyMeasurable
  exact Eventually.of_forall (fun p => abs_copyResponseDriftDifference_le beta v p.1.toNNReal p.2)

theorem ae_all_abs_driftPrimitive_le_commonResponseCompensator
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (v : TreeVertex d) :
    ∀ᵐ q ∂copies beta μ, ∀ t : ℝ≥0,
      |nnrealTimePrimitive (copyResponseDriftDifference beta v) t q| ≤
        commonResponseCompensator beta v t q := by
  have hiB := ae_intervalIntegrable_horizons_of_joint
    (μ := copies beta μ) (a := copyResponseDriftDifference beta v)
    (fun n => by simpa only [NNReal.coe_natCast] using
      copyResponseDriftDifference_integrable hμ hb v (n : ℝ≥0))
  have hiE := ae_intervalIntegrable_horizons_of_joint
    (μ := copies beta μ)
    (a := fun t q => copyResponseEnergy beta v true t q + copyResponseEnergy beta v false t q)
    (fun n => by
      have hi := (copyResponseEnergy_integrable hμ hb v true (n : ℝ≥0)).add
        (copyResponseEnergy_integrable hμ hb v false (n : ℝ≥0))
      convert hi using 1; rfl)
  filter_upwards [hiB, hiE] with q hB hE
  intro t
  obtain ⟨n, hn⟩ := exists_nat_ge (t : ℝ)
  have hrestrict {f : ℝ → ℝ} (hi : IntervalIntegrable f volume 0 (n : ℝ)) :
      IntervalIntegrable f volume 0 (t : ℝ) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le t.coe_nonneg).mpr
      (((intervalIntegrable_iff_integrableOn_Ioc_of_le (Nat.cast_nonneg n)).mp hi).mono_set
        (Ioc_subset_Ioc le_rfl hn))
  unfold nnrealTimePrimitive commonResponseCompensator
  calc
    _ ≤ ∫ s in (0 : ℝ)..(t : ℝ), |copyResponseDriftDifference beta v s.toNNReal q| :=
      intervalIntegral.abs_integral_le_integral_abs t.coe_nonneg
    _ ≤ _ := intervalIntegral.integral_mono t.coe_nonneg (hrestrict (hB n)).abs
      (hrestrict (hE n)) (fun s => abs_copyResponseDriftDifference_le beta v s.toNNReal q)

theorem ae_all_abs_commonResponseCompensator_stopped_le
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (v : TreeVertex d) (n : ℕ) {τ : Joint d → WithTop ℝ≥0}
    (hτ : ∀ q, τ q ≤ commonPosteriorExit beta v n q) :
    ∀ᵐ q ∂copies beta μ, ∀ t : ℝ≥0,
      |stoppedProcess (commonResponseCompensator beta v)
        τ t q| ≤ (n : ℝ) + 1 := by
  filter_upwards [commonResponseCompensator_continuous hμ hb v] with q hc
  intro t
  apply abs_stoppedProcess_le_of_le_exit hc
    (by simp [commonResponseCompensator, nnrealTimePrimitive]; positivity) _ t
  exact (hτ q).trans ((min_le_left _ _).trans (min_le_right _ _))

theorem ae_all_abs_stoppedDriftPrimitive_le
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (v : TreeVertex d) (n : ℕ) {τ : Joint d → WithTop ℝ≥0}
    (hτ : ∀ q, τ q ≤ commonPosteriorExit beta v n q) :
    ∀ᵐ q ∂copies beta μ, ∀ t : ℝ≥0,
      |stoppedProcess (nnrealTimePrimitive (copyResponseDriftDifference beta v))
        τ t q| ≤ (n : ℝ) + 1 := by
  filter_upwards [ae_all_abs_driftPrimitive_le_commonResponseCompensator hμ hb v,
    ae_all_abs_commonResponseCompensator_stopped_le hμ hb v n hτ] with q hB hE
  intro t
  exact (hB _).trans ((le_abs_self _).trans (hE t))

theorem ae_all_abs_cutoffDriftPrimitive_le
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (v : TreeVertex d) (n : ℕ) {τ : Joint d → WithTop ℝ≥0}
    (hτ : ∀ q, τ q ≤ commonPosteriorExit beta v n q) :
    ∀ᵐ q ∂copies beta μ, ∀ t : ℝ≥0,
      |nnrealTimePrimitive
        (StoppedTimePrimitive.stopDensity (copyResponseDriftDifference beta v)
          τ) t q| ≤ (n : ℝ) + 1 := by
  filter_upwards [ae_all_abs_stoppedDriftPrimitive_le hμ hb v n hτ] with q hq
  intro t
  rw [← StoppedTimePrimitive.stoppedProcess_primitive]
  exact hq t

end Problem367.IsingObservationFactor

end

end OAI
