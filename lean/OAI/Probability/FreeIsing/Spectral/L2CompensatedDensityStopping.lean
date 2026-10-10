import OAI.Probability.FreeIsing.Estimates.IntegrableTimePrimitive
import OAI.Probability.FreeIsing.Martingales.StoppedTimePrimitive
import OAI.Probability.FreeIsing.Spectral.L2CompensatedSquareStopping
import OAI.Probability.FreeIsing.Trees.InnovationPathMap

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal Topology

namespace Problem367.L2CompensatedDensityStopping

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {F : Filtration ℝ≥0 mΩ} {M q : ℝ≥0 → Ω → ℝ}

theorem integrable_density_on_horizon
    (hq : ∀ N : ℕ, Integrable (fun p : ℝ × Ω => q p.1.toNNReal p.2)
      ((volume.restrict (Ioc (0 : ℝ) (N : ℝ))).prod μ))
    (T : ℝ≥0) :
    Integrable (fun p : ℝ × Ω => q p.1.toNNReal p.2)
      ((volume.restrict (Ioc (0 : ℝ) (T : ℝ))).prod μ) := by
  obtain ⟨N, hN⟩ := exists_nat_ge (T : ℝ)
  exact (hq N).mono_measure (Measure.prod_mono
    (Measure.restrict_mono (Ioc_subset_Ioc le_rfl hN) le_rfl) le_rfl)

theorem integrable_stopped_density_on_horizon
    (hprogq : IsStronglyProgressive F q)
    (hq : ∀ N : ℕ, Integrable (fun p : ℝ × Ω => q p.1.toNNReal p.2)
      ((volume.restrict (Ioc (0 : ℝ) (N : ℝ))).prod μ))
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime F.rightCont τ)
    (T : ℝ≥0) :
    Integrable (fun p : ℝ × Ω =>
      StoppedTimePrimitive.stopDensity q τ p.1.toNNReal p.2)
      ((volume.restrict (Ioc (0 : ℝ) (T : ℝ))).prod μ) := by
  have hp := StoppedTimePrimitive.isStronglyProgressive_stopDensity
    (DominatedMartingaleRightContinuation.isStronglyProgressive_mono_filtration
      F.le_rightCont hprogq) hτ
  have hm : StronglyMeasurable (fun p : ℝ × Ω =>
      StoppedTimePrimitive.stopDensity q τ p.1.toNNReal p.2) :=
    (stronglyMeasurable_joint_of_isStronglyProgressive hp).comp_measurable
      ((measurable_real_toNNReal.comp measurable_fst).prodMk measurable_snd)
  apply (integrable_density_on_horizon hq T).mono hm.aestronglyMeasurable
  apply Eventually.of_forall
  intro p
  unfold StoppedTimePrimitive.stopDensity
  split_ifs <;> simp only [le_refl, norm_zero, norm_nonneg]

theorem stopped_martingale_and_compensated_density
    (hM : Martingale M F μ) (h2 : ∀ t, MemLp (M t) 2 μ)
    (hcM : ∀ᵐ ω ∂μ, Continuous (fun t => M t ω))
    (hprogM : IsStronglyProgressive F M)
    (hprogq : IsStronglyProgressive F q)
    (hq0 : ∀ᵐ ω ∂μ, ∀ t, 0 ≤ q t ω)
    (hq : ∀ N : ℕ, Integrable (fun p : ℝ × Ω => q p.1.toNNReal p.2)
      ((volume.restrict (Ioc (0 : ℝ) (N : ℝ))).prod μ))
    (hQ : Martingale (fun t ω => M t ω ^ 2 - nnrealTimePrimitive q t ω) F μ)
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime F.rightCont τ) :
    Martingale (stoppedProcess M τ) F.rightCont μ ∧
      Martingale (fun t ω => stoppedProcess M τ t ω ^ 2 -
        nnrealTimePrimitive (StoppedTimePrimitive.stopDensity q τ) t ω)
        F.rightCont μ := by
  have hA0 : ∀ᵐ ω ∂μ, ∀ t, 0 ≤ nnrealTimePrimitive q t ω :=
    hq0.mono (fun ω hω t => nnrealTimePrimitive_nonneg hω t)
  have hAmono : ∀ᵐ ω ∂μ, Monotone (fun t => nnrealTimePrimitive q t ω) :=
    ae_monotone_nnrealTimePrimitive_of_joint hq hq0
  have hAint (t : ℝ≥0) : Integrable (nnrealTimePrimitive q t) μ :=
    nnrealTimePrimitive_integrable (integrable_density_on_horizon hq t)
  have hcA : ∀ᵐ ω ∂μ, Continuous (fun t => nnrealTimePrimitive q t ω) :=
    ae_continuous_nnrealTimePrimitive_of_joint hq
  refine ⟨L2CompensatedSquareStopping.martingale_stoppedProcess_rightCont
    hM h2 hcM hprogM hτ, ?_⟩
  have hs := L2CompensatedSquareStopping.stopped_compensatedSquare_rightCont
    hM h2 hcM hA0 hAmono hAint hcA hQ hprogM
    (isStronglyProgressive_nnrealTimePrimitive hprogq) hτ
  simpa only [StoppedTimePrimitive.stoppedProcess_primitive] using hs

end Problem367.L2CompensatedDensityStopping

end

end OAI
