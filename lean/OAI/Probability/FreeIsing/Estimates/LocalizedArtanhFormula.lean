import OAI.Probability.FreeIsing.Estimates.ConstructedArtanhFormula
import OAI.Probability.FreeIsing.Estimates.IntegrableTimePrimitive
import OAI.Probability.FreeIsing.Martingales.DominatedMartingaleRightContinuation
import OAI.Probability.FreeIsing.Martingales.StoppedTimePrimitive
import OAI.Probability.FreeIsing.Posterior.CompensatorStopping
import OAI.Probability.FreeIsing.Trees.InnovationPathMap

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal Topology
namespace Problem367.LocalizedArtanhFormula
open ArtanhMartingaleFormula PosteriorStoppingTimes PosteriorCompensatorStopping
open StoppedTimePrimitive DominatedMartingaleRightContinuation

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}

theorem integrable_stopDensity [SFinite μ]
    {F : Filtration ℝ≥0 mΩ} {a : ℝ≥0 → Ω → ℝ} {τ : Ω → WithTop ℝ≥0}
    (ha : IsStronglyProgressive F a) (hτ : IsStoppingTime F τ) (T : ℝ≥0)
    (hint : Integrable (fun p : ℝ × Ω => a p.1.toNNReal p.2)
      ((volume.restrict (Ioc (0 : ℝ) T)).prod μ)) :
    Integrable (fun p : ℝ × Ω => stopDensity a τ p.1.toNNReal p.2)
      ((volume.restrict (Ioc (0 : ℝ) T)).prod μ) := by
  have hprog := isStronglyProgressive_stopDensity ha hτ
  have hmeas : StronglyMeasurable
      (fun p : ℝ × Ω => stopDensity a τ p.1.toNNReal p.2) :=
    (stronglyMeasurable_joint_of_isStronglyProgressive hprog).comp_measurable
      ((measurable_real_toNNReal.comp measurable_fst).prodMk measurable_snd)
  apply hint.norm.mono' hmeas.aestronglyMeasurable
  apply Eventually.of_forall
  intro p
  simp only [stopDensity]
  split_ifs <;> simp

theorem isLocalizingSequence_jointExit_primitive [SFinite μ]
    {F : Filtration ℝ≥0 mΩ} {M a : ℝ≥0 → Ω → ℝ}
    (hprogM : IsStronglyProgressive F M) (hproga : IsStronglyProgressive F a)
    (ha : ∀ n : ℕ, Integrable (fun p : ℝ × Ω => a p.1.toNNReal p.2)
      ((volume.restrict (Ioc (0 : ℝ) (n : ℝ))).prod μ))
    (hcompact : ∀ᵐ ω ∂μ, ∀ T : ℝ≥0,
      ∃ r < (1 : ℝ), ∀ t ≤ T, |M t ω| ≤ r) :
    IsLocalizingSequence F.rightCont (jointExit M (nnrealTimePrimitive a)) μ :=
  isLocalizingSequence_jointExit_rightCont hprogM.stronglyAdapted.adapted
    (isStronglyProgressive_nnrealTimePrimitive hproga).stronglyAdapted.adapted
    hcompact (ae_continuous_nnrealTimePrimitive_of_joint ha)

theorem exists_jointExit_artanh_decomposition [IsProbabilityMeasure μ]
    {F : Filtration ℝ≥0 mΩ} {M a : ℝ≥0 → Ω → ℝ}
    (hM : Martingale M F μ)
    (hQ : Martingale (fun t ω => M t ω ^ 2 - nnrealTimePrimitive a t ω) F μ)
    (hprogM : IsStronglyProgressive F M) (hproga : IsStronglyProgressive F a)
    (hcM : ∀ᵐ ω ∂μ, Continuous (fun t => M t ω))
    (hzero : ∀ᵐ ω ∂μ, M 0 ω = 0)
    (hbound : ∀ᵐ ω ∂μ, ∀ t, |M t ω| ≤ 1)
    (hnonneg : ∀ᵐ ω ∂μ, ∀ t, 0 ≤ a t ω)
    (ha : ∀ T : ℝ≥0, Integrable (fun p : ℝ × Ω => a p.1.toNNReal p.2)
      ((volume.restrict (Ioc (0 : ℝ) T)).prod μ))
    (n : ℕ) (T : ℝ≥0) :
    let τ := jointExit M (nnrealTimePrimitive a) n
    let N := stoppedProcess M τ
    ∃ L : Ω → ℝ, StronglyMeasurable L ∧ MemLp L 2 μ ∧
      Tendsto (fun k => ∫ ω,
        (BrownianGrid.uniformSum N (fun t ω => firstWeight (N t ω)) T k ω - L ω) ^ 2 ∂μ)
        atTop (𝓝 0) ∧
      (fun ω => Real.artanh (N T ω) - Real.artanh (M 0 ω)) =ᵐ[μ]
        fun ω => L ω + stoppedProcess
          (nnrealTimePrimitive (fun t ω => secondWeight (M t ω) * a t ω)) τ T ω := by
  let A := nnrealTimePrimitive a
  let τ := jointExit M A n
  let N := stoppedProcess M τ
  have hproga' := isStronglyProgressive_mono_filtration F.le_rightCont hproga
  have hprogM' := isStronglyProgressive_mono_filtration F.le_rightCont hprogM
  have hprogA := isStronglyProgressive_nnrealTimePrimitive hproga
  have hprogA' := isStronglyProgressive_mono_filtration F.le_rightCont hprogA
  have hτ : IsStoppingTime F.rightCont τ :=
    isStoppingTime_jointExit hprogM'.stronglyAdapted.adapted hprogA'.stronglyAdapted.adapted n
  have hai (k : ℕ) : Integrable (fun p : ℝ × Ω => a p.1.toNNReal p.2)
      ((volume.restrict (Ioc (0 : ℝ) (k : ℝ))).prod μ) := by
    simpa only [NNReal.coe_natCast] using ha (k : ℝ≥0)
  have hcA : ∀ᵐ ω ∂μ, Continuous (fun t => A t ω) :=
    ae_continuous_nnrealTimePrimitive_of_joint hai
  have hmonoA : ∀ᵐ ω ∂μ, Monotone (fun t => A t ω) :=
    ae_monotone_nnrealTimePrimitive_of_joint hai hnonneg
  have hAint (t : ℝ≥0) : Integrable (A t) μ :=
    nnrealTimePrimitive_integrable (ha t)
  have hApos : ∀ᵐ ω ∂μ, ∀ t, 0 ≤ A t ω :=
    hnonneg.mono (fun ω hω t => nnrealTimePrimitive_nonneg hω t)
  have hA0 (ω : Ω) : A 0 ω = 0 := by simp [A, nnrealTimePrimitive]
  have hN : Martingale N F.rightCont μ :=
    martingale_stoppedProcess_rightCont hM hprogM hcM
      (fun _ => ⟨fun _ => 1, integrable_const _,
        hbound.mono (fun ω hω t _ => hω t)⟩) hτ
  have hQτ := martingale_stopped_compensatedSquare_rightCont hQ hprogM hprogA
    hcM hcA (by norm_num : (0 : ℝ) ≤ 1) hbound hApos hmonoA hAint hτ
  have hcN : ∀ᵐ ω ∂μ, ContinuousOn (fun t => N t ω) (Icc 0 T) :=
    hcM.mono (fun ω hω => (continuous_stoppedProcess hω τ).continuousOn)
  have hcB : ∀ᵐ ω ∂μ, ContinuousOn (fun t => stoppedProcess A τ t ω) (Icc 0 T) :=
    hcA.mono (fun ω hω => (continuous_stoppedProcess hω τ).continuousOn)
  have hmonoB : ∀ᵐ ω ∂μ, MonotoneOn (fun t => stoppedProcess A τ t ω) (Icc 0 T) :=
    hmonoA.mono (fun ω hω => (monotone_stoppedProcess hω τ).monotoneOn _)
  have hbN : ∀ᵐ ω ∂μ, ∀ t, |N t ω| ≤ threshold n := by
    filter_upwards [hcM, hzero] with ω hc hz
    exact abs_stopped_posterior_le hc hz n
  have hB0 (ω : Ω) : stoppedProcess A τ 0 ω = 0 := by
    rw [stoppedProcess_eq_of_le (show ((0 : ℝ≥0) : WithTop ℝ≥0) ≤ τ ω from zero_le)]
    exact hA0 ω
  have htotal : ∀ᵐ ω ∂μ,
      stoppedProcess A τ T ω - stoppedProcess A τ 0 ω ≤ (n : ℝ) + 1 := by
    filter_upwards [hcA] with ω hc
    rw [hB0, sub_zero]
    exact (le_abs_self _).trans (abs_stopped_compensator_le hc (hA0 ω) n T)
  have hprimitive : ∀ᵐ ω ∂μ, ∀ t ∈ Icc 0 T,
      stoppedProcess A τ t ω = stoppedProcess A τ 0 ω +
        nnrealTimePrimitive (stopDensity a τ) t ω := by
    apply Eventually.of_forall
    intro ω t _
    rw [hB0, zero_add]
    exact stoppedProcess_primitive a τ t ω
  obtain ⟨L, hLm, hL2, hlim, heq⟩ :=
    ConstructedArtanhFormula.exists_artanh_decomposition T hN hQτ
      (stronglyMeasurable_joint_of_isStronglyProgressive (hprogM'.stoppedProcess hτ)).measurable
      hcN hcB hmonoB (threshold_nonneg n) (threshold_lt_one n) hbN
      (by positivity : (0 : ℝ) ≤ (n : ℝ) + 1) htotal
      (integrable_stopDensity hproga' hτ T (ha T)) hprimitive
  refine ⟨L, hLm, hL2, hlim, ?_⟩
  filter_upwards [heq] with ω hω
  have hN0 : N 0 ω = M 0 ω :=
    stoppedProcess_eq_of_le (show ((0 : ℝ≥0) : WithTop ℝ≥0) ≤ τ ω from zero_le)
  rw [hN0] at hω
  rw [stoppedProcess_weighted_primitive M secondWeight a τ T ω]
  exact hω

end Problem367.LocalizedArtanhFormula

end

end OAI
