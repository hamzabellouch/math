import OAI.Probability.PosteriorReplicas.Measures.EqualLabelTransfer

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter Metric
open scoped ENNReal NNReal Topology
noncomputable section
namespace PosteriorReplicas

@[fun_prop] lemma continuous_labelNorm {k : ℕ} : Continuous (@labelNorm k) := by
  unfold labelNorm
  fun_prop

@[fun_prop] lemma measurable_ballDensityVersion {d k : ℕ} (ν : Measure (Vec d)) [SFinite ν] :
    Measurable (fun z : Rows d k × Labels k => ballDensityVersion ν z.1 z.2) := by
  unfold ballDensityVersion
  apply Measurable.liminf
  intro n
  apply Measurable.const_mul
  exact measurable_measure_prodMk_left (show MeasurableSet
    {z : (Rows d k × Labels k) × Vec d |
      labelNorm (labels z.1.1 z.2 - z.1.2) < (n + 1 : ℝ)⁻¹} from
    measurableSet_lt (continuous_labelNorm.measurable.comp (by fun_prop)) measurable_const)

@[fun_prop] lemma measurable_gaussianDensityVersion {d k : ℕ} (ν : Measure (Vec d)) [SFinite ν] :
    Measurable (fun z : Rows d k × Labels k => gaussianDensityVersion ν z.1 z.2) := by
  unfold gaussianDensityVersion
  apply Measurable.liminf
  intro n
  apply Measurable.lintegral_prod_right
  apply ENNReal.measurable_ofReal.comp
  fun_prop

section Generic
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

lemma closedBall_ae_eq_ball (μ : Measure E) (hμ : μ ≪ volume) (y : E) (r : ℝ) :
    closedBall y r =ᵐ[μ] ball y r := by
  rw [ae_eq_set, closedBall_sdiff_ball, sdiff_eq_empty.mpr ball_subset_closedBall, measure_empty]
  exact ⟨hμ (Measure.addHaar_sphere volume y r), rfl⟩

lemma ae_ball_differentiation {μ : Measure E} [IsFiniteMeasure μ] {h : E → ℝ≥0∞}
    (hh : Measurable h) (hμ : μ = volume.withDensity h) :
    ∀ᵐ y ∂(volume : Measure E),
      Tendsto (fun r => μ (ball y r) / volume (ball y r)) (𝓝[>] 0) (𝓝 (h y)) := by
  have hac : μ ≪ volume := by rw [hμ]; exact withDensity_absolutelyContinuous _ _
  have hrn : μ.rnDeriv volume =ᵐ[volume] h := by
    rw [hμ]
    exact Measure.rnDeriv_withDensity volume hh
  filter_upwards [Besicovitch.ae_tendsto_rnDeriv μ volume, hrn] with y hy hry
  rw [hry] at hy
  convert hy using 1
  ext r
  rw [(closedBall_ae_eq_ball μ hac y r).measure_eq,
    (closedBall_ae_eq_ball volume (Measure.AbsolutelyContinuous.refl _) y r).measure_eq]

omit [Nontrivial E] in
lemma bounded_density_measure_le [Nontrivial E] {μ : Measure E} {h : E → ℝ≥0∞}
    (hμ : μ = volume.withDensity h) {M : ℝ≥0∞} (hM : ∀ x, h x ≤ M)
    (s : Set E) (hs : MeasurableSet s) : μ s ≤ M * volume s := by
  rw [hμ, withDensity_apply _ hs]
  simpa using lintegral_mono (μ := volume.restrict s) hM

end Generic

end PosteriorReplicas
end

end OAI
