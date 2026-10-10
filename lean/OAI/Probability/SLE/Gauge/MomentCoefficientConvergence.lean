import OAI.Probability.SLE.Mass.MassCompensatorSelection

namespace OAI

/-! Bounded truncation of the prescribed moment coefficients. An
integrable finite-level density is enough to pass from convergence in
probability of the discrete mass to its clipped weighted moments. -/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal

namespace SLEExactGauge

lemma continuous_clip (u : ℝ) : Continuous (Target.clip u) := by
  exact (continuous_id.max continuous_const).min continuous_const

lemma clip_nonneg {u : ℝ} (hu : 0 ≤ u) (x : ℝ) : 0 ≤ Target.clip u x :=
  le_min (le_max_right x 0) hu

lemma clip_le (u x : ℝ) : Target.clip u x ≤ u := min_le_right _ _

/-- This is the inner limit in the paper's explicit coefficient formula;
the density need only be integrable, not uniformly bounded. -/
theorem weighted_clip_pow_integral_tendsto
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (X : ℕ → Ω → ℝ) (Y w : Ω → ℝ)
    (hX : ∀ n, AEStronglyMeasurable (X n) P) (hw : Integrable w P)
    (hXY : TendstoInMeasure P X atTop Y) (u : ℝ) (hu : 0 ≤ u) (k : ℕ) :
    Tendsto (fun n => ∫ ω, w ω*(Target.clip u (X n ω))^k ∂P) atTop
      (𝓝 (∫ ω, w ω*(Target.clip u (Y ω))^k ∂P)) := by
  apply tendsto_of_subseq_tendsto
  intro ns hns
  obtain ⟨ms,_,hms⟩ := (hXY.comp hns).exists_seq_tendsto_ae
  refine ⟨ms,?_⟩
  apply tendsto_integral_of_dominated_convergence (fun ω => ‖w ω‖*u^k)
  · intro n
    exact hw.aestronglyMeasurable.mul
      (((continuous_clip u).comp_aestronglyMeasurable (hX (ns (ms n)))).pow k)
  · exact hw.norm.mul_const (u^k)
  · intro n
    filter_upwards [] with ω
    rw [norm_mul,norm_pow,Real.norm_of_nonneg (clip_nonneg hu _)]
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (clip_nonneg hu _) (clip_le _ _) k) (norm_nonneg _)
  · filter_upwards [hms] with ω hω
    exact tendsto_const_nhds.mul (((continuous_clip u).continuousAt.tendsto.comp hω).pow k)

end SLEExactGauge

end

end OAI
