import OAI.Probability.FreeIsing.Gibbs.PosteriorSymmetry
import OAI.Probability.FreeIsing.Posterior.InteriorLocalization
import OAI.Probability.FreeIsing.Posterior.ProgressiveIsingPosterior

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace Problem367

theorem HasFreeIsingLaw.continuous_posterior_all_time_field_bound
    {d : ℕ} {beta : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (ν : TreeVertex d → Measure Ω)
    {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ v, IsBrownianReal (B v) (ν v))
    (hmB : ∀ v t, Measurable (B v t))
    {m : TreeVertex d → ℝ≥0 →
      ((TreeVertex d → IsingSpin) × (TreeVertex d → Ω)) → ℝ}
    (hcm : ∀ v, ∀ᵐ p ∂μ.prod (Measure.infinitePi ν), Continuous (fun t => m v t p))
    (hversion : ∀ v t, m v t =ᵐ[μ.prod (Measure.infinitePi ν)]
      (fun p => infiniteGibbsSpinMean beta v
        (fun i => (t : ℝ) * spinSign (p.1 i) + B i t (p.2 i)))) :
    ∀ᵐ p ∂μ.prod (Measure.infinitePi ν), ∀ v,
      (∀ t, m v t p ∈ Set.Ioo (-1 : ℝ) 1 ∧
        |Real.artanh (m v t p) - ((t : ℝ) * spinSign (p.1 v) + B v t (p.2 v))| ≤
          (d : ℝ) * beta) ∧
      Continuous (fun t => Real.artanh (m v t p)) := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have (vertex : TreeVertex d) : IsProbabilityMeasure (ν vertex) :=
    (hB vertex).isGaussianProcess.isProbabilityMeasure
  apply ae_all_iff.mpr
  intro v
  have hX : ∀ᵐ p ∂μ.prod (Measure.infinitePi ν),
      Continuous (fun t : ℝ≥0 => (t : ℝ) * spinSign (p.1 v) + B v t (p.2 v)) := by
    have hnoise := (planted_noise_coordinate_measurePreserving μ ν v).quasiMeasurePreserving.ae
      (hB v).cont
    filter_upwards [hnoise] with p hp
    exact (continuous_subtype_val.mul continuous_const).add hp
  have hb : ∀ t, ∀ᵐ p ∂μ.prod (Measure.infinitePi ν),
      m v t p ∈ Set.Ioo (-1 : ℝ) 1 ∧
      |Real.artanh (m v t p) - ((t : ℝ) * spinSign (p.1 v) + B v t (p.2 v))| ≤
        (d : ℝ) * beta := by
    intro t
    filter_upwards [hversion v t,
      hμ.infiniteGibbsSpinMean_brownian_field_bound hbeta ν
        (fun i => (hB i).toIsPreBrownianReal) hmB t v] with p hp hb
    rw [hp]
    exact hb
  filter_upwards [hcm v,
    PosteriorInteriorLocalization.ae_all_field_bound_of_continuous (hcm v) hX hb]
      with p hp hb
  exact ⟨hb, PosteriorInteriorLocalization.continuous_artanh_of_interior hp
    (fun t => (hb t).1)⟩

theorem HasFreeIsingLaw.continuous_posterior_compact_localization
    {d : ℕ} {beta : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (ν : TreeVertex d → Measure Ω)
    {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ v, IsBrownianReal (B v) (ν v))
    (hmB : ∀ v t, Measurable (B v t))
    {m : TreeVertex d → ℝ≥0 →
      ((TreeVertex d → IsingSpin) × (TreeVertex d → Ω)) → ℝ}
    (hcm : ∀ v, ∀ᵐ p ∂μ.prod (Measure.infinitePi ν), Continuous (fun t => m v t p))
    (hversion : ∀ v t, m v t =ᵐ[μ.prod (Measure.infinitePi ν)]
      (fun p => infiniteGibbsSpinMean beta v
        (fun i => (t : ℝ) * spinSign (p.1 i) + B i t (p.2 i)))) :
    ∀ᵐ p ∂μ.prod (Measure.infinitePi ν), ∀ v, ∀ T : ℝ≥0, ∀ᶠ n in atTop,
      ∀ t ≤ T, |m v t p| < PosteriorInteriorLocalization.radius n := by
  filter_upwards [ae_all_iff.mpr hcm,
    hμ.continuous_posterior_all_time_field_bound hbeta ν hB hmB hcm hversion]
      with p hc hb
  intro v T
  have h := PosteriorInteriorLocalization.eventually_uniform_abs_lt_radius
    (s := Set.Icc (0 : ℝ≥0) T) isCompact_Icc (hc v).continuousOn
    (fun t _ => (hb v).1 t |>.1)
  filter_upwards [h] with n hn
  exact fun t ht => hn t ⟨bot_le, ht⟩

theorem HasFreeIsingLaw.posterior_version_initial_zero
    {d : ℕ} {beta : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ)
    (ν : TreeVertex d → Measure Ω)
    {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ v, IsPreBrownianReal (B v) (ν v))
    {m : TreeVertex d → ℝ≥0 →
      ((TreeVertex d → IsingSpin) × (TreeVertex d → Ω)) → ℝ}
    (hversion : ∀ v, m v 0 =ᵐ[μ.prod (Measure.infinitePi ν)]
      (fun p => infiniteGibbsSpinMean beta v (fun i => B i 0 (p.2 i)))) :
    ∀ᵐ p ∂μ.prod (Measure.infinitePi ν), ∀ v,
      m v 0 p = 0 ∧ Real.artanh (m v 0 p) = 0 := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  filter_upwards [ae_all_iff.mpr hversion,
    infiniteGibbsSpinMean_brownian_zero beta μ ν hB] with p hp hz
  intro v
  have hzero : m v 0 p = 0 := by
    rw [hp v]
    simpa only [zero_mul, zero_add] using hz v
  exact ⟨hzero, by rw [hzero, Real.artanh_zero]⟩

theorem isStronglyProgressive_artanh
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (F : Filtration ℝ≥0 mΩ) {m : ℝ≥0 → Ω → ℝ}
    (hm : IsStronglyProgressive F m) :
    IsStronglyProgressive F (fun t ω => Real.artanh (m t ω)) := by
  have ha : Measurable Real.artanh := by
    unfold Real.artanh
    fun_prop
  intro t
  let : MeasurableSpace Ω := F t
  exact (ha.comp (hm t).measurable).stronglyMeasurable

end Problem367

end

end OAI
