import OAI.Probability.FreeIsing.Brownian.UniformGrid
import OAI.Probability.FreeIsing.Martingales.ArtanhMartingaleFormula
import OAI.Probability.FreeIsing.Martingales.InnovationMartingale

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped NNReal Topology

namespace Problem367.NNRealArtanhFormula

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}

def realFiltration (F : Filtration ℝ≥0 mΩ) : Filtration ℝ mΩ :=
  ⟨fun t => F t.toNNReal, fun _ _ h => F.mono (Real.toNNReal_mono h),
    fun t => F.le t.toNNReal⟩

lemma martingale_realExtension {F : Filtration ℝ≥0 mΩ} {M : ℝ≥0 → Ω → ℝ}
    (hM : Martingale M F μ) :
    Martingale (fun t : ℝ => M t.toNNReal) (realFiltration F) μ :=
  ⟨fun _ => hM.stronglyMeasurable _, fun _ _ h => hM.condExp_ae_eq (Real.toNNReal_mono h)⟩

lemma toNNReal_mem_Icc {T : ℝ≥0} {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    t.toNNReal ∈ Set.Icc (0 : ℝ≥0) T := by
  constructor
  · exact bot_le
  · simpa only [Real.toNNReal_coe] using Real.toNNReal_mono ht.2

lemma toNNReal_point (T : ℝ≥0) (n i : ℕ) :
    (EnergyRiemann.point T n i).toNNReal = BrownianGrid.uniformGrid T n i := by
  apply NNReal.eq
  rw [Real.coe_toNNReal _ (by unfold EnergyRiemann.point; positivity)]
  simp only [EnergyRiemann.point, BrownianGrid.uniformGrid, NNReal.coe_div,
    NNReal.coe_mul, NNReal.coe_natCast]
  ring

theorem artanh_eq_stochasticLimit_add_primitive [IsProbabilityMeasure μ]
    {F : Filtration ℝ≥0 mΩ} {M A a : ℝ≥0 → Ω → ℝ} (T : ℝ≥0)
    (hM : Martingale M F μ)
    (hQ : Martingale (fun t ω => M t ω ^ 2 - A t ω) F μ)
    (hMm : Measurable (fun p : ℝ≥0 × Ω => M p.1 p.2))
    (hcM : ∀ᵐ ω ∂μ, ContinuousOn (fun t => M t ω) (Set.Icc 0 T))
    (hcA : ∀ᵐ ω ∂μ, ContinuousOn (fun t => A t ω) (Set.Icc 0 T))
    (hmonoA : ∀ᵐ ω ∂μ, MonotoneOn (fun t => A t ω) (Set.Icc 0 T))
    {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1)
    (hbound : ∀ᵐ ω ∂μ, ∀ t, |M t ω| ≤ r)
    {C : ℝ} (hC : 0 ≤ C) (htotal : ∀ᵐ ω ∂μ, A T ω - A 0 ω ≤ C)
    (ha : Integrable (fun p : ℝ × Ω => a p.1.toNNReal p.2)
      ((volume.restrict (Set.Ioc (0 : ℝ) T)).prod μ))
    (hprimitive : ∀ᵐ ω ∂μ, ∀ t ∈ Set.Icc 0 T,
      A t ω = A 0 ω + nnrealTimePrimitive a t ω)
    {L : Ω → ℝ} (hL : Integrable L μ)
    (hlinear : Tendsto (fun n => ∫ ω,
      |BrownianGrid.uniformSum M (fun t ω => ArtanhMartingaleFormula.firstWeight (M t ω))
        T (n + 1) ω - L ω| ∂μ) atTop (𝓝 0)) :
    (fun ω => Real.artanh (M T ω) - Real.artanh (M 0 ω)) =ᵐ[μ]
      fun ω => L ω + nnrealTimePrimitive
        (fun t ω => ArtanhMartingaleFormula.secondWeight (M t ω) * a t ω) T ω := by
  have hmeas : Measurable (fun p : ℝ × Ω => M p.1.toNNReal p.2) :=
    hMm.comp ((measurable_real_toNNReal.comp measurable_fst).prodMk measurable_snd)
  have hcM' : ∀ᵐ ω ∂μ, ContinuousOn (fun t : ℝ => M t.toNNReal ω)
      (Set.Icc (0 : ℝ) T) := by
    filter_upwards [hcM] with ω hω
    exact hω.comp continuous_real_toNNReal.continuousOn (fun _ ht => toNNReal_mem_Icc ht)
  have hcA' : ∀ᵐ ω ∂μ, ContinuousOn (fun t : ℝ => A t.toNNReal ω)
      (Set.Icc (0 : ℝ) T) := by
    filter_upwards [hcA] with ω hω
    exact hω.comp continuous_real_toNNReal.continuousOn (fun _ ht => toNNReal_mem_Icc ht)
  have hmonoA' : ∀ᵐ ω ∂μ, MonotoneOn (fun t : ℝ => A t.toNNReal ω)
      (Set.Icc (0 : ℝ) T) := by
    filter_upwards [hmonoA] with ω hω
    exact fun _ hs _ ht hst => hω (toNNReal_mem_Icc hs) (toNNReal_mem_Icc ht)
      (Real.toNNReal_mono hst)
  have hprim' : ∀ᵐ ω ∂μ, ∀ t ∈ Set.Icc (0 : ℝ) T,
      A t.toNNReal ω = A (0 : ℝ).toNNReal ω +
        ∫ s in (0 : ℝ)..t, a s.toNNReal ω := by
    filter_upwards [hprimitive] with ω hω
    intro t ht
    simpa only [Real.toNNReal_zero, nnrealTimePrimitive, Real.coe_toNNReal _ ht.1] using
      hω t.toNNReal (toNNReal_mem_Icc ht)
  have hlin' : Tendsto (fun n => ∫ ω,
      |ArtanhMartingaleFormula.linearSum (fun t : ℝ => M t.toNNReal)
        (EnergyRiemann.point T (n + 1)) (n + 1) ω - L ω| ∂μ) atTop (𝓝 0) := by
    simpa only [ArtanhMartingaleFormula.linearSum, BrownianGrid.uniformSum,
      BrownianGrid.integralSum, toNNReal_point] using hlinear
  have h := ArtanhMartingaleFormula.artanh_eq_stochasticLimit_add_integral T.coe_nonneg
    (martingale_realExtension hM) (martingale_realExtension hQ) hmeas hcM' hcA' hmonoA'
    hr0 hr (hbound.mono (fun ω hω t => hω t.toNNReal)) hC
    (by simpa only [Real.toNNReal_coe, Real.toNNReal_zero] using htotal)
    ha hprim' hL hlin'
  simpa only [Real.toNNReal_coe, Real.toNNReal_zero, nnrealTimePrimitive] using h

end Problem367.NNRealArtanhFormula

end

end OAI
