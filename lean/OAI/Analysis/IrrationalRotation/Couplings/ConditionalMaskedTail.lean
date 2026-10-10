import OAI.Analysis.IrrationalRotation.Analysis.MaskedCauchySchwarz
import OAI.Analysis.IrrationalRotation.Analysis.MaskedTail

namespace OAI

open MeasureTheory
open scoped ENNReal

namespace InvariantProjection

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}

theorem lintegral_tsum_masked_mul_le_of_condExp
    {ι : Type*} [mι : MeasurableSpace ι] [MeasurableSingletonClass ι] [Countable ι]
    [IsFiniteMeasure μ]
    {a b : Ω × ι → ℝ} (ha : Measurable a) (hb : Measurable b)
    (ha_nonneg : ∀ z, 0 ≤ a z) (hb_nonneg : ∀ z, 0 ≤ b z)
    {H : Set (Ω × ι)} (hH : MeasurableSet H)
    {m : MeasurableSpace Ω} (hm : m ≤ mΩ) {δ : ℝ} (hδ : 0 ≤ δ)
    (ha_endpoint : ∀ i, StronglyMeasurable[m] (fun ω => a (ω, i) ^ 2))
    (hcond : ∀ i, μ[({ω | (ω, i) ∈ H}).indicator (fun _ => (1 : ℝ)) | m]
      ≤ᵐ[μ] fun _ => δ)
    (ha_energy : (∫⁻ ω, ∑' i, ENNReal.ofReal (a (ω, i) ^ 2) ∂μ) ≤ 1)
    (hb_energy : (∫⁻ ω, ∑' i, ENNReal.ofReal (b (ω, i) ^ 2) ∂μ) ≤ 1) :
    (∫⁻ ω, ∑' i, H.indicator
      (fun z => ENNReal.ofReal (a z) * ENNReal.ofReal (b z)) (ω, i) ∂μ) ≤
      ENNReal.ofReal (Real.sqrt δ) := by
  have ha_sq_int : ∀ i, Integrable (fun ω => a (ω, i) ^ 2) μ := by
    intro i
    refine ⟨((ha.comp (@measurable_prodMk_right Ω ι mΩ mι i)).pow_const 2).aestronglyMeasurable, ?_⟩
    apply (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun _ => sq_nonneg _)).2
    calc
      (∫⁻ ω, ENNReal.ofReal (a (ω, i) ^ 2) ∂μ) ≤
          ∫⁻ ω, ∑' j, ENNReal.ofReal (a (ω, j) ^ 2) ∂μ :=
        lintegral_mono fun ω => ENNReal.le_tsum (f := fun j => ENNReal.ofReal (a (ω, j) ^ 2)) i
      _ ≤ 1 := ha_energy
      _ < ⊤ := by simp
  have hs : ∀ i, MeasurableSet[mΩ] {ω | (ω, i) ∈ H} := fun i =>
    hH.preimage (@measurable_prodMk_right Ω ι mΩ mι i)
  have hsmall := lintegral_tsum_indicator_le_of_condExp_indicator_le_of_energy_le_one
    (mΩ := mΩ) hm hs hδ ha_sq_int ha_endpoint
    (fun _ => Filter.Eventually.of_forall fun _ => sq_nonneg _) hcond ha_energy
  have hmasked : (∫⁻ ω, ∑' i, H.indicator
      (fun z => ENNReal.ofReal (a z) ^ (2 : ℕ)) (ω, i) ∂μ) ≤ ENNReal.ofReal δ := by
    convert hsmall using 1
    apply lintegral_congr
    intro ω
    apply tsum_congr
    intro i
    by_cases hi : (ω, i) ∈ H
    · simp [hi, ENNReal.ofReal_pow (ha_nonneg (ω, i))]
    · simp [hi]
  have hb2 : (∫⁻ ω, ∑' i, ENNReal.ofReal (b (ω, i)) ^ (2 : ℕ) ∂μ) ≤ 1 := by
    simpa only [← ENNReal.ofReal_pow (hb_nonneg _)] using hb_energy
  let : MeasurableSpace Ω := mΩ
  have hcs := Invariant233.MaskedTail.lintegral_tsum_indicator_mul_le_sqrt
    (μ := μ) hH ha.ennreal_ofReal.aemeasurable hb.ennreal_ofReal.aemeasurable hmasked hb2
  simpa only [ENNReal.ofReal_rpow_of_nonneg hδ (by norm_num : (0 : ℝ) ≤ 1 / 2),
    ← Real.sqrt_eq_rpow] using hcs

end InvariantProjection

end OAI
