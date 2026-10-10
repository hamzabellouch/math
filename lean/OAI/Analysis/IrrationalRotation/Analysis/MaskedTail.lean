import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Function.ConditionalLExpectation
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic

namespace OAI

open MeasureTheory
open scoped ENNReal

namespace Invariant233.MaskedTail

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}

theorem lintegral_mul_le_sqrt
    {a b : Ω → ℝ≥0∞} {δ : ℝ≥0∞}
    (ha : AEMeasurable a μ) (hb : AEMeasurable b μ)
    (ha2 : (∫⁻ ω, a ω ^ (2 : ℕ) ∂μ) ≤ δ)
    (hb2 : (∫⁻ ω, b ω ^ (2 : ℕ) ∂μ) ≤ 1) :
    (∫⁻ ω, a ω * b ω ∂μ) ≤ δ ^ (1 / 2 : ℝ) := by
  have hconj : (2 : ℝ).HolderConjugate 2 := by
    rw [Real.holderConjugate_iff]
    norm_num
  have hcs := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hconj ha hb
  simp only [Pi.mul_apply, ENNReal.rpow_two] at hcs
  calc
    (∫⁻ ω, a ω * b ω ∂μ) ≤
        (∫⁻ ω, a ω ^ (2 : ℕ) ∂μ) ^ (1 / 2 : ℝ) *
          (∫⁻ ω, b ω ^ (2 : ℕ) ∂μ) ^ (1 / 2 : ℝ) := hcs
    _ ≤ δ ^ (1 / 2 : ℝ) * (1 : ℝ≥0∞) ^ (1 / 2 : ℝ) :=
      mul_le_mul' (ENNReal.rpow_le_rpow ha2 (by norm_num))
        (ENNReal.rpow_le_rpow hb2 (by norm_num))
    _ = δ ^ (1 / 2 : ℝ) := by simp

theorem lintegral_indicator_mul_le_sqrt
    {a b : Ω → ℝ≥0∞} {δ : ℝ≥0∞} {H : Set Ω}
    (hH : MeasurableSet H)
    (ha : AEMeasurable a μ) (hb : AEMeasurable b μ)
    (ha2 : (∫⁻ ω, H.indicator (fun ω => a ω ^ (2 : ℕ)) ω ∂μ) ≤ δ)
    (hb2 : (∫⁻ ω, b ω ^ (2 : ℕ) ∂μ) ≤ 1) :
    (∫⁻ ω, H.indicator (fun ω => a ω * b ω) ω ∂μ) ≤
      δ ^ (1 / 2 : ℝ) := by
  have hpow : (fun ω => (H.indicator a ω) ^ (2 : ℕ)) =
      H.indicator (fun ω => a ω ^ (2 : ℕ)) := by
    funext ω
    by_cases hω : ω ∈ H <;> simp [hω]
  have hmul : (fun ω => H.indicator a ω * b ω) =
      H.indicator (fun ω => a ω * b ω) := by
    funext ω
    by_cases hω : ω ∈ H <;> simp [hω]
  have h := lintegral_mul_le_sqrt (ha.indicator hH) hb (by simpa [hpow] using ha2) hb2
  simpa [hmul] using h

theorem lintegral_tsum_indicator_mul_le_sqrt
    {ι : Type*} [MeasurableSpace ι] [MeasurableSingletonClass ι] [Countable ι]
    {a b : Ω × ι → ℝ≥0∞} {δ : ℝ≥0∞} {H : Set (Ω × ι)}
    (hH : MeasurableSet H)
    (ha : AEMeasurable a (μ.prod Measure.count))
    (hb : AEMeasurable b (μ.prod Measure.count))
    (ha2 : (∫⁻ ω, ∑' i, H.indicator (fun z => a z ^ (2 : ℕ)) (ω, i) ∂μ) ≤ δ)
    (hb2 : (∫⁻ ω, ∑' i, b (ω, i) ^ (2 : ℕ) ∂μ) ≤ 1) :
    (∫⁻ ω, ∑' i, H.indicator (fun z => a z * b z) (ω, i) ∂μ) ≤
      δ ^ (1 / 2 : ℝ) := by
  have ha2' : (∫⁻ z, H.indicator (fun z => a z ^ (2 : ℕ)) z
      ∂μ.prod Measure.count) ≤ δ := by
    rw [lintegral_prod _ ((ha.pow_const 2).indicator hH)]
    simpa only [lintegral_count] using ha2
  have hb2' : (∫⁻ z, b z ^ (2 : ℕ) ∂μ.prod Measure.count) ≤ 1 := by
    rw [lintegral_prod _ (hb.pow_const 2)]
    simpa only [lintegral_count] using hb2
  have h := lintegral_indicator_mul_le_sqrt hH ha hb ha2' hb2'
  change (∫⁻ z, H.indicator (a * b) z ∂μ.prod Measure.count) ≤ _ at h
  rw [lintegral_prod _ ((ha.mul hb).indicator hH)] at h
  simpa only [lintegral_count, Pi.mul_def] using h

theorem lintegral_tsum_indicator_mul_le_sqrt_right
    {ι : Type*} [MeasurableSpace ι] [MeasurableSingletonClass ι] [Countable ι]
    {a b : Ω × ι → ℝ≥0∞} {δ : ℝ≥0∞} {H : Set (Ω × ι)}
    (hH : MeasurableSet H)
    (ha : AEMeasurable a (μ.prod Measure.count))
    (hb : AEMeasurable b (μ.prod Measure.count))
    (ha2 : (∫⁻ ω, ∑' i, a (ω, i) ^ (2 : ℕ) ∂μ) ≤ 1)
    (hb2 : (∫⁻ ω, ∑' i, H.indicator (fun z => b z ^ (2 : ℕ)) (ω, i) ∂μ) ≤ δ) :
    (∫⁻ ω, ∑' i, H.indicator (fun z => a z * b z) (ω, i) ∂μ) ≤
      δ ^ (1 / 2 : ℝ) := by
  simpa only [mul_comm] using
    lintegral_tsum_indicator_mul_le_sqrt hH hb ha hb2 ha2

theorem lintegral_mul_le_of_condLExp_le
    {m : MeasurableSpace Ω} (hm : m ≤ mΩ)
    [SigmaFinite (μ.trim hm)] {a h : Ω → ℝ≥0∞} {δ : ℝ≥0∞}
    (ha : Measurable[m] a) (hh : Measurable[mΩ] h)
    (hcond : ∀ᵐ ω ∂μ, condLExp m μ h ω ≤ δ) :
    (∫⁻ ω, h ω * a ω ∂μ) ≤ δ * ∫⁻ ω, a ω ∂μ := by
  have hmeasure : (μ.withDensity h).trim hm ≤ δ • μ.trim hm := by
    apply Measure.le_iff.mpr
    intro s hs
    rw [trim_measurableSet_eq hm hs, Measure.smul_apply,
      trim_measurableSet_eq hm hs, withDensity_apply _ (hm s hs)]
    rw [← setLIntegral_condLExp hm μ h hs]
    calc
      (∫⁻ ω in s, condLExp m μ h ω ∂μ) ≤ ∫⁻ _ in s, δ ∂μ :=
        lintegral_mono_ae (ae_restrict_of_ae hcond)
      _ = δ * μ s := by simp
  have haFull : Measurable[mΩ] a := ha.mono hm le_rfl
  calc
    (∫⁻ ω, h ω * a ω ∂μ) = ∫⁻ ω, a ω ∂μ.withDensity h := by
      simpa only [Pi.mul_apply] using
        (lintegral_withDensity_eq_lintegral_mul μ hh haFull).symm
    _ = ∫⁻ ω, a ω ∂(μ.withDensity h).trim hm := (lintegral_trim hm ha).symm
    _ ≤ ∫⁻ ω, a ω ∂δ • μ.trim hm := lintegral_mono' hmeasure le_rfl
    _ = δ * ∫⁻ ω, a ω ∂μ := by rw [lintegral_smul_measure, lintegral_trim hm ha]; rfl

theorem lintegral_tsum_ofReal_indicator_mul_le_sqrt
    {ι : Type*} [MeasurableSpace ι] [MeasurableSingletonClass ι] [Countable ι]
    {a b : ι → Ω → ℝ} {H : ι → Set Ω} {δ : ℝ}
    (ha : ∀ i, Measurable (a i)) (hb : ∀ i, Measurable (b i))
    (hH : ∀ i, MeasurableSet (H i))
    (ha_nonneg : ∀ i ω, 0 ≤ a i ω) (hb_nonneg : ∀ i ω, 0 ≤ b i ω)
    (hδ : 0 ≤ δ)
    (ha2 : (∫⁻ ω, ∑' i, ENNReal.ofReal ((H i).indicator
      (fun ω => a i ω ^ (2 : ℕ)) ω) ∂μ) ≤ ENNReal.ofReal δ)
    (hb2 : (∫⁻ ω, ∑' i, ENNReal.ofReal (b i ω ^ (2 : ℕ)) ∂μ) ≤ 1) :
    (∫⁻ ω, ∑' i, ENNReal.ofReal ((H i).indicator
      (fun ω => a i ω * b i ω) ω) ∂μ) ≤ ENNReal.ofReal (Real.sqrt δ) := by
  let A : Ω × ι → ℝ≥0∞ := fun z => ENNReal.ofReal ((H z.2).indicator (a z.2) z.1)
  let B : Ω × ι → ℝ≥0∞ := fun z => ENNReal.ofReal (b z.2 z.1)
  have hA : Measurable A := measurable_from_prod_countable_left fun i =>
    ((ha i).indicator (hH i)).ennreal_ofReal
  have hB : Measurable B := measurable_from_prod_countable_left fun i =>
    (hb i).ennreal_ofReal
  have hA2 : ∀ z : Ω × ι, A z ^ (2 : ℕ) =
      ENNReal.ofReal ((H z.2).indicator (fun ω => a z.2 ω ^ (2 : ℕ)) z.1) := by
    intro z
    by_cases hz : z.1 ∈ H z.2
    · simp [A, hz, ENNReal.ofReal_pow (ha_nonneg z.2 z.1)]
    · simp [A, hz]
  have hB2 : ∀ z : Ω × ι, B z ^ (2 : ℕ) =
      ENNReal.ofReal (b z.2 z.1 ^ (2 : ℕ)) := by
    intro z
    exact (ENNReal.ofReal_pow (hb_nonneg z.2 z.1) 2).symm
  have hAB : ∀ z : Ω × ι, A z * B z =
      ENNReal.ofReal ((H z.2).indicator (fun ω => a z.2 ω * b z.2 ω) z.1) := by
    intro z
    by_cases hz : z.1 ∈ H z.2
    · simp [A, B, hz, ENNReal.ofReal_mul (ha_nonneg z.2 z.1)]
    · simp [A, B, hz]
  have hA2' : (∫⁻ z, A z ^ (2 : ℕ) ∂μ.prod Measure.count) ≤ ENNReal.ofReal δ := by
    rw [lintegral_prod _ (hA.pow_const 2).aemeasurable]
    simpa only [lintegral_count, hA2] using ha2
  have hB2' : (∫⁻ z, B z ^ (2 : ℕ) ∂μ.prod Measure.count) ≤ 1 := by
    rw [lintegral_prod _ (hB.pow_const 2).aemeasurable]
    simpa only [lintegral_count, hB2] using hb2
  have h := lintegral_mul_le_sqrt hA.aemeasurable hB.aemeasurable hA2' hB2'
  change (∫⁻ z, (A * B) z ∂μ.prod Measure.count) ≤ _ at h
  rw [lintegral_prod _ (hA.mul hB).aemeasurable] at h
  simp only [lintegral_count, Pi.mul_apply, hAB] at h
  rw [Real.sqrt_eq_rpow, ← ENNReal.ofReal_rpow_of_nonneg hδ (by norm_num)]
  exact h

theorem real_tsum_integrable_of_lintegral_bound
    {ι : Type*} [Countable ι] {f : ι → Ω → ℝ} {C : ℝ}
    (hf : ∀ i, Measurable (f i)) (hf_nonneg : ∀ i ω, 0 ≤ f i ω)
    (hC : 0 ≤ C)
    (hbound : (∫⁻ ω, ∑' i, ENNReal.ofReal (f i ω) ∂μ) ≤ ENNReal.ofReal C) :
    (∀ᵐ ω ∂μ, Summable (fun i => f i ω)) ∧
      Integrable (fun ω => ∑' i, f i ω) μ ∧
      (∫ ω, ∑' i, f i ω ∂μ) ≤ C := by
  have hsum_meas : Measurable (fun ω => ∑' i, ENNReal.ofReal (f i ω)) :=
    Measurable.tsum fun i => (hf i).ennreal_ofReal
  have hfinite : (∫⁻ ω, ∑' i, ENNReal.ofReal (f i ω) ∂μ) ≠ ⊤ :=
    (hbound.trans_lt ENNReal.ofReal_lt_top).ne
  have hsummable : ∀ᵐ ω ∂μ, Summable (fun i => f i ω) := by
    filter_upwards [ae_lt_top hsum_meas hfinite] with ω hω
    have h := ENNReal.summable_toReal hω.ne
    simpa only [ENNReal.toReal_ofReal (hf_nonneg _ _)] using h
  have hpoint : ∀ ω, ENNReal.ofReal (∑' i, f i ω) ≤ ∑' i, ENNReal.ofReal (f i ω) := by
    intro ω
    by_cases h : Summable (fun i => f i ω)
    · exact (ENNReal.ofReal_tsum_of_nonneg (fun i => hf_nonneg i ω) h).le
    · simp [tsum_eq_zero_of_not_summable h]
  have hlin : (∫⁻ ω, ENNReal.ofReal (∑' i, f i ω) ∂μ) ≤ ENNReal.ofReal C :=
    (lintegral_mono hpoint).trans hbound
  have hmeas : Measurable (fun ω => ∑' i, f i ω) := Measurable.tsum hf
  have hnonneg : ∀ᵐ ω ∂μ, 0 ≤ ∑' i, f i ω :=
    Filter.Eventually.of_forall fun ω => tsum_nonneg (fun i => hf_nonneg i ω)
  have hint : Integrable (fun ω => ∑' i, f i ω) μ :=
    ⟨hmeas.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal hnonneg).2
      (hlin.trans_lt ENNReal.ofReal_lt_top)⟩
  refine ⟨hsummable, hint, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae hnonneg hmeas.aestronglyMeasurable]
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hlin).trans_eq (ENNReal.toReal_ofReal hC)

theorem integral_tsum_indicator_mul_le_sqrt
    {ι : Type*} [MeasurableSpace ι] [MeasurableSingletonClass ι] [Countable ι]
    {a b : ι → Ω → ℝ} {H : ι → Set Ω} {δ : ℝ}
    (ha : ∀ i, Measurable (a i)) (hb : ∀ i, Measurable (b i))
    (hH : ∀ i, MeasurableSet (H i))
    (ha_nonneg : ∀ i ω, 0 ≤ a i ω) (hb_nonneg : ∀ i ω, 0 ≤ b i ω)
    (hδ : 0 ≤ δ)
    (ha2 : (∫⁻ ω, ∑' i, ENNReal.ofReal ((H i).indicator
      (fun ω => a i ω ^ (2 : ℕ)) ω) ∂μ) ≤ ENNReal.ofReal δ)
    (hb2 : (∫⁻ ω, ∑' i, ENNReal.ofReal (b i ω ^ (2 : ℕ)) ∂μ) ≤ 1) :
    (∀ᵐ ω ∂μ, Summable (fun i => (H i).indicator (fun ω => a i ω * b i ω) ω)) ∧
      Integrable (fun ω => ∑' i, (H i).indicator (fun ω => a i ω * b i ω) ω) μ ∧
      (∫ ω, ∑' i, (H i).indicator (fun ω => a i ω * b i ω) ω ∂μ) ≤ Real.sqrt δ := by
  apply real_tsum_integrable_of_lintegral_bound
    (fun i => ((ha i).mul (hb i)).indicator (hH i))
    (fun i ω => Set.indicator_nonneg (fun ω _ => mul_nonneg (ha_nonneg i ω)
      (hb_nonneg i ω)) ω)
    (Real.sqrt_nonneg δ)
  exact lintegral_tsum_ofReal_indicator_mul_le_sqrt ha hb hH ha_nonneg hb_nonneg hδ ha2 hb2

end Invariant233.MaskedTail

end OAI
