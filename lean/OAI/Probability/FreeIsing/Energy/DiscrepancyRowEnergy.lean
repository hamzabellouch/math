import OAI.Probability.FreeIsing.Energy.DiscrepancyEnergy

namespace OAI

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace Problem367.DiscrepancyEnergy

theorem summable_sq_sub {ι : Type*} {c c' : ι → ℝ}
    (hc : Summable (fun i => (c i) ^ 2))
    (hc' : Summable (fun i => (c' i) ^ 2)) :
    Summable (fun i => (c i - c' i) ^ 2) := by
  apply Summable.of_nonneg_of_le (fun _ => sq_nonneg _) _ ((hc.add hc').mul_left 2)
  intro i
  nlinarith [sq_nonneg (c i + c' i)]

theorem tsum_sq_sub_le {ι : Type*} {c c' : ι → ℝ}
    (hc : Summable (fun i => (c i) ^ 2))
    (hc' : Summable (fun i => (c' i) ^ 2)) :
    (∑' i, (c i - c' i) ^ 2) ≤ 2 * ((∑' i, (c i) ^ 2) + ∑' i, (c' i) ^ 2) := by
  calc
    (∑' i, (c i - c' i) ^ 2) ≤ ∑' i, 2 * ((c i) ^ 2 + (c' i) ^ 2) := by
      exact Summable.tsum_le_tsum (fun i => by nlinarith [sq_nonneg (c i + c' i)])
        (summable_sq_sub hc hc') ((hc.add hc').mul_left 2)
    _ = _ := by rw [tsum_mul_left, hc.tsum_add hc']

theorem abs_noise_add_drift_le
    {R X m m' A A' H : ℝ} (hR : 0 ≤ R) (hA : 0 ≤ A) (hA' : 0 ≤ A')
    (hnoise : R ≤ 2 * (A + A')) (hX : |X| ≤ H)
    (hm : |m| ≤ 1) (hm' : |m'| ≤ 1) :
    |R + 2 * X * (m * A - m' * A')| ≤ (2 + 2 * H) * (A + A') := by
  have hH : 0 ≤ H := (abs_nonneg X).trans hX
  have hd : |m * A - m' * A'| ≤ A + A' := by
    calc
      |m * A - m' * A'| ≤ |m * A| + |m' * A'| := abs_sub _ _
      _ = |m| * A + |m'| * A' := by rw [abs_mul, abs_mul, abs_of_nonneg hA,
        abs_of_nonneg hA']
      _ ≤ A + A' := by nlinarith
  calc
    |R + 2 * X * (m * A - m' * A')| ≤ |R| + |2 * X * (m * A - m' * A')| :=
      abs_add_le _ _
    _ = R + 2 * |X| * |m * A - m' * A'| := by
      rw [abs_of_nonneg hR, abs_mul, abs_mul]
      norm_num
    _ ≤ R + 2 * H * (A + A') := by gcongr
    _ ≤ (2 + 2 * H) * (A + A') := by nlinarith

theorem integrable_sq_difference_row
    {Ω ι : Type*} [MeasurableSpace Ω] [Countable ι] {μ : Measure Ω}
    {c c' : ι → Ω → ℝ}
    (hc : ∀ i, AEStronglyMeasurable (c i) μ)
    (hc' : ∀ i, AEStronglyMeasurable (c' i) μ)
    (hA : Integrable (fun ω => ∑' i, (c i ω) ^ 2) μ)
    (hA' : Integrable (fun ω => ∑' i, (c' i ω) ^ 2) μ)
    (hsum : ∀ᵐ ω ∂μ, Summable (fun i => (c i ω) ^ 2) ∧
      Summable (fun i => (c' i ω) ^ 2)) :
    Integrable (fun ω => ∑' i, (c i ω - c' i ω) ^ 2) μ := by
  apply ((hA.add hA').const_mul 2).mono'
    (AEStronglyMeasurable.tsum (fun i => ((hc i).sub (hc' i)).pow 2))
  filter_upwards [hsum] with ω hω
  rw [Real.norm_eq_abs, abs_of_nonneg (tsum_nonneg (fun _ => sq_nonneg _))]
  exact tsum_sq_sub_le hω.1 hω.2

theorem integrable_noise_add_drift
    {Ω ι : Type*} [MeasurableSpace Ω] [Countable ι] {μ : Measure Ω}
    {c c' : ι → Ω → ℝ} {X m m' : Ω → ℝ} {H : ℝ}
    (hc : ∀ i, AEStronglyMeasurable (c i) μ)
    (hc' : ∀ i, AEStronglyMeasurable (c' i) μ)
    (hXm : AEStronglyMeasurable X μ)
    (hm : AEStronglyMeasurable m μ) (hm' : AEStronglyMeasurable m' μ)
    (hA : Integrable (fun ω => ∑' i, (c i ω) ^ 2) μ)
    (hA' : Integrable (fun ω => ∑' i, (c' i ω) ^ 2) μ)
    (hsum : ∀ᵐ ω ∂μ, Summable (fun i => (c i ω) ^ 2) ∧
      Summable (fun i => (c' i ω) ^ 2))
    (hbound : ∀ᵐ ω ∂μ, |X ω| ≤ H ∧ |m ω| ≤ 1 ∧ |m' ω| ≤ 1) :
    Integrable (fun ω => (∑' i, (c i ω - c' i ω) ^ 2) +
      2 * X ω * (m ω * (∑' i, (c i ω) ^ 2) - m' ω * (∑' i, (c' i ω) ^ 2))) μ := by
  have hn := integrable_sq_difference_row hc hc' hA hA' hsum
  have hmeas := hn.aestronglyMeasurable.add
    ((hXm.const_mul 2).mul
      ((hm.mul hA.aestronglyMeasurable).sub (hm'.mul hA'.aestronglyMeasurable)))
  apply ((hA.add hA').const_mul (2 + 2 * H)).mono' hmeas
  filter_upwards [hsum, hbound] with ω hsumω hb
  rw [Real.norm_eq_abs]
  exact abs_noise_add_drift_le (tsum_nonneg (fun _ => sq_nonneg _))
    (tsum_nonneg (fun _ => sq_nonneg _)) (tsum_nonneg (fun _ => sq_nonneg _))
    (tsum_sq_sub_le hsumω.1 hsumω.2) hb.1 hb.2.1 hb.2.2

theorem hasSum_integral_sq_row
    {Ω ι : Type*} [MeasurableSpace Ω] [Countable ι] {μ : Measure Ω}
    {c : ι → Ω → ℝ} (hc : ∀ i, AEStronglyMeasurable (c i) μ)
    (hsum : ∀ᵐ ω ∂μ, Summable (fun i => (c i ω) ^ 2))
    (hA : Integrable (fun ω => ∑' i, (c i ω) ^ 2) μ) :
    HasSum (fun i => ∫ ω, (c i ω) ^ 2 ∂μ) (∫ ω, (∑' i, (c i ω) ^ 2) ∂μ) := by
  refine hasSum_integral_of_dominated_convergence (fun i ω => (c i ω) ^ 2)
    (fun i => (hc i).pow 2) ?_ hsum hA ?_
  · intro i
    filter_upwards with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  · filter_upwards [hsum] with ω hω
    exact hω.hasSum

theorem integral_noise_add_drift
    {Ω ι : Type*} [MeasurableSpace Ω] [Countable ι] {μ : Measure Ω}
    {c c' : ι → Ω → ℝ} {X m m' : Ω → ℝ} {H : ℝ}
    (hc : ∀ i, AEStronglyMeasurable (c i) μ)
    (hc' : ∀ i, AEStronglyMeasurable (c' i) μ)
    (hXm : AEStronglyMeasurable X μ)
    (hm : AEStronglyMeasurable m μ) (hm' : AEStronglyMeasurable m' μ)
    (hA : Integrable (fun ω => ∑' i, (c i ω) ^ 2) μ)
    (hA' : Integrable (fun ω => ∑' i, (c' i ω) ^ 2) μ)
    (hsum : ∀ᵐ ω ∂μ, Summable (fun i => (c i ω) ^ 2) ∧
      Summable (fun i => (c' i ω) ^ 2))
    (hbound : ∀ᵐ ω ∂μ, |X ω| ≤ H ∧ |m ω| ≤ 1 ∧ |m' ω| ≤ 1) :
    (∫ ω, (∑' i, (c i ω - c' i ω) ^ 2) +
      2 * X ω * (m ω * (∑' i, (c i ω) ^ 2) - m' ω * (∑' i, (c' i ω) ^ 2)) ∂μ) =
      (∑' i, ∫ ω, (c i ω - c' i ω) ^ 2 ∂μ) +
        2 * ∫ ω, X ω * (m ω * (∑' i, (c i ω) ^ 2) -
          m' ω * (∑' i, (c' i ω) ^ 2)) ∂μ := by
  have hn := integrable_sq_difference_row hc hc' hA hA' hsum
  have hE := integrable_noise_add_drift hc hc' hXm hm hm' hA hA' hsum hbound
  have hd : Integrable (fun ω => 2 * X ω *
      (m ω * (∑' i, (c i ω) ^ 2) - m' ω * (∑' i, (c' i ω) ^ 2))) μ := by
    apply (hE.sub hn).congr
    filter_upwards with ω
    simp only [Pi.sub_apply]
    ring
  have hs := hasSum_integral_sq_row (fun i => (hc i).sub (hc' i))
    (hsum.mono (fun ω hω => summable_sq_sub hω.1 hω.2)) hn
  simp only [Pi.sub_apply] at hs
  rw [integral_add hn hd, ← hs.tsum_eq]
  congr 1
  simp only [mul_assoc, integral_const_mul]

theorem sq_row_integrable_of_summable_integrals
    {Ω ι : Type*} [MeasurableSpace Ω] [Countable ι] {μ : Measure Ω}
    {c : ι → Ω → ℝ}
    (hc : ∀ i, Integrable (fun ω => (c i ω) ^ 2) μ)
    (hs : Summable (fun i => ∫ ω, (c i ω) ^ 2 ∂μ)) :
    (∀ᵐ ω ∂μ, Summable (fun i => (c i ω) ^ 2)) ∧
      Integrable (fun ω => ∑' i, (c i ω) ^ 2) μ := by
  have hm (i : ι) : AEMeasurable (fun ω => ENNReal.ofReal ((c i ω) ^ 2)) μ :=
    (hc i).aestronglyMeasurable.aemeasurable.ennreal_ofReal
  have hfin : (∫⁻ ω, ∑' i, ENNReal.ofReal ((c i ω) ^ 2) ∂μ) < ∞ := by
    rw [lintegral_tsum hm]
    calc
      (∑' i, ∫⁻ ω, ENNReal.ofReal ((c i ω) ^ 2) ∂μ) =
          ∑' i, ENNReal.ofReal (∫ ω, (c i ω) ^ 2 ∂μ) := by
        apply tsum_congr
        intro i
        exact (ofReal_integral_eq_lintegral_ofReal (hc i)
          (Eventually.of_forall (fun ω => sq_nonneg (c i ω)))).symm
      _ < ∞ := hs.tsum_ofReal_lt_top
  have hAe : ∀ᵐ ω ∂μ, Summable (fun i => (c i ω) ^ 2) := by
    filter_upwards [ae_lt_top' (AEMeasurable.tsum hm) hfin.ne] with ω hω
    simpa only [ENNReal.toReal_ofReal (sq_nonneg _)] using
      ENNReal.summable_toReal hω.ne
  refine ⟨hAe, ?_⟩
  have hI := integrable_toReal_of_lintegral_ne_top (AEMeasurable.tsum hm) hfin.ne
  simpa only [ENNReal.tsum_toReal_eq (fun i => ENNReal.ofReal_ne_top),
    ENNReal.toReal_ofReal (sq_nonneg _)] using hI

def density {Ω ι : Type*} (c c' : ι → Ω → ℝ) (X m m' : Ω → ℝ) (ω : Ω) : ℝ :=
  (∑' i, (c i ω - c' i ω) ^ 2) +
    2 * X ω * (m ω * (∑' i, (c i ω) ^ 2) - m' ω * (∑' i, (c' i ω) ^ 2))

theorem secondMoment_row_analysis_of_martingale
    {Ω ι : Type*} [mΩ : MeasurableSpace Ω] [Countable ι]
    {μ : Measure Ω} [IsFiniteMeasure μ] {F : Filtration ℝ mΩ}
    {c c' : ι → ℝ → Ω → ℝ} {X M m m' : ℝ → Ω → ℝ} {H T : ℝ}
    (hT : 0 ≤ T) (hX0 : Integrable (fun ω => (X 0 ω) ^ 2) μ)
    (hM : Martingale M F μ) (hM0 : M 0 =ᵐ[μ] fun _ => 0)
    (hc : ∀ i, AEStronglyMeasurable (fun p : ℝ × Ω => c i p.1 p.2)
      ((volume.restrict (Ioc 0 T)).prod μ))
    (hc' : ∀ i, AEStronglyMeasurable (fun p : ℝ × Ω => c' i p.1 p.2)
      ((volume.restrict (Ioc 0 T)).prod μ))
    (hXm : AEStronglyMeasurable (fun p : ℝ × Ω => X p.1 p.2)
      ((volume.restrict (Ioc 0 T)).prod μ))
    (hm : AEStronglyMeasurable (fun p : ℝ × Ω => m p.1 p.2)
      ((volume.restrict (Ioc 0 T)).prod μ))
    (hm' : AEStronglyMeasurable (fun p : ℝ × Ω => m' p.1 p.2)
      ((volume.restrict (Ioc 0 T)).prod μ))
    (hA : Integrable (fun p : ℝ × Ω => ∑' i, (c i p.1 p.2) ^ 2)
      ((volume.restrict (Ioc 0 T)).prod μ))
    (hA' : Integrable (fun p : ℝ × Ω => ∑' i, (c' i p.1 p.2) ^ 2)
      ((volume.restrict (Ioc 0 T)).prod μ))
    (hsum : ∀ᵐ p ∂(volume.restrict (Ioc 0 T)).prod μ,
      Summable (fun i => (c i p.1 p.2) ^ 2) ∧
      Summable (fun i => (c' i p.1 p.2) ^ 2))
    (hbound : ∀ᵐ p ∂(volume.restrict (Ioc 0 T)).prod μ,
      |X p.1 p.2| ≤ H ∧ |m p.1 p.2| ≤ 1 ∧ |m' p.1 p.2| ≤ 1)
    (hdecomp : ∀ t ∈ Icc 0 T, ∀ᵐ ω ∂μ,
      (X t ω) ^ 2 = (X 0 ω) ^ 2 + M t ω +
        ∫ s in (0 : ℝ)..t, density (fun i => c i s) (fun i => c' i s)
          (X s) (m s) (m' s) ω) :
    AbsolutelyContinuousOnInterval (fun t => ∫ ω, (X t ω) ^ 2 ∂μ) 0 T ∧
      (∀ᵐ t ∂volume.restrict (Icc 0 T),
        deriv (fun s => ∫ ω, (X s ω) ^ 2 ∂μ) t =
          (∑' i, ∫ ω, (c i t ω - c' i t ω) ^ 2 ∂μ) +
            2 * ∫ ω, X t ω * (m t ω * (∑' i, (c i t ω) ^ 2) -
              m' t ω * (∑' i, (c' i t ω) ^ 2)) ∂μ) := by
  have hE : Integrable (fun p : ℝ × Ω =>
      density (fun i => c i p.1) (fun i => c' i p.1)
        (X p.1) (m p.1) (m' p.1) p.2)
      ((volume.restrict (Ioc 0 T)).prod μ) :=
    integrable_noise_add_drift hc hc' hXm hm hm' hA hA' hsum hbound
  obtain ⟨hac, hd⟩ := secondMoment_analysis_of_martingale hT hX0 hM hM0 hE hdecomp
  refine ⟨hac, ?_⟩
  rw [← restrict_Ioc_eq_restrict_Icc] at hd ⊢
  have hcs := ae_all_iff.mpr (fun i => (hc i).prodMk_left)
  have hcs' := ae_all_iff.mpr (fun i => (hc' i).prodMk_left)
  filter_upwards [hd, hcs, hcs', hXm.prodMk_left, hm.prodMk_left, hm'.prodMk_left,
    hA.prod_right_ae, hA'.prod_right_ae, Measure.ae_ae_of_ae_prod hsum,
    Measure.ae_ae_of_ae_prod hbound] with t hdt hct hct' hXt hmt hmt' hAt hAt' hst hbt
  exact hdt.trans (integral_noise_add_drift hct hct' hXt hmt hmt' hAt hAt' hst hbt)

end Problem367.DiscrepancyEnergy

end

end OAI
