import OAI.Probability.FreeIsing.Martingales.DriftEnergy

namespace OAI

noncomputable section
open MeasureTheory Set

namespace Problem367.MartingaleDriftEnergy

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}

theorem stronglyMeasurable_timePrimitive {b : ℝ → Ω → ℝ}
    (hb : StronglyMeasurable (fun p : ℝ × Ω => b p.1 p.2)) :
    StronglyMeasurable (fun p : ℝ × Ω => ∫ s in (0 : ℝ)..p.1, b s p.2) := by
  have hf : StronglyMeasurable (fun p : (ℝ × Ω) × ℝ => b p.2 p.1.2) :=
    hb.comp_measurable (measurable_snd.prodMk (measurable_snd.comp measurable_fst))
  have hpos : MeasurableSet {p : (ℝ × Ω) × ℝ | 0 < p.2 ∧ p.2 ≤ p.1.1} :=
    (measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_le measurable_snd (measurable_fst.comp measurable_fst))
  have hneg : MeasurableSet {p : (ℝ × Ω) × ℝ | p.1.1 < p.2 ∧ p.2 ≤ 0} :=
    (measurableSet_lt (measurable_fst.comp measurable_fst) measurable_snd).inter
      (measurableSet_le measurable_snd measurable_const)
  have hp := (hf.indicator hpos).integral_prod_right' (ν := volume)
  have hn := (hf.indicator hneg).integral_prod_right' (ν := volume)
  convert hp.sub hn using 1
  funext p
  simp only [intervalIntegral]
  congr 1 <;> symm
  · simpa only [Set.indicator, Set.mem_ofPred_eq, Set.mem_Ioc] using
      (integral_indicator (μ := volume) (f := fun s => b s p.2)
        (s := Ioc 0 p.1) measurableSet_Ioc)
  · simpa only [Set.indicator, Set.mem_ofPred_eq, Set.mem_Ioc] using
      (integral_indicator (μ := volume) (f := fun s => b s p.2)
        (s := Ioc p.1 0) measurableSet_Ioc)

theorem ae_timePrimitive_bound_of_totalVariation [SFinite μ]
    {b : ℝ → Ω → ℝ} {T D : ℝ} (hT : 0 ≤ T)
    (hbInt : Integrable (fun p : ℝ × Ω => b p.1 p.2)
      ((volume.restrict (Ioc 0 T)).prod μ))
    (hD : ∀ᵐ ω ∂μ, (∫ s in (0 : ℝ)..T, |b s ω|) ≤ D) :
    ∀ᵐ ω ∂μ, ∀ t ∈ Icc 0 T, |∫ s in (0 : ℝ)..t, b s ω| ≤ D := by
  filter_upwards [hbInt.prod_left_ae, hD] with ω hω hDω
  intro t ht
  rw [intervalIntegral.integral_of_le ht.1]
  rw [intervalIntegral.integral_of_le hT] at hDω
  calc
    |∫ s in Ioc 0 t, b s ω| ≤ ∫ s in Ioc 0 t, |b s ω| :=
      abs_integral_le_integral_abs
    _ ≤ ∫ s in Ioc 0 T, |b s ω| :=
      setIntegral_mono_set hω.abs
        (Filter.Eventually.of_forall (fun s => abs_nonneg (b s ω)))
        (Filter.Eventually.of_forall (fun _ hs => Ioc_subset_Ioc_right ht.2 hs))
    _ ≤ D := hDω

theorem ae_norm_martingale_le_of_bounded_process
    {M b : ℝ → Ω → ℝ} {T C D : ℝ} (hT : 0 ≤ T)
    (hX : ∀ᵐ ω ∂μ, |M T ω + ∫ s in (0 : ℝ)..T, b s ω| ≤ C)
    (hA : ∀ᵐ ω ∂μ, ∀ t ∈ Icc 0 T, |∫ s in (0 : ℝ)..t, b s ω| ≤ D) :
    ∀ᵐ ω ∂μ, ‖M T ω‖ ≤ C + D := by
  filter_upwards [hX, hA] with ω hω hAω
  have hAT := hAω T ⟨hT, le_rfl⟩
  rw [Real.norm_eq_abs]
  calc
    |M T ω| = |(M T ω + ∫ s in (0 : ℝ)..T, b s ω) -
        (∫ s in (0 : ℝ)..T, b s ω)| := by ring_nf
    _ ≤ |M T ω + ∫ s in (0 : ℝ)..T, b s ω| +
        |∫ s in (0 : ℝ)..T, b s ω| := abs_sub _ _
    _ ≤ C + D := add_le_add hω hAT

theorem mixed_integrability_of_bounded_process [IsFiniteMeasure μ]
    {ℱ : Filtration ℝ mΩ} {M b : ℝ → Ω → ℝ} {T C D : ℝ} (hT : 0 ≤ T)
    (hM : Martingale M ℱ μ)
    (hbMeas : StronglyMeasurable (fun p : ℝ × Ω => b p.1 p.2))
    (hbInt : Integrable (fun p : ℝ × Ω => b p.1 p.2)
      ((volume.restrict (Ioc 0 T)).prod μ))
    (hX : ∀ᵐ ω ∂μ, |M T ω + ∫ s in (0 : ℝ)..T, b s ω| ≤ C)
    (hA : ∀ᵐ ω ∂μ, ∀ t ∈ Icc 0 T, |∫ s in (0 : ℝ)..t, b s ω| ≤ D) :
    Integrable (fun p : ℝ × Ω => M T p.2 * b p.1 p.2)
      ((volume.restrict (Ioc 0 T)).prod μ) ∧
    Integrable (fun p : ℝ × Ω =>
      (∫ s in (0 : ℝ)..p.1, b s p.2) * b p.1 p.2)
      ((volume.restrict (Ioc 0 T)).prod μ) := by
  have hMt : StronglyMeasurable (M T) := (hM.stronglyAdapted T).mono (ℱ.le T)
  have hMb := ae_norm_martingale_le_of_bounded_process hT hX hA
  constructor
  · exact hbInt.bdd_mul hMt.comp_snd.aestronglyMeasurable
      (Measure.quasiMeasurePreserving_snd.ae hMb)
  · apply hbInt.bdd_mul (stronglyMeasurable_timePrimitive hbMeas).aestronglyMeasurable
    have hAp : ∀ᵐ p ∂((volume.restrict (Ioc 0 T)).prod μ),
        ∀ t ∈ Icc 0 T, |∫ s in (0 : ℝ)..t, b s p.2| ≤ D :=
      Measure.quasiMeasurePreserving_snd.ae hA
    have hmem : ∀ᵐ p ∂((volume.restrict (Ioc 0 T)).prod μ), p.1 ∈ Ioc 0 T :=
      Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Ioc)
    filter_upwards [hAp, hmem] with p hp hpt
    simpa only [Real.norm_eq_abs] using hp p.1 ⟨hpt.1.le, hpt.2⟩

theorem integral_sq_of_bounded_process [IsFiniteMeasure μ]
    {ℱ : Filtration ℝ mΩ} {M b : ℝ → Ω → ℝ} {T C D : ℝ} (hT : 0 ≤ T)
    (hM : Martingale M ℱ μ) (hb : StronglyAdapted ℱ b)
    (hbMeas : StronglyMeasurable (fun p : ℝ × Ω => b p.1 p.2))
    (hbInt : Integrable (fun p : ℝ × Ω => b p.1 p.2)
      ((volume.restrict (Ioc 0 T)).prod μ))
    (hmeas : AEStronglyMeasurable (fun p : ℝ × Ω => M p.1 p.2 * b p.1 p.2)
      ((volume.restrict (Ioc 0 T)).prod μ))
    (hX : ∀ᵐ ω ∂μ, |M T ω + ∫ s in (0 : ℝ)..T, b s ω| ≤ C)
    (hA : ∀ᵐ ω ∂μ, ∀ t ∈ Icc 0 T, |∫ s in (0 : ℝ)..t, b s ω| ≤ D) :
    Integrable (fun ω => (M T ω + ∫ s in (0 : ℝ)..T, b s ω) ^ 2) μ ∧
    (∫ ω, (M T ω + ∫ s in (0 : ℝ)..T, b s ω) ^ 2 ∂μ) =
      (∫ ω, (M T ω) ^ 2 ∂μ) +
        2 * ∫ s in (0 : ℝ)..T,
          ∫ ω, (M s ω + ∫ u in (0 : ℝ)..s, b u ω) * b s ω ∂μ := by
  obtain ⟨hcross, hAb⟩ := mixed_integrability_of_bounded_process hT hM hbMeas hbInt hX hA
  have hM2 : Integrable (fun ω => (M T ω) ^ 2) μ := by
    apply Integrable.of_bound
      (((hM.stronglyAdapted T).mono (ℱ.le T)).aestronglyMeasurable.pow 2) ((C + D) ^ 2)
    filter_upwards [ae_norm_martingale_le_of_bounded_process hT hX hA] with ω hω
    change ‖(M T ω) ^ 2‖ ≤ (C + D) ^ 2
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    calc
      (M T ω) ^ 2 = |M T ω| ^ 2 := (sq_abs _).symm
      _ ≤ (C + D) ^ 2 := pow_le_pow_left₀ (abs_nonneg _)
        (by simpa only [Real.norm_eq_abs] using hω) 2
  exact integral_sq_martingale_add_timeIntegral hT hM hb hM2 hbInt hcross hmeas hAb

end Problem367.MartingaleDriftEnergy

end

end OAI
