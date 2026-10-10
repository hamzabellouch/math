import OAI.Probability.FreeIsing.Martingales.InnovationMartingale

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367

theorem stronglyMeasurable_clipped_nnreal_process
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {F : Filtration ℝ≥0 mΩ}
    {m : ℝ≥0 → Ω → ℝ} (hm : IsStronglyProgressive F m) (t : ℝ≥0) :
    StronglyMeasurable[@MeasurableSpace.prod ℝ Ω inferInstance (F t)]
      (fun p : ℝ × Ω => m (min p.1.toNNReal t) p.2) := by
  let : MeasurableSpace Ω := F t
  let clip : ℝ → Set.Iic t := fun r => ⟨min r.toNNReal t, by exact (min_le_right r.toNNReal t)⟩
  have hc : Measurable clip := by
    dsimp [clip]
    fun_prop
  exact (hm t).comp_measurable ((hc.comp measurable_fst).prodMk measurable_snd)

theorem stronglyAdapted_nnrealTimePrimitive
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {F : Filtration ℝ≥0 mΩ}
    {m : ℝ≥0 → Ω → ℝ} (hm : IsStronglyProgressive F m) :
    StronglyAdapted F (nnrealTimePrimitive m) := by
  intro t
  have hcl := stronglyMeasurable_clipped_nnreal_process hm t
  have hi : StronglyMeasurable[F t]
      (fun ω => ∫ r in Set.Ioc (0 : ℝ) (t : ℝ), m (min r.toNNReal t) ω) := by
    let : MeasurableSpace Ω := F t
    exact hcl.integral_prod_left'
  convert hi using 1
  funext ω
  rw [nnrealTimePrimitive, intervalIntegral.integral_of_le t.coe_nonneg]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro r hr
  have hrt : r.toNNReal ≤ t := by simpa using Real.toNNReal_mono hr.2
  simp only [min_eq_left hrt]

theorem integrable_nnreal_process_interval_of_progressive_bounded
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {F : Filtration ℝ≥0 mΩ} {m : ℝ≥0 → Ω → ℝ}
    (hm : IsStronglyProgressive F m) (C : ℝ)
    (hbound : ∀ t, ∀ᵐ ω ∂P, |m t ω| ≤ C) (s t : ℝ≥0) :
    Integrable (fun p : ℝ × Ω => m p.1.toNNReal p.2)
      ((volume.restrict (Set.Ioc (s : ℝ) (t : ℝ))).prod P) := by
  let ν : Measure ℝ := volume.restrict (Set.Ioc (s : ℝ) (t : ℝ))
  have hle : @MeasurableSpace.prod ℝ Ω inferInstance (F t) ≤
      @MeasurableSpace.prod ℝ Ω inferInstance mΩ :=
    sup_le_sup le_rfl (MeasurableSpace.comap_mono (F.le t))
  have hcl : StronglyMeasurable (fun p : ℝ × Ω => m (min p.1.toNNReal t) p.2) :=
    (stronglyMeasurable_clipped_nnreal_process hm t).mono hle
  have hb : ∀ᵐ p ∂ν.prod P, ‖m (min p.1.toNNReal t) p.2‖ ≤ C := by
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_le hcl.norm.measurable measurable_const)).2
    apply Filter.Eventually.of_forall
    intro r
    simpa only [Real.norm_eq_abs] using hbound (min r.toNNReal t)
  have hi : Integrable (fun p : ℝ × Ω => m (min p.1.toNNReal t) p.2) (ν.prod P) :=
    (integrable_const C).mono' hcl.aestronglyMeasurable hb
  apply hi.congr
  have hmem : ∀ᵐ p ∂ν.prod P, p.1 ∈ Set.Ioc (s : ℝ) (t : ℝ) :=
    Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Ioc)
  filter_upwards [hmem] with p hp
  have hpt : p.1.toNNReal ≤ t := by simpa using Real.toNNReal_mono hp.2
  simp only [min_eq_left hpt]

theorem compensated_observation_martingale_of_progressive_bounded
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {F G : Filtration ℝ≥0 mΩ} {B m : ℝ≥0 → Ω → ℝ} {σ : Ω → ℝ}
    (hB : Martingale B G P) (hFG : ∀ t, F t ≤ G t) (hσ : Integrable σ P)
    (hXad : StronglyAdapted F (fun t ω => B t ω + (t : ℝ) * σ ω))
    (hm : IsStronglyProgressive F m)
    (hposterior : ∀ t, m t =ᵐ[P] P[σ | F t])
    (C : ℝ) (hbound : ∀ t, ∀ᵐ ω ∂P, |m t ω| ≤ C) :
    Martingale (fun t ω => B t ω + (t : ℝ) * σ ω -
      nnrealTimePrimitive m t ω) F P := by
  exact compensated_observation_martingale_of_posterior_version hB hFG hσ hXad
    hm.stronglyAdapted hposterior (stronglyAdapted_nnrealTimePrimitive hm)
    (fun s t _ => integrable_nnreal_process_interval_of_progressive_bounded hm C hbound s t)

theorem compensated_observation_martingale_of_bounded_signal
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {F G : Filtration ℝ≥0 mΩ} {B m : ℝ≥0 → Ω → ℝ} {σ : Ω → ℝ}
    (hB : Martingale B G P) (hFG : ∀ t, F t ≤ G t) (hσ : Integrable σ P)
    (hXad : StronglyAdapted F (fun t ω => B t ω + (t : ℝ) * σ ω))
    (hm : IsStronglyProgressive F m)
    (hposterior : ∀ t, m t =ᵐ[P] P[σ | F t])
    (C : ℝ) (hbound : ∀ᵐ ω ∂P, |σ ω| ≤ C) :
    Martingale (fun t ω => B t ω + (t : ℝ) * σ ω -
      nnrealTimePrimitive m t ω) F P := by
  apply compensated_observation_martingale_of_progressive_bounded hB hFG hσ hXad
    hm hposterior C
  intro t
  filter_upwards [hposterior t, ae_bdd_abs_condExp_of_ae_bdd_abs (m := F t) hbound]
    with ω heq hb
  rwa [heq]

theorem continuous_nnreal_primitive_of_integrable_horizons
    (f : ℝ → ℝ) (hf : ∀ n : ℕ, IntervalIntegrable f volume 0 (n : ℝ)) :
    Continuous (fun t : ℝ≥0 => ∫ u in (0 : ℝ)..(t : ℝ), f u) := by
  rw [continuous_iff_continuousAt]
  intro t
  obtain ⟨n, hn⟩ := exists_nat_gt (t : ℝ)
  have hcont : Continuous (fun s : ℝ≥0 => ∫ u in (0 : ℝ)..min (s : ℝ) (n : ℝ), f u) := by
    apply (intervalIntegral.continuousOn_primitive_interval' (hf n)
      (Set.left_mem_uIcc : (0 : ℝ) ∈ Set.uIcc 0 (n : ℝ))).comp_continuous
        (NNReal.continuous_coe.min continuous_const)
    intro s
    rw [Set.uIcc_of_le (Nat.cast_nonneg n)]
    exact ⟨le_min s.coe_nonneg (Nat.cast_nonneg n), min_le_right _ _⟩
  apply hcont.continuousAt.congr_of_eventuallyEq
  filter_upwards [NNReal.continuous_coe.continuousAt.eventually (gt_mem_nhds hn)] with s hs
  simp only [min_eq_left hs.le]

theorem ae_continuous_nnrealTimePrimitive_of_progressive_bounded
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {F : Filtration ℝ≥0 mΩ} {m : ℝ≥0 → Ω → ℝ}
    (hm : IsStronglyProgressive F m) (C : ℝ)
    (hbound : ∀ t, ∀ᵐ ω ∂P, |m t ω| ≤ C) :
    ∀ᵐ ω ∂P, Continuous (fun t => nnrealTimePrimitive m t ω) := by
  have hi (n : ℕ) : ∀ᵐ ω ∂P,
      IntervalIntegrable (fun u : ℝ => m u.toNNReal ω) volume 0 (n : ℝ) := by
    have hh := (integrable_nnreal_process_interval_of_progressive_bounded hm C hbound
      0 (n : ℝ≥0)).prod_left_ae
    filter_upwards [hh] with ω hω
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le (Nat.cast_nonneg n)).mpr
    simpa only [IntegrableOn, NNReal.coe_zero, NNReal.coe_natCast] using hω
  filter_upwards [ae_all_iff.mpr hi] with ω hω
  exact continuous_nnreal_primitive_of_integrable_horizons _ hω

theorem ae_continuous_compensated_observation
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {F : Filtration ℝ≥0 mΩ} {B m : ℝ≥0 → Ω → ℝ} (σ : Ω → ℝ)
    (hB : ∀ᵐ ω ∂P, Continuous (fun t => B t ω))
    (hm : IsStronglyProgressive F m) (C : ℝ)
    (hbound : ∀ t, ∀ᵐ ω ∂P, |m t ω| ≤ C) :
    ∀ᵐ ω ∂P, Continuous (fun t => B t ω + (t : ℝ) * σ ω -
      nnrealTimePrimitive m t ω) := by
  filter_upwards [hB, ae_continuous_nnrealTimePrimitive_of_progressive_bounded hm C hbound]
    with ω hBω hAω
  exact (hBω.add (NNReal.continuous_coe.mul continuous_const)).sub hAω

end Problem367

end

end OAI
