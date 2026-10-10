import OAI.Probability.FreeIsing.Estimates.ProgressivePrimitive

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal

namespace Problem367

theorem ae_all_nnrealTimePrimitive_eq_of_modification
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [SFinite P]
    {F G : Filtration ℝ≥0 mΩ} {m k : ℝ≥0 → Ω → ℝ}
    (hm : IsStronglyProgressive F m) (hk : IsStronglyProgressive G k)
    (heq : ∀ t, m t =ᵐ[P] k t) :
    ∀ᵐ ω ∂P, ∀ t, nnrealTimePrimitive m t ω = nnrealTimePrimitive k t ω := by
  have hlocal : ∀ n : ℕ, ∀ᵐ ω ∂P,
      (fun u : ℝ => m u.toNNReal ω) =ᵐ[volume.restrict (Set.Ioc 0 (n : ℝ))]
        (fun u : ℝ => k u.toNNReal ω) := by
    intro n
    let ν : Measure ℝ := volume.restrict (Set.Ioc 0 (n : ℝ))
    have hcm : StronglyMeasurable
        (fun p : ℝ × Ω => m (min p.1.toNNReal (n : ℝ≥0)) p.2) :=
      (stronglyMeasurable_clipped_nnreal_process hm (n : ℝ≥0)).mono
        (sup_le_sup le_rfl (MeasurableSpace.comap_mono (F.le (n : ℝ≥0))))
    have hck : StronglyMeasurable
        (fun p : ℝ × Ω => k (min p.1.toNNReal (n : ℝ≥0)) p.2) :=
      (stronglyMeasurable_clipped_nnreal_process hk (n : ℝ≥0)).mono
        (sup_le_sup le_rfl (MeasurableSpace.comap_mono (G.le (n : ℝ≥0))))
    have hc : ∀ᵐ ω ∂P, ∀ᵐ u ∂ν,
        m (min u.toNNReal (n : ℝ≥0)) ω = k (min u.toNNReal (n : ℝ≥0)) ω := by
      apply (Measure.ae_ae_comm (μ := ν) (ν := P)
        (p := fun u ω => m (min u.toNNReal (n : ℝ≥0)) ω =
          k (min u.toNNReal (n : ℝ≥0)) ω)
        (measurableSet_eq_fun hcm.measurable hck.measurable)).mp
      exact Filter.Eventually.of_forall fun u => heq (min u.toNNReal (n : ℝ≥0))
    filter_upwards [hc] with ω hω
    filter_upwards [hω, ae_restrict_mem measurableSet_Ioc] with u hu hmem
    have hun : u.toNNReal ≤ (n : ℝ≥0) :=
      Real.toNNReal_le_iff_le_coe.mpr hmem.2
    simpa only [min_eq_left hun] using hu
  filter_upwards [ae_all_iff.mpr hlocal] with ω hω
  intro t
  obtain ⟨n, hn⟩ := exists_nat_gt (t : ℝ)
  simp only [nnrealTimePrimitive, intervalIntegral.integral_of_le t.coe_nonneg]
  exact integral_congr_ae
    (ae_restrict_of_ae_restrict_of_subset (Ioc_subset_Ioc le_rfl hn.le) (hω n))

theorem posterior_version_ae_abs_le
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {F : Filtration ℝ≥0 mΩ} {m : ℝ≥0 → Ω → ℝ} {σ : Ω → ℝ}
    (hposterior : ∀ t, m t =ᵐ[P] P[σ | F t]) {C : ℝ}
    (hσbound : ∀ᵐ ω ∂P, |σ ω| ≤ C) :
    ∀ t, ∀ᵐ ω ∂P, |m t ω| ≤ C := by
  intro t
  filter_upwards [hposterior t,
    ae_bdd_abs_condExp_of_ae_bdd_abs (m := F t) hσbound] with ω hmω hb
  simpa only [hmω] using hb

theorem ae_locally_integrable_bounded_progressive
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {F : Filtration ℝ≥0 mΩ} {m : ℝ≥0 → Ω → ℝ}
    (hm : IsStronglyProgressive F m) {C : ℝ}
    (hbound : ∀ t, ∀ᵐ ω ∂P, |m t ω| ≤ C) :
    ∀ᵐ ω ∂P, ∀ n : ℕ,
      IntegrableOn (fun u : ℝ => m u.toNNReal ω) (Ioc 0 (n : ℝ)) ∧
      ∀ᵐ u ∂volume.restrict (Ioc 0 (n : ℝ)), |m u.toNNReal ω| ≤ C := by
  apply ae_all_iff.mpr
  intro n
  let ν : Measure ℝ := volume.restrict (Ioc 0 (n : ℝ))
  have hclip : StronglyMeasurable
      (fun p : ℝ × Ω => m (min p.1.toNNReal (n : ℝ≥0)) p.2) :=
    (stronglyMeasurable_clipped_nnreal_process hm (n : ℝ≥0)).mono
      (sup_le_sup le_rfl (MeasurableSpace.comap_mono (F.le (n : ℝ≥0))))
  have hb : ∀ᵐ ω ∂P, ∀ᵐ u ∂ν, |m (min u.toNNReal (n : ℝ≥0)) ω| ≤ C := by
    apply (Measure.ae_ae_comm (μ := ν) (ν := P)
      (p := fun u ω => |m (min u.toNNReal (n : ℝ≥0)) ω| ≤ C)
      (measurableSet_le hclip.measurable.abs measurable_const)).mp
    exact Filter.Eventually.of_forall fun u => hbound (min u.toNNReal (n : ℝ≥0))
  have hi := (integrable_nnreal_process_interval_of_progressive_bounded
    hm C hbound 0 (n : ℝ≥0)).prod_left_ae
  filter_upwards [hb, hi] with ω hbω hiω
  constructor
  · simpa only [IntegrableOn, NNReal.coe_zero, NNReal.coe_natCast] using hiω
  · filter_upwards [hbω, ae_restrict_mem measurableSet_Ioc] with u hu hmem
    have hun : u.toNNReal ≤ (n : ℝ≥0) :=
      Real.toNNReal_le_iff_le_coe.mpr hmem.2
    simpa only [min_eq_left hun] using hu

theorem lipschitzWith_nnrealTimePrimitive_of_local_bounds
    {Ω : Type*} {m : ℝ≥0 → Ω → ℝ} {ω : Ω} {C : ℝ≥0}
    (hint : ∀ n : ℕ,
      IntegrableOn (fun u : ℝ => m u.toNNReal ω) (Ioc 0 (n : ℝ)))
    (hbound : ∀ n : ℕ, ∀ᵐ u ∂volume.restrict (Ioc 0 (n : ℝ)),
      |m u.toNNReal ω| ≤ (C : ℝ)) :
    LipschitzWith C (fun t => nnrealTimePrimitive m t ω) := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro s t
  obtain ⟨n, hn⟩ := exists_nat_gt (max (s : ℝ) (t : ℝ))
  have hsn : (s : ℝ) ≤ n := (le_max_left _ _).trans hn.le
  have htn : (t : ℝ) ≤ n := (le_max_right _ _).trans hn.le
  have his : IntervalIntegrable (fun u : ℝ => m u.toNNReal ω) volume 0 s :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le s.coe_nonneg).mpr
      ((hint n).mono_set (Ioc_subset_Ioc le_rfl hsn))
  have hit : IntervalIntegrable (fun u : ℝ => m u.toNNReal ω) volume 0 t :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le t.coe_nonneg).mpr
      ((hint n).mono_set (Ioc_subset_Ioc le_rfl htn))
  have hsub : uIoc (t : ℝ) (s : ℝ) ⊆ Ioc 0 (n : ℝ) := by
    intro u hu
    exact ⟨lt_of_le_of_lt (le_min t.coe_nonneg s.coe_nonneg) hu.1,
      hu.2.trans (max_le htn hsn)⟩
  have hb : ∀ᵐ u ∂volume, u ∈ uIoc (t : ℝ) (s : ℝ) →
      ‖m u.toNNReal ω‖ ≤ (C : ℝ) := by
    apply ae_imp_of_ae_restrict
    simpa only [Real.norm_eq_abs] using
      ae_restrict_of_ae_restrict_of_subset hsub (hbound n)
  simp only [Real.dist_eq, NNReal.dist_eq, nnrealTimePrimitive]
  rw [intervalIntegral.integral_interval_sub_left his hit]
  simpa only [Real.norm_eq_abs] using
    intervalIntegral.norm_integral_le_of_norm_le_const_ae hb

theorem ae_lipschitzWith_nnrealTimePrimitive
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {F : Filtration ℝ≥0 mΩ} {m : ℝ≥0 → Ω → ℝ}
    (hm : IsStronglyProgressive F m) {C : ℝ≥0}
    (hbound : ∀ t, ∀ᵐ ω ∂P, |m t ω| ≤ (C : ℝ)) :
    ∀ᵐ ω ∂P, LipschitzWith C (fun t => nnrealTimePrimitive m t ω) := by
  filter_upwards [ae_locally_integrable_bounded_progressive hm hbound] with ω hω
  exact lipschitzWith_nnrealTimePrimitive_of_local_bounds
    (fun n => (hω n).1) (fun n => (hω n).2)

end Problem367

end

end OAI
