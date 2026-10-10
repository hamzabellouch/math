import OAI.Probability.FreeIsing.Energy.DiscrepancyEnergy

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal Topology

namespace Problem367.DiscrepancyEnergy

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

theorem tendsto_integral_stopped_density [SFinite P]
    {τ : ℕ → Ω → WithTop ℝ≥0} (hτ : ∀ n, Measurable (τ n))
    {E : ℝ → Ω → ℝ} {T : ℝ≥0}
    (hE : Integrable (fun p : ℝ × Ω => E p.1 p.2)
      ((volume.restrict (Ioc (0 : ℝ) T)).prod P))
    (hexit : ∀ᵐ ω ∂P, ∀ᶠ n in atTop, (T : WithTop ℝ≥0) ≤ τ n ω) :
    Tendsto (fun n => ∫ s in (0 : ℝ)..(T : ℝ),
      ∫ ω, if (s.toNNReal : WithTop ℝ≥0) ≤ τ n ω then E s ω else 0 ∂P)
      atTop (𝓝 (∫ s in (0 : ℝ)..(T : ℝ), ∫ ω, E s ω ∂P)) := by
  let Q := (volume.restrict (Ioc (0 : ℝ) (T : ℝ))).prod P
  let A n := {p : ℝ × Ω | (p.1.toNNReal : WithTop ℝ≥0) ≤ τ n p.2}
  have hA (n : ℕ) : MeasurableSet (A n) :=
    measurableSet_le ((measurable_real_toNNReal.comp measurable_fst).withTop_coe)
      ((hτ n).comp measurable_snd)
  have hEn (n : ℕ) : Integrable ((A n).indicator (fun p : ℝ × Ω => E p.1 p.2)) Q :=
    hE.indicator (hA n)
  have hlim : Tendsto (fun n => ∫ p, (A n).indicator (fun p : ℝ × Ω => E p.1 p.2) p ∂Q)
      atTop (𝓝 (∫ p : ℝ × Ω, E p.1 p.2 ∂Q)) := by
    apply tendsto_integral_of_dominated_convergence (fun p : ℝ × Ω => ‖E p.1 p.2‖)
      (fun n => (hEn n).aestronglyMeasurable) hE.norm
    · intro n
      apply Eventually.of_forall
      intro p
      by_cases hp : p ∈ A n <;> simp [hp]
    · have hm : ∀ᵐ p ∂Q, p.1 ∈ Ioc (0 : ℝ) (T : ℝ) :=
        Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Ioc)
      have he : ∀ᵐ p ∂Q, ∀ᶠ n in atTop, (T : WithTop ℝ≥0) ≤ τ n p.2 :=
        Measure.quasiMeasurePreserving_snd.ae hexit
      filter_upwards [hm, he] with p hp he
      have hpT : p.1.toNNReal ≤ T := by
        simpa only [Real.toNNReal_coe] using Real.toNNReal_mono hp.2
      apply tendsto_const_nhds.congr'
      filter_upwards [he] with n hn
      exact (Set.indicator_of_mem (show p ∈ A n from
        (WithTop.coe_le_coe.mpr hpT).trans hn) (fun p : ℝ × Ω => E p.1 p.2)).symm
  have heq (n : ℕ) : (∫ p, (A n).indicator (fun p : ℝ × Ω => E p.1 p.2) p ∂Q) =
      ∫ s in (0 : ℝ)..(T : ℝ),
        ∫ ω, if (s.toNNReal : WithTop ℝ≥0) ≤ τ n ω then E s ω else 0 ∂P := by
    rw [integral_prod _ (hEn n), intervalIntegral.integral_of_le T.coe_nonneg]
    simp only [Set.indicator, A, mem_ofPred_eq]
  have heq' : (∫ p : ℝ × Ω, E p.1 p.2 ∂Q) =
      ∫ s in (0 : ℝ)..(T : ℝ), ∫ ω, E s ω ∂P := by
    rw [integral_prod _ hE, intervalIntegral.integral_of_le T.coe_nonneg]
  simpa only [heq, heq'] using hlim

theorem tendsto_integral_stopped_square [IsFiniteMeasure P]
    {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ}
    (hX : IsStronglyProgressive F X)
    {τ : ℕ → Ω → WithTop ℝ≥0} (hτ : ∀ n, IsStoppingTime F (τ n))
    {T t : ℝ≥0} (ht : t ≤ T) {C : ℝ}
    (hb : ∀ᵐ ω ∂P, ∀ s ≤ T, |X s ω| ≤ C)
    (hexit : ∀ᵐ ω ∂P, ∀ᶠ n in atTop, (T : WithTop ℝ≥0) ≤ τ n ω) :
    Tendsto (fun n => ∫ ω, (stoppedProcess X (τ n) t ω) ^ 2 ∂P)
      atTop (𝓝 (∫ ω, (X t ω) ^ 2 ∂P)) := by
  apply tendsto_integral_of_dominated_convergence (fun _ : Ω => C ^ 2)
  · intro n
    have hm : AEStronglyMeasurable (stoppedProcess X (τ n) t) P :=
      (((hX.stoppedProcess (hτ n)).stronglyAdapted t).mono (F.le t)).aestronglyMeasurable
    exact hm.pow 2
  · exact integrable_const _
  · intro n
    filter_upwards [hb] with ω hω
    have hs : |stoppedProcess X (τ n) t ω| ≤ C := by
      exact hω _ ((WithTop.untopA_le (min_le_left (t : WithTop ℝ≥0) (τ n ω))).trans ht)
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hs 2
  · filter_upwards [hexit] with ω hω
    apply tendsto_const_nhds.congr'
    filter_upwards [hω] with n hn
    rw [stoppedProcess_eq_of_le ((WithTop.coe_le_coe.mpr ht).trans hn)]

theorem secondMoment_integral_representation_of_stopped [IsFiniteMeasure P]
    {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ}
    (hX : IsStronglyProgressive F X)
    {τ : ℕ → Ω → WithTop ℝ≥0} (hτ : ∀ n, IsStoppingTime F (τ n))
    {T : ℝ≥0} {C : ℝ}
    (hb : ∀ᵐ ω ∂P, ∀ s ≤ T, |X s ω| ≤ C)
    (hexit : ∀ᵐ ω ∂P, ∀ᶠ n in atTop, (T : WithTop ℝ≥0) ≤ τ n ω)
    {E : ℝ → Ω → ℝ}
    (hE : Integrable (fun p : ℝ × Ω => E p.1 p.2)
      ((volume.restrict (Ioc (0 : ℝ) T)).prod P))
    (hlocal : ∀ n, ∀ t ≤ T,
      (∫ ω, (stoppedProcess X (τ n) t ω) ^ 2 ∂P) =
        (∫ ω, (X 0 ω) ^ 2 ∂P) + ∫ s in (0 : ℝ)..(t : ℝ),
          ∫ ω, if (s.toNNReal : WithTop ℝ≥0) ≤ τ n ω then E s ω else 0 ∂P) :
    ∀ t ≤ T, (∫ ω, (X t ω) ^ 2 ∂P) =
      (∫ ω, (X 0 ω) ^ 2 ∂P) + ∫ s in (0 : ℝ)..(t : ℝ), ∫ ω, E s ω ∂P := by
  intro t ht
  have hEt : Integrable (fun p : ℝ × Ω => E p.1 p.2)
      ((volume.restrict (Ioc (0 : ℝ) (t : ℝ))).prod P) :=
    hE.mono_measure (Measure.prod_mono
      (Measure.restrict_mono_set _ (Ioc_subset_Ioc_right (show (t : ℝ) ≤ T from ht))) le_rfl)
  have hxt : ∀ᵐ ω ∂P, ∀ᶠ n in atTop, (t : WithTop ℝ≥0) ≤ τ n ω := by
    filter_upwards [hexit] with ω hω
    filter_upwards [hω] with n hn
    exact (WithTop.coe_le_coe.mpr ht).trans hn
  have hl := tendsto_integral_stopped_square hX hτ ht hb hexit
  have hr := (tendsto_integral_stopped_density (fun n => (hτ n).measurable') hEt hxt).const_add
    (∫ ω, (X 0 ω) ^ 2 ∂P)
  have heq : (fun n => ∫ ω, (stoppedProcess X (τ n) t ω) ^ 2 ∂P) =
      (fun n => (∫ ω, (X 0 ω) ^ 2 ∂P) + ∫ s in (0 : ℝ)..(t : ℝ),
        ∫ ω, if (s.toNNReal : WithTop ℝ≥0) ≤ τ n ω then E s ω else 0 ∂P) :=
    funext (fun n => hlocal n t ht)
  rw [heq] at hl
  exact tendsto_nhds_unique hl hr

theorem secondMoment_analysis_of_stopped [IsFiniteMeasure P]
    {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ}
    (hX : IsStronglyProgressive F X)
    {τ : ℕ → Ω → WithTop ℝ≥0} (hτ : ∀ n, IsStoppingTime F (τ n))
    {T : ℝ≥0} {C : ℝ}
    (hb : ∀ᵐ ω ∂P, ∀ s ≤ T, |X s ω| ≤ C)
    (hexit : ∀ᵐ ω ∂P, ∀ᶠ n in atTop, (T : WithTop ℝ≥0) ≤ τ n ω)
    {E : ℝ → Ω → ℝ}
    (hE : Integrable (fun p : ℝ × Ω => E p.1 p.2)
      ((volume.restrict (Ioc (0 : ℝ) T)).prod P))
    (hlocal : ∀ n, ∀ t ≤ T,
      (∫ ω, (stoppedProcess X (τ n) t ω) ^ 2 ∂P) =
        (∫ ω, (X 0 ω) ^ 2 ∂P) + ∫ s in (0 : ℝ)..(t : ℝ),
          ∫ ω, if (s.toNNReal : WithTop ℝ≥0) ≤ τ n ω then E s ω else 0 ∂P) :
    AbsolutelyContinuousOnInterval (fun t : ℝ => ∫ ω, (X t.toNNReal ω) ^ 2 ∂P) 0 T ∧
      (∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) T),
        deriv (fun s : ℝ => ∫ ω, (X s.toNNReal ω) ^ 2 ∂P) t = ∫ ω, E t ω ∂P) := by
  have hrep : ∀ t ∈ Icc (0 : ℝ) (T : ℝ),
      (∫ ω, (X t.toNNReal ω) ^ 2 ∂P) =
        (∫ ω, (X 0 ω) ^ 2 ∂P) + ∫ s in (0 : ℝ)..t, ∫ ω, E s ω ∂P := by
    intro t ht
    have htT : t.toNNReal ≤ T := by
      simpa only [Real.toNNReal_coe] using Real.toNNReal_mono ht.2
    simpa only [Real.coe_toNNReal t ht.1] using
      secondMoment_integral_representation_of_stopped hX hτ hb hexit hE hlocal t.toNNReal htT
  refine ⟨?_, ae_deriv_of_integral_representation T.coe_nonneg
    (intervalIntegrable_mean T.coe_nonneg hE) hrep⟩
  apply absolutelyContinuousOnInterval_of_integral_representation
    (intervalIntegrable_mean T.coe_nonneg hE)
  simpa only [uIcc_of_le T.coe_nonneg] using hrep

end Problem367.DiscrepancyEnergy

end

end OAI
