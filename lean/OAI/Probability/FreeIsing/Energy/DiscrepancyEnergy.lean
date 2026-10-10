import OAI.Probability.FreeIsing.Estimates.AbsoluteContinuity

namespace OAI

noncomputable section

open MeasureTheory Filter Set
open scoped Topology

namespace Problem367.DiscrepancyEnergy

theorem absolutelyContinuousOnInterval_congr_on
    {f g : ℝ → ℝ} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b)
    (hfg : EqOn f g (uIcc a b)) :
    AbsolutelyContinuousOnInterval g a b := by
  rw [absolutelyContinuousOnInterval_iff] at hf ⊢
  intro ε hε
  obtain ⟨δ, hδ, hδf⟩ := hf ε hε
  refine ⟨δ, hδ, ?_⟩
  intro E hE hlen
  have heq : (∑ i ∈ Finset.range E.1,
      dist (f (E.2 i).1) (f (E.2 i).2)) =
      ∑ i ∈ Finset.range E.1, dist (g (E.2 i).1) (g (E.2 i).2) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [hfg (hE.1 i hi).1, hfg (hE.1 i hi).2]
  rw [← heq]
  exact hδf E hE hlen

theorem absolutelyContinuousOnInterval_of_integral_representation
    {V k : ℝ → ℝ} {a b c : ℝ}
    (hk : IntervalIntegrable k volume a b)
    (hV : ∀ t ∈ uIcc a b, V t = c + ∫ s in a..t, k s) :
    AbsolutelyContinuousOnInterval V a b := by
  have hc : AbsolutelyContinuousOnInterval (fun _ : ℝ => c) a b :=
    contDiffOn_const.absolutelyContinuousOnInterval
  apply absolutelyContinuousOnInterval_congr_on
    (hc.fun_add (hk.absolutelyContinuousOnInterval_intervalIntegral (c := a) (by simp)))
  intro t ht
  exact (hV t ht).symm

theorem integral_timePrimitive
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [SFinite μ]
    {E : ℝ → Ω → ℝ} {T t : ℝ} (ht : t ∈ Icc 0 T)
    (hE : Integrable (fun p : ℝ × Ω => E p.1 p.2)
      ((volume.restrict (Ioc 0 T)).prod μ)) :
    (∫ ω, (∫ s in (0 : ℝ)..t, E s ω) ∂μ) =
      ∫ s in (0 : ℝ)..t, ∫ ω, E s ω ∂μ := by
  have hEt : Integrable (fun p : ℝ × Ω => E p.1 p.2)
      ((volume.restrict (Ioc 0 t)).prod μ) :=
    hE.mono_measure (Measure.prod_mono
      (Measure.restrict_mono_set _ (Ioc_subset_Ioc_right ht.2)) le_rfl)
  simp only [intervalIntegral.integral_of_le ht.1]
  exact (integral_integral_swap (f := E) hEt).symm

theorem intervalIntegrable_mean
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [SFinite μ]
    {E : ℝ → Ω → ℝ} {T : ℝ} (hT : 0 ≤ T)
    (hE : Integrable (fun p : ℝ × Ω => E p.1 p.2)
      ((volume.restrict (Ioc 0 T)).prod μ)) :
    IntervalIntegrable (fun s => ∫ ω, E s ω ∂μ) volume 0 T := by
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).mpr hE.integral_prod_left

theorem secondMoment_integral_representation
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [SFinite μ]
    {X M E : ℝ → Ω → ℝ} {T : ℝ}
    (hX0 : Integrable (fun ω => (X 0 ω) ^ 2) μ)
    (hM : ∀ t ∈ Icc 0 T, Integrable (M t) μ)
    (hMzero : ∀ t ∈ Icc 0 T, (∫ ω, M t ω ∂μ) = 0)
    (hE : Integrable (fun p : ℝ × Ω => E p.1 p.2)
      ((volume.restrict (Ioc 0 T)).prod μ))
    (hdecomp : ∀ t ∈ Icc 0 T, ∀ᵐ ω ∂μ,
      (X t ω) ^ 2 = (X 0 ω) ^ 2 + M t ω + ∫ s in (0 : ℝ)..t, E s ω) :
    ∀ t ∈ Icc 0 T,
      (∫ ω, (X t ω) ^ 2 ∂μ) = (∫ ω, (X 0 ω) ^ 2 ∂μ) +
        ∫ s in (0 : ℝ)..t, ∫ ω, E s ω ∂μ := by
  intro t ht
  have hEt : Integrable (fun p : ℝ × Ω => E p.1 p.2)
      ((volume.restrict (Ioc 0 t)).prod μ) :=
    hE.mono_measure (Measure.prod_mono
      (Measure.restrict_mono_set _ (Ioc_subset_Ioc_right ht.2)) le_rfl)
  have hprim : Integrable (fun ω => ∫ s in (0 : ℝ)..t, E s ω) μ := by
    simpa only [intervalIntegral.integral_of_le ht.1] using hEt.integral_prod_right
  calc
    (∫ ω, (X t ω) ^ 2 ∂μ) =
        ∫ ω, (X 0 ω) ^ 2 + M t ω + (∫ s in (0 : ℝ)..t, E s ω) ∂μ :=
      integral_congr_ae (hdecomp t ht)
    _ = (∫ ω, (X 0 ω) ^ 2 + M t ω ∂μ) +
        ∫ ω, (∫ s in (0 : ℝ)..t, E s ω) ∂μ :=
      integral_add (hX0.add (hM t ht)) hprim
    _ = (∫ ω, (X 0 ω) ^ 2 ∂μ) + ∫ s in (0 : ℝ)..t, ∫ ω, E s ω ∂μ := by
      rw [integral_add hX0 (hM t ht), hMzero t ht, add_zero,
        integral_timePrimitive ht hE]

theorem secondMoment_absolutelyContinuous
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [SFinite μ]
    {X M E : ℝ → Ω → ℝ} {T : ℝ} (hT : 0 ≤ T)
    (hX0 : Integrable (fun ω => (X 0 ω) ^ 2) μ)
    (hM : ∀ t ∈ Icc 0 T, Integrable (M t) μ)
    (hMzero : ∀ t ∈ Icc 0 T, (∫ ω, M t ω ∂μ) = 0)
    (hE : Integrable (fun p : ℝ × Ω => E p.1 p.2)
      ((volume.restrict (Ioc 0 T)).prod μ))
    (hdecomp : ∀ t ∈ Icc 0 T, ∀ᵐ ω ∂μ,
      (X t ω) ^ 2 = (X 0 ω) ^ 2 + M t ω + ∫ s in (0 : ℝ)..t, E s ω) :
    AbsolutelyContinuousOnInterval (fun t => ∫ ω, (X t ω) ^ 2 ∂μ) 0 T := by
  apply absolutelyContinuousOnInterval_of_integral_representation
    (intervalIntegrable_mean hT hE)
  simpa only [uIcc_of_le hT] using
    secondMoment_integral_representation hX0 hM hMzero hE hdecomp

theorem ae_deriv_of_integral_representation
    {V k : ℝ → ℝ} {a b c : ℝ} (hab : a ≤ b)
    (hk : IntervalIntegrable k volume a b)
    (hV : ∀ t ∈ Icc a b, V t = c + ∫ s in a..t, k s) :
    ∀ᵐ t ∂volume.restrict (Icc a b), deriv V t = k t := by
  rw [← restrict_Ioo_eq_restrict_Icc, ae_restrict_iff' measurableSet_Ioo]
  filter_upwards [hk.ae_hasDerivAt_integral] with t ht hmem
  have ht' : t ∈ uIcc a b := by
    rw [uIcc_of_le hab]
    exact ⟨hmem.1.le, hmem.2.le⟩
  have hlocal : V =ᶠ[𝓝 t] (fun x => c + ∫ s in a..x, k s) := by
    filter_upwards [Ioo_mem_nhds hmem.1 hmem.2] with x hx
    exact hV x ⟨hx.1.le, hx.2.le⟩
  exact ((ht ht' a (by simp)).const_add c).congr_of_eventuallyEq hlocal |>.deriv

theorem secondMoment_ae_deriv
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [SFinite μ]
    {X M E : ℝ → Ω → ℝ} {T : ℝ} (hT : 0 ≤ T)
    (hX0 : Integrable (fun ω => (X 0 ω) ^ 2) μ)
    (hM : ∀ t ∈ Icc 0 T, Integrable (M t) μ)
    (hMzero : ∀ t ∈ Icc 0 T, (∫ ω, M t ω ∂μ) = 0)
    (hE : Integrable (fun p : ℝ × Ω => E p.1 p.2)
      ((volume.restrict (Ioc 0 T)).prod μ))
    (hdecomp : ∀ t ∈ Icc 0 T, ∀ᵐ ω ∂μ,
      (X t ω) ^ 2 = (X 0 ω) ^ 2 + M t ω + ∫ s in (0 : ℝ)..t, E s ω) :
    ∀ᵐ t ∂volume.restrict (Icc 0 T),
      deriv (fun s => ∫ ω, (X s ω) ^ 2 ∂μ) t = ∫ ω, E t ω ∂μ :=
  ae_deriv_of_integral_representation hT (intervalIntegrable_mean hT hE)
    (secondMoment_integral_representation hX0 hM hMzero hE hdecomp)

theorem integral_martingale_eq_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {F : Filtration ℝ mΩ} {M : ℝ → Ω → ℝ} (hM : Martingale M F μ)
    (hM0 : M 0 =ᵐ[μ] fun _ => 0) {t : ℝ} (ht : 0 ≤ t) :
    (∫ ω, M t ω ∂μ) = 0 := by
  calc
    (∫ ω, M t ω ∂μ) = ∫ ω, μ[M t | F 0] ω ∂μ :=
      (integral_condExp (F.le 0)).symm
    _ = ∫ ω, M 0 ω ∂μ := integral_congr_ae (hM.condExp_ae_eq ht)
    _ = 0 := by rw [integral_congr_ae hM0]; simp

theorem secondMoment_analysis_of_martingale
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {F : Filtration ℝ mΩ} {X M E : ℝ → Ω → ℝ} {T : ℝ} (hT : 0 ≤ T)
    (hX0 : Integrable (fun ω => (X 0 ω) ^ 2) μ)
    (hM : Martingale M F μ) (hM0 : M 0 =ᵐ[μ] fun _ => 0)
    (hE : Integrable (fun p : ℝ × Ω => E p.1 p.2)
      ((volume.restrict (Ioc 0 T)).prod μ))
    (hdecomp : ∀ t ∈ Icc 0 T, ∀ᵐ ω ∂μ,
      (X t ω) ^ 2 = (X 0 ω) ^ 2 + M t ω + ∫ s in (0 : ℝ)..t, E s ω) :
    AbsolutelyContinuousOnInterval (fun t => ∫ ω, (X t ω) ^ 2 ∂μ) 0 T ∧
      (∀ᵐ t ∂volume.restrict (Icc 0 T),
        deriv (fun s => ∫ ω, (X s ω) ^ 2 ∂μ) t = ∫ ω, E t ω ∂μ) := by
  have hMi : ∀ t ∈ Icc 0 T, Integrable (M t) μ := fun t _ => hM.integrable t
  have hMz : ∀ t ∈ Icc 0 T, (∫ ω, M t ω ∂μ) = 0 :=
    fun _ ht => integral_martingale_eq_zero hM hM0 ht.1
  exact ⟨secondMoment_absolutelyContinuous hT hX0 hMi hMz hE hdecomp,
    secondMoment_ae_deriv hT hX0 hMi hMz hE hdecomp⟩

end Problem367.DiscrepancyEnergy

end

end OAI
