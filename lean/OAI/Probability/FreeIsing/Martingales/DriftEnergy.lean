import OAI.Probability.FreeIsing.Energy.DriftSquareEnergy

namespace OAI

noncomputable section

open MeasureTheory Set Filter
open scoped Topology

namespace Problem367.MartingaleDriftEnergy

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}

theorem condExp_mul_past_eq [IsFiniteMeasure μ]
    {I : Type*} [Preorder I] {ℱ : Filtration I mΩ}
    {M : I → Ω → ℝ} (hM : Martingale M ℱ μ) {s t : I} (hst : s ≤ t)
    {H : Ω → ℝ} (hH : StronglyMeasurable[ℱ s] H)
    (hprod : Integrable (fun ω => M t ω * H ω) μ) :
    μ[(fun ω => M t ω * H ω) | ℱ s] =ᵐ[μ] fun ω => M s ω * H ω := by
  change μ[M t * H | ℱ s] =ᵐ[μ] fun ω => M s ω * H ω
  have hp : Integrable (M t * H) μ := hprod
  have hCE := condExp_mul_of_stronglyMeasurable_right hH hp (hM.integrable t)
  filter_upwards [hCE, hM.condExp_ae_eq hst] with ω hce hm
  simpa only [Pi.mul_apply, hm] using hce

theorem integrable_mul_past [IsFiniteMeasure μ]
    {I : Type*} [Preorder I] {ℱ : Filtration I mΩ}
    {M : I → Ω → ℝ} (hM : Martingale M ℱ μ) {s t : I} (hst : s ≤ t)
    {H : Ω → ℝ} (hH : StronglyMeasurable[ℱ s] H)
    (hprod : Integrable (fun ω => M t ω * H ω) μ) :
    Integrable (fun ω => M s ω * H ω) μ :=
  integrable_condExp.congr (condExp_mul_past_eq hM hst hH hprod)

theorem integral_abs_mul_past_le [IsFiniteMeasure μ]
    {I : Type*} [Preorder I] {ℱ : Filtration I mΩ}
    {M : I → Ω → ℝ} (hM : Martingale M ℱ μ) {s t : I} (hst : s ≤ t)
    {H : Ω → ℝ} (hH : StronglyMeasurable[ℱ s] H)
    (hprod : Integrable (fun ω => M t ω * H ω) μ) :
    (∫ ω, |M s ω * H ω| ∂μ) ≤ ∫ ω, |M t ω * H ω| ∂μ := by
  calc
    (∫ ω, |M s ω * H ω| ∂μ) =
        ∫ ω, |μ[(fun ω => M t ω * H ω) | ℱ s] ω| ∂μ := by
      apply integral_congr_ae
      filter_upwards [condExp_mul_past_eq hM hst hH hprod] with ω hω
      rw [hω]
    _ ≤ ∫ ω, |M t ω * H ω| ∂μ := integral_abs_condExp_le _

theorem integral_mul_past_eq [IsFiniteMeasure μ]
    {I : Type*} [Preorder I] {ℱ : Filtration I mΩ}
    {M : I → Ω → ℝ} (hM : Martingale M ℱ μ) {s t : I} (hst : s ≤ t)
    {H : Ω → ℝ} (hH : StronglyMeasurable[ℱ s] H)
    (hprod : Integrable (fun ω => M t ω * H ω) μ) :
    (∫ ω, M t ω * H ω ∂μ) = ∫ ω, M s ω * H ω ∂μ := by
  have hp : Integrable (H * M t) μ := by
    change Integrable (fun ω => H ω * M t ω) μ
    simpa only [mul_comm] using hprod
  have hCE := condExp_mul_of_stronglyMeasurable_left hH hp (hM.integrable t)
  calc
    (∫ ω, M t ω * H ω ∂μ) = ∫ ω, μ[H * M t | ℱ s] ω ∂μ := by
      simpa only [Pi.mul_apply, mul_comm] using (integral_condExp (ℱ.le s) (f := H * M t)).symm
    _ = ∫ ω, M s ω * H ω ∂μ := by
      apply integral_congr_ae
      filter_upwards [hCE, hM.condExp_ae_eq hst] with ω hce hm
      simpa only [Pi.mul_apply, hm, mul_comm] using hce

theorem integral_martingale_mul_timeIntegral [IsFiniteMeasure μ]
    {ℱ : Filtration ℝ mΩ} {M b : ℝ → Ω → ℝ} {T : ℝ} (hT : 0 ≤ T)
    (hM : Martingale M ℱ μ) (hb : StronglyAdapted ℱ b)
    (hcross : Integrable (fun p : ℝ × Ω => M T p.2 * b p.1 p.2)
      ((volume.restrict (Ioc 0 T)).prod μ)) :
    (∫ ω, M T ω * (∫ s in (0 : ℝ)..T, b s ω) ∂μ) =
      ∫ s in (0 : ℝ)..T, ∫ ω, M s ω * b s ω ∂μ := by
  calc
    (∫ ω, M T ω * (∫ s in (0 : ℝ)..T, b s ω) ∂μ) =
        ∫ ω, (∫ s in (0 : ℝ)..T, M T ω * b s ω) ∂μ := by
      simp only [intervalIntegral.integral_const_mul]
    _ = ∫ s in (0 : ℝ)..T, ∫ ω, M T ω * b s ω ∂μ :=
      DiscrepancyEnergy.integral_timePrimitive ⟨hT, le_rfl⟩ hcross
    _ = ∫ s in (0 : ℝ)..T, ∫ ω, M s ω * b s ω ∂μ := by
      apply intervalIntegral.integral_congr_ae
      have hint : ∀ᵐ s : ℝ, s ∈ Ioc 0 T →
          Integrable (fun ω => M T ω * b s ω) μ :=
        (ae_restrict_iff' measurableSet_Ioc).1 hcross.prod_right_ae
      filter_upwards [hint] with s hs hmem
      have hst : s ∈ Ioc 0 T := by simpa only [uIoc_of_le hT] using hmem
      exact integral_mul_past_eq hM hst.2 (hb s) (hs hst)

theorem integrable_martingale_mul_timeIntegral [SFinite μ]
    {M b : ℝ → Ω → ℝ} {T : ℝ} (hT : 0 ≤ T)
    (hcross : Integrable (fun p : ℝ × Ω => M T p.2 * b p.1 p.2)
      ((volume.restrict (Ioc 0 T)).prod μ)) :
    Integrable (fun ω => M T ω * (∫ s in (0 : ℝ)..T, b s ω)) μ := by
  have h := hcross.integral_prod_right
  simpa only [← intervalIntegral.integral_of_le hT,
    intervalIntegral.integral_const_mul] using h

theorem integrable_diagonal_mul_of_terminal [IsFiniteMeasure μ]
    {ℱ : Filtration ℝ mΩ} {M b : ℝ → Ω → ℝ} {T : ℝ}
    (hM : Martingale M ℱ μ) (hb : StronglyAdapted ℱ b)
    (hmeas : AEStronglyMeasurable (fun p : ℝ × Ω => M p.1 p.2 * b p.1 p.2)
      ((volume.restrict (Ioc 0 T)).prod μ))
    (hcross : Integrable (fun p : ℝ × Ω => M T p.2 * b p.1 p.2)
      ((volume.restrict (Ioc 0 T)).prod μ)) :
    Integrable (fun p : ℝ × Ω => M p.1 p.2 * b p.1 p.2)
      ((volume.restrict (Ioc 0 T)).prod μ) := by
  apply (integrable_prod_iff hmeas).2
  constructor
  · filter_upwards [hcross.prod_right_ae, ae_restrict_mem measurableSet_Ioc] with s hs hmem
    exact integrable_mul_past hM hmem.2 (hb s) hs
  · apply hcross.integral_norm_prod_left.mono' hmeas.norm.integral_prod_right'
    filter_upwards [hcross.prod_right_ae, ae_restrict_mem measurableSet_Ioc] with s hs hmem
    simpa only [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun _ => abs_nonneg _))] using
      integral_abs_mul_past_le hM hmem.2 (hb s) hs

theorem integral_sq_martingale_add_timeIntegral [IsFiniteMeasure μ]
    {ℱ : Filtration ℝ mΩ} {M b : ℝ → Ω → ℝ} {T : ℝ} (hT : 0 ≤ T)
    (hM : Martingale M ℱ μ) (hb : StronglyAdapted ℱ b)
    (hM2 : Integrable (fun ω => (M T ω) ^ 2) μ)
    (hbInt : Integrable (fun p : ℝ × Ω => b p.1 p.2)
      ((volume.restrict (Ioc 0 T)).prod μ))
    (hcross : Integrable (fun p : ℝ × Ω => M T p.2 * b p.1 p.2)
      ((volume.restrict (Ioc 0 T)).prod μ))
    (hmeas : AEStronglyMeasurable (fun p : ℝ × Ω => M p.1 p.2 * b p.1 p.2)
      ((volume.restrict (Ioc 0 T)).prod μ))
    (hAb : Integrable (fun p : ℝ × Ω =>
      (∫ u in (0 : ℝ)..p.1, b u p.2) * b p.1 p.2)
      ((volume.restrict (Ioc 0 T)).prod μ)) :
    Integrable (fun ω => (M T ω + ∫ s in (0 : ℝ)..T, b s ω) ^ 2) μ ∧
    (∫ ω, (M T ω + ∫ s in (0 : ℝ)..T, b s ω) ^ 2 ∂μ) =
      (∫ ω, (M T ω) ^ 2 ∂μ) +
        2 * ∫ s in (0 : ℝ)..T,
          ∫ ω, (M s ω + ∫ u in (0 : ℝ)..s, b u ω) * b s ω ∂μ := by
  have hA2 := DiscrepancyEnergy.integrable_timePrimitive_sq ⟨hT, le_rfl⟩ hbInt hAb
  have hMA := integrable_martingale_mul_timeIntegral hT hcross
  have hdiag := integrable_diagonal_mul_of_terminal hM hb hmeas hcross
  have hpoly : (fun ω => (M T ω + ∫ s in (0 : ℝ)..T, b s ω) ^ 2) =
      (fun ω => (M T ω) ^ 2 + 2 * (M T ω * (∫ s in (0 : ℝ)..T, b s ω)) +
        (∫ s in (0 : ℝ)..T, b s ω) ^ 2) := by
    funext ω
    ring
  have hsum : (∫ s in (0 : ℝ)..T,
      ∫ ω, (M s ω + ∫ u in (0 : ℝ)..s, b u ω) * b s ω ∂μ) =
      (∫ s in (0 : ℝ)..T, ∫ ω, M s ω * b s ω ∂μ) +
      (∫ s in (0 : ℝ)..T,
        ∫ ω, (∫ u in (0 : ℝ)..s, b u ω) * b s ω ∂μ) := by
    simp only [intervalIntegral.integral_of_le hT]
    calc
      (∫ s in Ioc 0 T, ∫ ω,
          (M s ω + ∫ u in (0 : ℝ)..s, b u ω) * b s ω ∂μ) =
          ∫ s in Ioc 0 T, (∫ ω, M s ω * b s ω ∂μ) +
            ∫ ω, (∫ u in (0 : ℝ)..s, b u ω) * b s ω ∂μ := by
        apply integral_congr_ae
        filter_upwards [hdiag.prod_right_ae, hAb.prod_right_ae] with s hs hAs
        simp only [add_mul]
        exact integral_add hs hAs
      _ = _ := integral_add hdiag.integral_prod_left hAb.integral_prod_left
  constructor
  · rw [hpoly]
    exact (hM2.add (hMA.const_mul 2)).add hA2
  · have hfirst : Integrable (fun ω => (M T ω) ^ 2 +
        2 * (M T ω * (∫ s in (0 : ℝ)..T, b s ω))) μ :=
      hM2.add (hMA.const_mul 2)
    rw [hpoly, integral_add hfirst hA2,
      integral_add hM2 (hMA.const_mul 2), integral_const_mul,
      integral_martingale_mul_timeIntegral hT hM hb hcross,
      DiscrepancyEnergy.integral_timePrimitive_sq ⟨hT, le_rfl⟩ hbInt hAb, hsum]
    ring

theorem integral_sq_of_compensatedSquare [IsFiniteMeasure μ]
    {ℱ : Filtration ℝ mΩ} {M q : ℝ → Ω → ℝ} {T t : ℝ}
    (ht : t ∈ Icc 0 T)
    (hq : Integrable (fun p : ℝ × Ω => q p.1 p.2)
      ((volume.restrict (Ioc 0 T)).prod μ))
    (hcomp : Martingale
      (fun s ω => (M s ω) ^ 2 - ∫ u in (0 : ℝ)..s, q u ω) ℱ μ) :
    Integrable (fun ω => (M t ω) ^ 2) μ ∧
      (∫ ω, (M t ω) ^ 2 ∂μ) = (∫ ω, (M 0 ω) ^ 2 ∂μ) +
        ∫ s in (0 : ℝ)..t, ∫ ω, q s ω ∂μ := by
  have hqt : Integrable (fun p : ℝ × Ω => q p.1 p.2)
      ((volume.restrict (Ioc 0 t)).prod μ) :=
    hq.mono_measure (Measure.prod_mono
      (Measure.restrict_mono_set _ (Ioc_subset_Ioc_right ht.2)) le_rfl)
  have hprim : Integrable (fun ω => ∫ s in (0 : ℝ)..t, q s ω) μ := by
    simpa only [intervalIntegral.integral_of_le ht.1] using hqt.integral_prod_right
  have hM2 : Integrable (fun ω => (M t ω) ^ 2) μ := by
    have h : Integrable (fun ω => ((M t ω) ^ 2 -
        (∫ u in (0 : ℝ)..t, q u ω)) + (∫ u in (0 : ℝ)..t, q u ω)) μ :=
      (hcomp.integrable t).add hprim
    simpa only [sub_add_cancel] using h
  have hmean : (∫ ω, (M t ω) ^ 2 - (∫ s in (0 : ℝ)..t, q s ω) ∂μ) =
      ∫ ω, (M 0 ω) ^ 2 ∂μ := by
    calc
      (∫ ω, (M t ω) ^ 2 - (∫ s in (0 : ℝ)..t, q s ω) ∂μ) =
          ∫ ω, μ[(fun ω => (M t ω) ^ 2 - ∫ s in (0 : ℝ)..t, q s ω) | ℱ 0] ω ∂μ :=
        (integral_condExp (ℱ.le 0)).symm
      _ = ∫ ω, (M 0 ω) ^ 2 - (∫ s in (0 : ℝ)..0, q s ω) ∂μ :=
        integral_congr_ae (hcomp.condExp_ae_eq ht.1)
      _ = ∫ ω, (M 0 ω) ^ 2 ∂μ := by simp
  rw [integral_sub hM2 hprim, DiscrepancyEnergy.integral_timePrimitive ht hq] at hmean
  exact ⟨hM2, by linarith⟩

theorem integrable_terminal_mul_of_later_terminal [IsFiniteMeasure μ]
    {ℱ : Filtration ℝ mΩ} {M b : ℝ → Ω → ℝ} {T t : ℝ} (ht : t ≤ T)
    (hM : Martingale M ℱ μ) (hb : StronglyAdapted ℱ b)
    (hbMeas : AEStronglyMeasurable (fun p : ℝ × Ω => b p.1 p.2)
      ((volume.restrict (Ioc 0 t)).prod μ))
    (hcross : Integrable (fun p : ℝ × Ω => M T p.2 * b p.1 p.2)
      ((volume.restrict (Ioc 0 T)).prod μ)) :
    Integrable (fun p : ℝ × Ω => M t p.2 * b p.1 p.2)
      ((volume.restrict (Ioc 0 t)).prod μ) := by
  have hcross' : Integrable (fun p : ℝ × Ω => M T p.2 * b p.1 p.2)
      ((volume.restrict (Ioc 0 t)).prod μ) :=
    hcross.mono_measure (Measure.prod_mono
      (Measure.restrict_mono_set _ (Ioc_subset_Ioc_right ht)) le_rfl)
  have hMt : StronglyMeasurable (fun p : ℝ × Ω => M t p.2) :=
    ((hM.stronglyAdapted t).mono (ℱ.le t)).comp_snd
  have hmeas : AEStronglyMeasurable (fun p : ℝ × Ω => M t p.2 * b p.1 p.2)
      ((volume.restrict (Ioc 0 t)).prod μ) := hMt.aestronglyMeasurable.mul hbMeas
  apply (integrable_prod_iff hmeas).2
  constructor
  · filter_upwards [hcross'.prod_right_ae, ae_restrict_mem measurableSet_Ioc] with s hs hmem
    exact integrable_mul_past hM ht ((hb s).mono (ℱ.mono hmem.2)) hs
  · apply hcross'.integral_norm_prod_left.mono' hmeas.norm.integral_prod_right'
    filter_upwards [hcross'.prod_right_ae, ae_restrict_mem measurableSet_Ioc] with s hs hmem
    simpa only [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun _ => abs_nonneg _))] using
      integral_abs_mul_past_le hM ht ((hb s).mono (ℱ.mono hmem.2)) hs

theorem expectedSquare_ac_and_deriv [IsFiniteMeasure μ]
    {ℱ : Filtration ℝ mΩ} {M b q : ℝ → Ω → ℝ} {T : ℝ} (hT : 0 ≤ T)
    (hM : Martingale M ℱ μ) (hb : StronglyAdapted ℱ b)
    (hcomp : Martingale
      (fun t ω => (M t ω) ^ 2 - ∫ s in (0 : ℝ)..t, q s ω) ℱ μ)
    (hq : Integrable (fun p : ℝ × Ω => q p.1 p.2)
      ((volume.restrict (Ioc 0 T)).prod μ))
    (hbInt : Integrable (fun p : ℝ × Ω => b p.1 p.2)
      ((volume.restrict (Ioc 0 T)).prod μ))
    (hcross : Integrable (fun p : ℝ × Ω => M T p.2 * b p.1 p.2)
      ((volume.restrict (Ioc 0 T)).prod μ))
    (hmeas : AEStronglyMeasurable (fun p : ℝ × Ω => M p.1 p.2 * b p.1 p.2)
      ((volume.restrict (Ioc 0 T)).prod μ))
    (hAb : Integrable (fun p : ℝ × Ω =>
      (∫ u in (0 : ℝ)..p.1, b u p.2) * b p.1 p.2)
      ((volume.restrict (Ioc 0 T)).prod μ)) :
    AbsolutelyContinuousOnInterval
      (fun t => ∫ ω, (M t ω + ∫ s in (0 : ℝ)..t, b s ω) ^ 2 ∂μ) 0 T ∧
      (∀ᵐ t ∂volume.restrict (Icc 0 T),
        deriv (fun t => ∫ ω, (M t ω + ∫ s in (0 : ℝ)..t, b s ω) ^ 2 ∂μ) t =
          (∫ ω, q t ω ∂μ) +
            2 * ∫ ω, (M t ω + ∫ s in (0 : ℝ)..t, b s ω) * b t ω ∂μ) := by
  have hdiag := integrable_diagonal_mul_of_terminal hM hb hmeas hcross
  have hXb : Integrable (fun p : ℝ × Ω =>
      (M p.1 p.2 + ∫ u in (0 : ℝ)..p.1, b u p.2) * b p.1 p.2)
      ((volume.restrict (Ioc 0 T)).prod μ) := by
    have hi : Integrable (fun p : ℝ × Ω => M p.1 p.2 * b p.1 p.2 +
        (∫ u in (0 : ℝ)..p.1, b u p.2) * b p.1 p.2)
        ((volume.restrict (Ioc 0 T)).prod μ) := hdiag.add hAb
    simpa only [add_mul] using hi
  have hk := (DiscrepancyEnergy.intervalIntegrable_mean hT hq).add
    ((DiscrepancyEnergy.intervalIntegrable_mean
      (E := fun s ω => (M s ω + ∫ u in (0 : ℝ)..s, b u ω) * b s ω) hT hXb).const_mul 2)
  have hrep : ∀ t ∈ Icc 0 T,
      (∫ ω, (M t ω + ∫ s in (0 : ℝ)..t, b s ω) ^ 2 ∂μ) =
        (∫ ω, (M 0 ω) ^ 2 ∂μ) + ∫ s in (0 : ℝ)..t,
          (∫ ω, q s ω ∂μ) +
            2 * ∫ ω, (M s ω + ∫ u in (0 : ℝ)..s, b u ω) * b s ω ∂μ := by
    intro t ht
    have hmeasure : ((volume.restrict (Ioc 0 t)).prod μ) ≤
        ((volume.restrict (Ioc 0 T)).prod μ) :=
      Measure.prod_mono (Measure.restrict_mono_set _ (Ioc_subset_Ioc_right ht.2)) le_rfl
    obtain ⟨hM2, hMmean⟩ := integral_sq_of_compensatedSquare ht hq hcomp
    have hcrossT := integrable_terminal_mul_of_later_terminal ht.2 hM hb
      (hbInt.aestronglyMeasurable.mono_measure hmeasure) hcross
    have hfull := (integral_sq_martingale_add_timeIntegral ht.1 hM hb hM2
      (hbInt.mono_measure hmeasure) hcrossT (hmeas.mono_measure hmeasure)
      (hAb.mono_measure hmeasure)).2
    have hqi := DiscrepancyEnergy.intervalIntegrable_mean ht.1 (hq.mono_measure hmeasure)
    have hbi := DiscrepancyEnergy.intervalIntegrable_mean
      (E := fun s ω => (M s ω + ∫ u in (0 : ℝ)..s, b u ω) * b s ω) ht.1
      (hXb.mono_measure hmeasure)
    rw [hfull, hMmean, intervalIntegral.integral_add hqi (hbi.const_mul 2),
      intervalIntegral.integral_const_mul]
    ring
  exact ⟨DiscrepancyEnergy.absolutelyContinuousOnInterval_of_integral_representation hk
      (by simpa only [uIcc_of_le hT] using hrep),
    DiscrepancyEnergy.ae_deriv_of_integral_representation hT hk hrep⟩

end Problem367.MartingaleDriftEnergy

end

end OAI
