import OAI.Geometry.Perimeter.Regularity.PairedCutTest

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
open scoped Topology ENNReal NNReal
open scoped ENNReal Topology ContDiff Pointwise
open scoped Topology ENNReal ContDiff
namespace RPISingularHarnack

theorem integral_divergence_eq_zero {n : ℕ} {V : Euc n → Euc n}
    (hV : ContDiff ℝ ∞ V) (hcV : HasCompactSupport V) :
    (∫ x, divergence V x) = 0 := by
  let b := EuclideanSpace.basisFun (Fin n) ℝ
  let v : Fin n → Euc n → ℝ := fun i x ↦ inner ℝ (b i) (V x)
  have hv : ∀ i, ContDiff ℝ ∞ (v i) := fun i ↦ (innerSL ℝ (b i)).contDiff.comp hV
  have hcv : ∀ i, HasCompactSupport (v i) := fun i ↦ hcV.comp_left (by simp)
  have hdv : ∀ i x, fderiv ℝ (v i) x (b i) =
      inner ℝ (b i) (fderiv ℝ V x (b i)) := by
    intro i x
    have h := ((innerSL ℝ (b i)).hasFDerivAt.comp x
      (hV.differentiable (by simp) x).hasFDerivAt).fderiv
    exact congrArg (fun L : Euc n →L[ℝ] ℝ ↦ L (b i)) h
  have hInt : ∀ i, Integrable (fun x ↦ fderiv ℝ (v i) x (b i)) volume := by
    intro i
    exact (((hv i).continuous_fderiv (by simp)).clm_apply continuous_const).integrable_of_hasCompactSupport
      ((hcv i).fderiv_apply ℝ (b i))
  have hz : ∀ i, (∫ x, fderiv ℝ (v i) x (b i)) = 0 := by
    intro i
    have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
      (f := fun _ : Euc n ↦ (1 : ℝ)) (g := v i) (v := b i) (μ := volume)
      (by simp)
      (by simpa using hInt i)
      (by simpa using (hv i).continuous.integrable_of_hasCompactSupport (hcv i))
      (fun _ _ ↦ differentiableAt_const _) (fun x _ ↦ (hv i).differentiable (by simp) x)
    simpa using h
  calc
    (∫ x, divergence V x) = ∫ x, ∑ i, fderiv ℝ (v i) x (b i) := by
      congr 1
      funext x
      simp only [divergence, hdv, b]
    _ = ∑ i, ∫ x, fderiv ℝ (v i) x (b i) := integral_finsetSum _ (fun i _ ↦ hInt i)
    _ = 0 := by simp only [hz, Finset.sum_const_zero]

theorem divergence_neg {n : ℕ} {V : Euc n → Euc n}
    (hV : Differentiable ℝ V) : divergence (-V) = -divergence V := by
  funext x
  simp only [divergence, (hV x).hasFDerivAt.neg.fderiv, neg_apply,
    inner_neg_right, Finset.sum_neg_distrib, Pi.neg_apply]

theorem perimeterAdmissible_neg {n : ℕ} {U : Set (Euc n)} {V : Euc n → Euc n}
    (hV : PerimeterAdmissible U V) : PerimeterAdmissible U (-V) := by
  exact ⟨hV.1.neg, hV.2.1.neg, by simpa using hV.2.2.1,
    fun x ↦ by simpa using hV.2.2.2 x⟩

theorem raw_perimeter_compl_le {n : ℕ} {E : Set (Euc n)} (hE : MeasurableSet E)
    (U : Set (Euc n)) : perimeter Eᶜ U ≤ perimeter E U := by
  rw [perimeter_eq_iSup_tests]
  refine iSup_le fun V ↦ iSup_le fun hV ↦ ?_
  have hsplit := integral_add_compl hE (integrable_divergence hV.1 hV.2.1)
  rw [integral_divergence_eq_zero hV.1 hV.2.1] at hsplit
  have heq : (∫ x in Eᶜ, divergence V x) = ∫ x in E, divergence (-V) x := by
    simp only [divergence_neg (hV.1.differentiable (by simp)), Pi.neg_apply, integral_neg]
    linarith
  rw [heq, perimeter_eq_iSup_tests]
  exact le_iSup_of_le (-V) (le_iSup_of_le (perimeterAdmissible_neg hV) le_rfl)

theorem raw_perimeter_compl {n : ℕ} {E : Set (Euc n)} (hE : MeasurableSet E)
    (U : Set (Euc n)) : perimeter Eᶜ U = perimeter E U := by
  apply le_antisymm (raw_perimeter_compl_le hE U)
  simpa only [compl_compl] using raw_perimeter_compl_le hE.compl U

theorem perimeterSupport_compl {n : ℕ} {E : Set (Euc n)} (hE : MeasurableSet E) :
    perimeterSupport Eᶜ = perimeterSupport E := by
  ext x
  simp only [perimeterSupport, mem_ofPred_eq, raw_perimeter_compl hE]

theorem isLocallyPerimeterMinimizing_compl {n : ℕ} {E : Set (Euc n)}
    (hmin : IsLocallyPerimeterMinimizing E) : IsLocallyPerimeterMinimizing Eᶜ := by
  refine ⟨hmin.1.compl, ?_, ?_⟩
  · intro x r hr
    rw [raw_perimeter_compl hmin.1]
    exact hmin.2.1 x r hr
  · intro x r hr F hF hc hs
    have heq : symmDiff E Fᶜ = symmDiff Eᶜ F := by
      ext y
      simp only [mem_symmDiff, mem_compl_iff]
      tauto
    have h := hmin.2.2 x r hr Fᶜ hF.compl (by simpa only [heq] using hc)
      (by simpa only [heq] using hs)
    simpa only [raw_perimeter_compl hmin.1, raw_perimeter_compl hF] using h

theorem raw_perimeter_eq_zero_of_volume_inter_eq_zero {n : ℕ} {E U : Set (Euc n)}
    (hU : MeasurableSet U) (hnull : volume (E ∩ U) = 0) : perimeter E U = 0 := by
  apply le_antisymm _ bot_le
  rw [perimeter_eq_iSup_tests]
  refine iSup_le fun V ↦ iSup_le fun hV ↦ ?_
  have hzero : divergence V =ᵐ[volume.restrict E] 0 := by
    have hnonmem : ∀ᵐ x ∂volume.restrict E, x ∉ U := by
      rw [ae_iff]
      simp only [not_not]
      change (volume.restrict E) U = 0
      rw [Measure.restrict_apply hU, inter_comm]
      exact hnull
    filter_upwards [hnonmem] with x hx
    exact image_eq_zero_of_notMem_tsupport
      (fun h ↦ hx (hV.2.2.1 (tsupport_divergence_subset V h)))
  rw [integral_congr_ae hzero]
  simp

theorem minimizing_two_phase_volume_lower {n : ℕ} {p : ℝ}
    (hp : Real.HolderConjugate (n : ℝ) p) {R : ℝ} (hR : 0 < R) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ E : Set (Euc n), IsLocallyPerimeterMinimizing E →
      ∀ c ∈ perimeterSupport E,
        ε < volume.real (E ∩ Metric.closedBall c R) ∧
        ε < volume.real (Eᶜ ∩ Metric.closedBall c R) := by
  obtain ⟨ε, hε, hclear⟩ := minimizing_clearing_out hp hR
  have hphase : ∀ E : Set (Euc n), IsLocallyPerimeterMinimizing E →
      ∀ c ∈ perimeterSupport E, ε < volume.real (E ∩ Metric.closedBall c R) := by
    intro E hmin c hc
    by_contra h
    have hz := hclear E hmin c (le_of_not_gt h)
    have hpz := raw_perimeter_eq_zero_of_volume_inter_eq_zero measurableSet_ball
      (measure_mono_null (inter_subset_inter_right E Metric.ball_subset_closedBall) hz)
    have hpos := hc (R / 2) (by positivity)
    rw [hpz] at hpos
    exact (lt_irrefl _ hpos)
  refine ⟨ε, hε, ?_⟩
  intro E hmin c hc
  exact ⟨hphase E hmin c hc, hphase Eᶜ (isLocallyPerimeterMinimizing_compl hmin) c
    (by simpa only [perimeterSupport_compl hmin.1] using hc)⟩

end RPISingularHarnack

end

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
open scoped Topology ENNReal NNReal
open scoped ENNReal Topology ContDiff Pointwise
open scoped Topology ENNReal ContDiff
namespace RPISingularHarnack

theorem holder_volume_scale {n : ℕ} {p R : ℝ}
    (hp : Real.HolderConjugate (n : ℝ) p) (hR : 0 < R) :
    (R ^ (n : ℝ) / R) ^ p = R ^ (n : ℝ) := by
  rw [← Real.rpow_sub_one hR.ne', ← Real.rpow_mul hR.le, hp.sub_one_mul_conj]

theorem minimizing_scaled_clearing_out {n : ℕ} {p : ℝ}
    (hp : Real.HolderConjugate (n : ℝ) p) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ E : Set (Euc n), IsLocallyPerimeterMinimizing E →
      ∀ c : Euc n, ∀ R : ℝ, 0 < R →
      volume.real (E ∩ Metric.closedBall c R) ≤ ε * R ^ n →
        volume (E ∩ Metric.closedBall c (R / 2)) = 0 := by
  obtain ⟨L, hL, hbound⟩ := exists_smoothTransition_deriv_bound
  let S : ℝ := lintegralPowLePowLIntegralFDerivConst (volume : Measure (Euc n)) p
  let K : ℝ := 64 * L
  let C : ℝ := (S + 1) * K ^ p
  let B : ℝ := (2 : ℝ) ^ p
  have hS : 0 ≤ S := NNReal.coe_nonneg _
  have hK : 0 < K := by dsimp [K]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  have hp1 : 1 < p := hp.symm.lt
  have hB : 1 < B := Real.one_lt_rpow (by norm_num) (by linarith)
  obtain ⟨ε, hε, hiteration⟩ := nonlinear_iteration_tendsto_zero hp1 hC hB
  refine ⟨ε, hε, ?_⟩
  intro E hmin c R hR hsmall
  let Q : ℝ := R ^ n
  have hQ : 0 < Q := pow_pos hR n
  have hscale : (Q / R) ^ p = Q := by
    simpa only [Q, Real.rpow_natCast] using holder_volume_scale hp hR
  let u : ℕ → ℝ := fun i ↦ volume.real (E ∩ Metric.closedBall c (clearingRadius R i)) / Q
  have hu : ∀ i, 0 ≤ u i := fun _ ↦ div_nonneg ENNReal.toReal_nonneg hQ.le
  have hstart : u 0 ≤ ε := by
    dsimp [u]
    rw [clearingRadius_zero]
    exact (div_le_iff₀ hQ).mpr hsmall
  have hstep : ∀ i, u (i + 1) ≤ C * B ^ i * (u i) ^ p := by
    intro i
    have hm := minimizing_volume_recursion hp hmin c (clearingRadius_pos hR (i + 1))
      (clearingRadius_succ_lt hR i) hL hbound
    have heq : 16 * L * volume.real (E ∩ Metric.closedBall c (clearingRadius R i)) /
        (clearingRadius R i - clearingRadius R (i + 1)) =
        (K * (2 : ℝ) ^ i * u i) * (Q / R) := by
      rw [clearingRadius_sub_succ]
      dsimp [K, u]
      field_simp
      ring
    change volume.real (E ∩ Metric.closedBall c (clearingRadius R (i + 1))) ≤ S * _ at hm
    rw [heq, Real.mul_rpow (by positivity) (by positivity), hscale] at hm
    have hpow : ((2 : ℝ) ^ i) ^ p = ((2 : ℝ) ^ p) ^ i := by
      rw [← Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 2),
        mul_comm (i : ℝ), Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2)]
    calc
      u (i + 1) ≤ S * (K * (2 : ℝ) ^ i * u i) ^ p := by
        exact (div_le_iff₀ hQ).mpr (by simpa only [mul_assoc] using hm)
      _ = (S * K ^ p) * B ^ i * (u i) ^ p := by
        rw [Real.mul_rpow (by positivity) (hu i),
          Real.mul_rpow hK.le (by positivity), hpow]
        dsimp [B]
        ring
      _ ≤ C * B ^ i * (u i) ^ p := by
        unfold C
        gcongr
        linarith
  have ht := hiteration u hu hstart hstep
  have hzero : volume.real (E ∩ Metric.closedBall c (R / 2)) / Q = 0 := by
    apply le_antisymm _ (div_nonneg ENNReal.toReal_nonneg hQ.le)
    apply ge_of_tendsto ht
    apply Eventually.of_forall
    intro i
    exact div_le_div_of_nonneg_right (measureReal_mono
      (inter_subset_inter_right E (Metric.closedBall_subset_closedBall (clearingRadius_half_le hR.le i)))
      (measure_ne_top_of_subset inter_subset_right (isCompact_closedBall c (clearingRadius R i)).measure_ne_top)) hQ.le
  have hvol : volume.real (E ∩ Metric.closedBall c (R / 2)) = 0 := (div_eq_zero_iff).mp hzero |>.resolve_right hQ.ne'
  exact ((ENNReal.toReal_eq_zero_iff _).mp hvol).resolve_right
    (measure_ne_top_of_subset inter_subset_right (isCompact_closedBall c (R / 2)).measure_ne_top)

theorem minimizing_scaled_two_phase_volume_lower {n : ℕ} {p : ℝ}
    (hp : Real.HolderConjugate (n : ℝ) p) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ E : Set (Euc n), IsLocallyPerimeterMinimizing E →
      ∀ c ∈ perimeterSupport E, ∀ R : ℝ, 0 < R →
        ε * R ^ n < volume.real (E ∩ Metric.closedBall c R) ∧
        ε * R ^ n < volume.real (Eᶜ ∩ Metric.closedBall c R) := by
  obtain ⟨ε, hε, hclear⟩ := minimizing_scaled_clearing_out hp
  have hphase : ∀ E : Set (Euc n), IsLocallyPerimeterMinimizing E →
      ∀ c ∈ perimeterSupport E, ∀ R : ℝ, 0 < R →
        ε * R ^ n < volume.real (E ∩ Metric.closedBall c R) := by
    intro E hmin c hc R hR
    by_contra h
    have hz := hclear E hmin c R hR (le_of_not_gt h)
    have hpz := raw_perimeter_eq_zero_of_volume_inter_eq_zero measurableSet_ball
      (measure_mono_null (inter_subset_inter_right E Metric.ball_subset_closedBall) hz)
    have hpos := hc (R / 2) (by positivity)
    rw [hpz] at hpos
    exact (lt_irrefl _ hpos)
  refine ⟨ε, hε, ?_⟩
  intro E hmin c hc R hR
  exact ⟨hphase E hmin c hc R hR, hphase Eᶜ (isLocallyPerimeterMinimizing_compl hmin) c
    (by simpa only [perimeterSupport_compl hmin.1] using hc) R hR⟩

end RPISingularHarnack

end

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
open scoped Topology ENNReal NNReal
open scoped ENNReal Topology ContDiff Pointwise
open scoped Topology ENNReal ContDiff
namespace RPISingularHarnack

theorem indicator_one_locallyIntegrable {n : ℕ} {E : Set (Euc n)}
    (hE : MeasurableSet E) : LocallyIntegrable (E.indicator (fun _ ↦ (1 : ℝ))) volume := by
  apply (locallyIntegrable_const (μ := (volume : Measure (Euc n))) (1 : ℝ)).mono
    (measurable_const.indicator hE).aestronglyMeasurable
  exact ae_of_all _ fun x ↦ by
    by_cases hx : x ∈ E <;> simp [hx]

theorem average_indicator_one_closedBall {n : ℕ} {E : Set (Euc n)}
    (hE : MeasurableSet E) (c : Euc n) (R : ℝ) :
    (⨍ x in Metric.closedBall c R, E.indicator (fun _ ↦ (1 : ℝ)) x) =
      volume.real (E ∩ Metric.closedBall c R) / volume.real (Metric.closedBall c R) := by
  rw [setAverage_eq, integral_indicator hE, Measure.restrict_restrict hE,
    integral_const, smul_eq_mul, smul_eq_mul]
  simp only [measureReal_restrict_apply_univ, one_mul, div_eq_mul_inv, mul_comm]

theorem minimizing_phaseSupport_volume_lower {n : ℕ} {p : ℝ}
    (hp : Real.HolderConjugate (n : ℝ) p) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ E : Set (Euc n), IsLocallyPerimeterMinimizing E →
      ∀ c ∈ (volume.restrict E).support, ∀ R : ℝ, 0 < R →
        ε * R ^ n < volume.real (E ∩ Metric.closedBall c R) := by
  obtain ⟨ε, hε, hclear⟩ := minimizing_scaled_clearing_out hp
  refine ⟨ε, hε, ?_⟩
  intro E hmin c hc R hR
  by_contra h
  have hz := hclear E hmin c R hR (le_of_not_gt h)
  have hpos := (Metric.nhds_basis_ball.mem_measureSupport (μ := volume.restrict E)).mp hc
    (R / 2) (by positivity)
  rw [Measure.restrict_apply measurableSet_ball, inter_comm] at hpos
  have hnull := measure_mono_null (inter_subset_inter_right E Metric.ball_subset_closedBall) hz
  exact hpos.ne' hnull

theorem minimizing_ae_eq_phaseSupport {n : ℕ} {p : ℝ}
    (hp : Real.HolderConjugate (n : ℝ) p) {E : Set (Euc n)}
    (hmin : IsLocallyPerimeterMinimizing E) : E =ᵐ[volume] (volume.restrict E).support := by
  obtain ⟨ε, hε, hlower⟩ := minimizing_phaseSupport_volume_lower hp
  let omegaVol : ℝ := volume.real (Metric.ball (0 : Euc n) 1)
  have homegaVol : 0 < omegaVol := by
    exact ENNReal.toReal_pos (Metric.measure_ball_pos volume (0 : Euc n) (by norm_num)).ne'
      measure_ball_lt_top.ne
  have hmean : ∀ c ∈ (volume.restrict E).support, ∀ R : ℝ, 0 < R →
      ε / omegaVol ≤ ⨍ x in Metric.closedBall c R, E.indicator (fun _ ↦ (1 : ℝ)) x := by
    intro c hc R hR
    rw [average_indicator_one_closedBall hmin.1,
      Measure.addHaar_real_closedBall volume c hR.le]
    simp only [finrank_euclideanSpace, Fintype.card_fin]
    calc
      ε / omegaVol = (ε * R ^ n) / (R ^ n * omegaVol) := by field_simp [hR.ne', homegaVol.ne']
      _ ≤ volume.real (E ∩ Metric.closedBall c R) / (R ^ n * omegaVol) :=
        div_le_div_of_nonneg_right (hlower E hmin c hc R hR).le (by positivity)
  have hmem : ∀ᵐ x ∂volume, x ∈ E → x ∈ (volume.restrict E).support :=
    (ae_restrict_iff' hmin.1).mp (volume.restrict E).support_mem_ae
  have hdiff := IsUnifLocDoublingMeasure.ae_tendsto_average volume
    (indicator_one_locallyIntegrable hmin.1) (1 : ℝ)
  filter_upwards [hmem, hdiff] with x hmem hdiff
  apply propext
  constructor
  · exact hmem
  · intro hx
    by_contra hxE
    have ht := hdiff (fun _ : ℝ ↦ x) (id : ℝ → ℝ) tendsto_id
      (by filter_upwards [self_mem_nhdsWithin] with R hR
          exact Metric.mem_closedBall_self (by simpa only [one_mul] using hR.le))
    simp only [indicator_of_notMem hxE] at ht
    have hle : ε / omegaVol ≤ (0 : ℝ) := ge_of_tendsto ht (by
      filter_upwards [self_mem_nhdsWithin] with R hR
      exact hmean x hx R hR)
    exact (div_pos hε homegaVol).not_ge hle

end RPISingularHarnack

end

end OAI
