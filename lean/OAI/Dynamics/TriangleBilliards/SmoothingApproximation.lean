import OAI.Dynamics.TriangleBilliards.SmoothingLp

namespace OAI

universe uAlpha uE

open MeasureTheory Set
open scoped ENNReal symmDiff
noncomputable section
open MeasureTheory Set Filter Function Metric
open scoped Topology Convolution ContDiff
noncomputable section
open MeasureTheory Set
open scoped ENNReal
noncomputable section

namespace TriangularBilliards.SpatialSmoothing
open Filter
open scoped Topology BoundedContinuousFunction

lemma rho_fderiv_neg (x : ℂ) : fderiv ℝ rho (-x) = -fderiv ℝ rho x := by
  have h := (rho_contDiff.differentiable (by simp) (-x)).hasFDerivAt.comp x
    (hasFDerivAt_id x).neg
  have he : (fun z : ℂ => rho (-z)) = rho := funext rho_neg
  change HasFDerivAt (fun z : ℂ => rho (-z)) _ x at h
  rw [he] at h
  have hh := h.fderiv
  simp only [ContinuousLinearMap.comp_neg, ContinuousLinearMap.comp_id] at hh
  rw [hh]
  simp

lemma rho_fderiv_integral : (∫ x : ℂ, fderiv ℝ rho x) = 0 := by
  have h := integral_neg_eq_self (fun x : ℂ => fderiv ℝ rho x) volume
  simp_rw [rho_fderiv_neg] at h
  rw [integral_neg] at h
  ext v
  have hv := congrArg (fun L : ℂ →L[ℝ] ℝ => L v) h
  simp only [neg_apply, zero_apply] at hv ⊢
  linarith

lemma rho_smulRight_integral (c : ℂ) :
    (∫ x : ℂ, (fderiv ℝ rho x).smulRight c) = 0 := by
  have h := ((ContinuousLinearMap.smulRightL ℝ ℂ ℂ).flip c).integral_comp_comm
    rho_fderiv_integrable
  change (∫ x : ℂ, (fderiv ℝ rho x).smulRight c) =
    (∫ x : ℂ, fderiv ℝ rho x).smulRight c at h
  simpa only [rho_fderiv_integral, ContinuousLinearMap.zero_smulRight] using h

lemma rescaled_gradient_continuous (f : ℂ →ᵇ ℂ) (x : ℂ) (ε : ℝ) :
    Continuous (fun y : ℂ => (fderiv ℝ rho y).smulRight (f (x - ε • y))) := by
  let L : (ℂ →L[ℝ] ℝ) →L[ℝ] ℂ →L[ℝ] ℂ →L[ℝ] ℂ :=
    ContinuousLinearMap.smulRightL ℝ ℂ ℂ
  have h₁ : Continuous (fun y : ℂ => L (fderiv ℝ rho y)) :=
    L.continuous.comp (rho_contDiff.continuous_fderiv (by simp))
  have h₂ : Continuous (fun y : ℂ => f (x - ε • y)) := by fun_prop
  exact h₁.clm_apply h₂

lemma rescaled_gradient_dominated (f : ℂ →ᵇ ℂ) (x : ℂ) (ε : ℝ) (y : ℂ) :
    ‖(fderiv ℝ rho y).smulRight (f (x - ε • y))‖ ≤ ‖fderiv ℝ rho y‖ * ‖f‖ := by
  rw [ContinuousLinearMap.norm_smulRight_apply]
  exact mul_le_mul_of_nonneg_left (f.norm_coe_le_norm _) (norm_nonneg _)

lemma rescaled_gradient_pointwise (f : ℂ →ᵇ ℂ) (x y : ℂ) :
    Tendsto (fun ε : ℝ => (fderiv ℝ rho y).smulRight (f (x - ε • y)))
      (𝓝 0) (𝓝 ((fderiv ℝ rho y).smulRight (f x))) := by
  let L : ℂ →L[ℝ] ℂ →L[ℝ] ℂ := (ContinuousLinearMap.smulRightL ℝ ℂ ℂ) (fderiv ℝ rho y)
  have h : Continuous (fun ε : ℝ => L (f (x - ε • y))) := by fun_prop
  have hL (c : ℂ) : L c = (fderiv ℝ rho y).smulRight c := by
    ext v
    rfl
  simp_rw [hL] at h
  have hh := h.continuousAt (x := (0 : ℝ))
  simpa only [zero_smul, sub_zero] using hh.tendsto

/-- Rescaled cancellation for a bounded spatially continuous input. This
is the elementary pointwise producer for the small scaled derivative. -/
lemma rescaled_gradient_tendsto (f : ℂ →ᵇ ℂ) (x : ℂ) :
    Tendsto (fun ε : ℝ => ∫ y : ℂ,
      (fderiv ℝ rho y).smulRight (f (x - ε • y))) (𝓝 0) (𝓝 0) := by
  have hi : Integrable (fun y : ℂ => ‖fderiv ℝ rho y‖ * ‖f‖) volume :=
    rho_fderiv_integrable.norm.mul_const ‖f‖
  have hlim : Tendsto (fun ε : ℝ => ∫ y : ℂ,
      (fderiv ℝ rho y).smulRight (f (x - ε • y))) (𝓝 0)
      (𝓝 (∫ y : ℂ, (fderiv ℝ rho y).smulRight (f x))) := by
    apply tendsto_integral_filter_of_dominated_convergence
      (fun y : ℂ => ‖fderiv ℝ rho y‖ * ‖f‖)
    · exact Eventually.of_forall fun ε => (rescaled_gradient_continuous f x ε).aestronglyMeasurable
    · exact Eventually.of_forall fun ε => Eventually.of_forall (rescaled_gradient_dominated f x ε)
    · exact hi
    · exact Eventually.of_forall (rescaled_gradient_pointwise f x)
  simpa only [rho_smulRight_integral] using hlim

/-- Exact substitution relating the rescaled derivative to the actual
first-derivative convolution kernel. -/
lemma scaled_full_gradient (ε : ℝ) (hε : 0 < ε) (f : ℂ → ℂ) (x : ℂ) :
    ε • (∫ y : ℂ, (fderiv ℝ (kernel ε) (x-y)).smulRight (f y)) =
      ∫ y : ℂ, (fderiv ℝ rho y).smulRight (f (x - ε • y)) := by
  rw [← integral_sub_left_eq_self
    (fun y : ℂ => (fderiv ℝ (kernel ε) (x-y)).smulRight (f y)) volume x]
  simp only [sub_sub_cancel]
  have hs := Measure.integral_comp_smul volume
    (fun y : ℂ => (fderiv ℝ (kernel ε) y).smulRight (f (x-y))) ε
  rw [Complex.finrank_real_complex, abs_of_nonneg (inv_nonneg.mpr (sq_nonneg ε))] at hs
  have he : (∫ y : ℂ, (fderiv ℝ (kernel ε) (ε • y)).smulRight (f (x-ε • y))) =
      (ε ^ 3)⁻¹ • (∫ y : ℂ, (fderiv ℝ rho y).smulRight (f (x-ε • y))) := by
    simp_rw [kernel_fderiv, smul_smul, inv_mul_cancel₀ hε.ne', one_smul]
    have hl (y : ℂ) : ((ε ^ 3)⁻¹ • fderiv ℝ rho y).smulRight (f (x - ε • y)) =
        (ε ^ 3)⁻¹ • (fderiv ℝ rho y).smulRight (f (x - ε • y)) := by
      ext v
      simp only [ContinuousLinearMap.smulRight_apply, smul_apply, smul_eq_mul,
        smul_smul]
    simp only [hl, integral_smul]
  rw [he] at hs
  have heq := congrArg (fun u : ℂ →L[ℝ] ℂ => ε ^ 3 • u) hs
  simp only [smul_smul] at heq
  have h₁ : ε ^ 3 * (ε ^ 3)⁻¹ = 1 := mul_inv_cancel₀ (pow_ne_zero _ hε.ne')
  have h₂ : ε ^ 3 * (ε ^ 2)⁻¹ = ε := by field_simp
  simpa only [h₁, h₂, one_smul] using heq.symm

end TriangularBilliards.SpatialSmoothing

namespace TriangularBilliards
open Filter SpatialSmoothing
open scoped Topology BoundedContinuousFunction

lemma kernel_fderiv_eq_zero {ε : ℝ} (hε : 0 < ε) {x : ℂ} (hx : ε < ‖x‖) :
    fderiv ℝ (kernel ε) x = 0 := by
  by_contra hn
  have hm := support_fderiv_subset ℝ (f := kernel ε) hn
  rw [tsupport, kernel_support hε, closure_ball _ hε.ne', mem_closedBall_zero_iff] at hm
  exact (not_le_of_gt hx) hm

lemma directGradS_eq_full (Q : Triangle) {ε : ℝ} (hε : 0 < ε)
    (f : SmoothPhase → ℂ) (z : SmoothPhase) (hz : closedBall z.1.1 ε ⊆ Q.table) :
    directGradS Q ε f z = ∫ y : ℂ,
      (fderiv ℝ (kernel ε) (z.1.1 - y)).smulRight (f ((y,z.1.2),z.2)) := by
  rw [directGradS, ← integral_indicator Q.measurableSet_table]
  apply integral_congr_ae
  exact Eventually.of_forall fun y => by
    by_cases hy : y ∈ Q.table
    · rw [indicator_of_mem hy]
    · rw [indicator_of_notMem hy]
      have hn : ε < ‖z.1.1 - y‖ := by
        by_contra hh
        exact hy (hz (by rw [mem_closedBall, dist_comm, dist_eq_norm]; exact not_lt.mp hh))
      simp only [kernel_fderiv_eq_zero hε hn, ContinuousLinearMap.zero_smulRight]

lemma reflectedGradS_zero_of_coord (Q : Triangle) (i : Fin 3) {ε : ℝ} (hε : 0 < ε)
    (f : SmoothPhase → ℂ) (z : SmoothPhase)
    (hz : Q.coordinateBound * ε < Q.basis.coord (i+2) z.1.1) :
    reflectedGradS Q i ε f z = 0 := by
  apply integral_eq_zero_of_ae
  filter_upwards [ae_restrict_mem Q.measurableSet_table] with y hy
  have hn : ε < ‖z.1.1 - wallReflection Q i y‖ := by
    by_contra hh
    exact (not_le_of_gt hz) (Q.coord_small_of_reflected_near i hy (not_lt.mp hh))
  simp only [kernel_fderiv_eq_zero hε hn, ContinuousLinearMap.zero_smulRight, Pi.zero_apply]

lemma eventually_interior_gradient (Q : Triangle) (f : SmoothPhase → ℂ)
    (z : SmoothPhase) (hz : z.1.1 ∈ Q.table) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), reflectedSmoothingGradient Q ε f z =
      ∫ y : ℂ, (fderiv ℝ (kernel ε) (z.1.1-y)).smulRight (f ((y,z.1.2),z.2)) := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp Q.isOpen_table _ hz
  have hcoords : ∀ᶠ ε in 𝓝 (0 : ℝ), ∀ i : Fin 3,
      Q.coordinateBound * ε < Q.basis.coord (i+2) z.1.1 := by
    rw [Filter.eventually_all]
    intro i
    have hp := (Q.table_iff_coords z.1.1).mp hz (i+2)
    have hc : Continuous (fun ε : ℝ => Q.coordinateBound * ε) := by fun_prop
    simpa only [mul_zero] using hc.continuousAt.eventually (gt_mem_nhds (by simpa only [mul_zero] using hp))
  filter_upwards [nhdsWithin_le_nhds hcoords,
    nhdsWithin_le_nhds (gt_mem_nhds hr), self_mem_nhdsWithin] with ε hc hεr hε
  have hε' : 0 < ε := hε
  have hfull := directGradS_eq_full Q hε' f z (fun y hy => hball (by
    rw [mem_ball]
    exact (mem_closedBall.mp hy).trans_lt hεr))
  change directGradS Q ε f z + ∑ i : Fin 3, reflectedGradS Q i ε f z = _
  simp only [reflectedGradS_zero_of_coord Q _ hε' f z (hc _), Finset.sum_const_zero, add_zero]
  exact hfull

lemma scaled_gradient_pointwise (Q : Triangle) (f : DoublePhase →ᵇ ℂ)
    (z : DoublePhase) (hz : z.1.1 ∈ Q.table) :
    Tendsto (fun ε : ℝ => ε • reflectedSmoothingGradient Q ε f z)
      (𝓝[>] 0) (𝓝 0) := by
  let g : ℂ →ᵇ ℂ := f.compContinuous ⟨fun y => ((y,z.1.2),z.2), by fun_prop⟩
  have h := (rescaled_gradient_tendsto g z.1.1).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  apply h.congr'
  filter_upwards [eventually_interior_gradient Q f z hz, self_mem_nhdsWithin] with ε hε hp
  rw [hε]
  exact (scaled_full_gradient ε hp (fun y => f ((y,z.1.2),z.2)) z.1.1).symm

end TriangularBilliards

namespace TriangularBilliards
open Filter SpatialSmoothing
open scoped Topology BoundedContinuousFunction

lemma norm_integral_le_kernel_bound {α : Type uAlpha} {E : Type uE} [MeasurableSpace α]
    [NormedAddCommGroup E] [NormedSpace ℝ E] {μ : Measure α}
    (F : α → E) {K : α → ℝ≥0∞} {H C : ℝ} (hH : 0 ≤ H) (hC : 0 ≤ C)
    (hF : ∀ x, ‖F x‖ₑ ≤ K x * ENNReal.ofReal H)
    (hK : ∫⁻ x, K x ∂μ ≤ ENNReal.ofReal C) :
    ‖∫ x, F x ∂μ‖ ≤ C * H := by
  apply (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hC hH)).mp
  rw [ofReal_norm, ENNReal.ofReal_mul hC]
  calc
    ‖∫ x, F x ∂μ‖ₑ ≤ ∫⁻ x, ‖F x‖ₑ ∂μ := enorm_integral_le_lintegral_enorm F
    _ ≤ ∫⁻ x, K x * ENNReal.ofReal H ∂μ := lintegral_mono hF
    _ = (∫⁻ x, K x ∂μ) * ENNReal.ofReal H := lintegral_mul_const' _ _ ENNReal.ofReal_ne_top
    _ ≤ _ := by gcongr

lemma directGradS_norm_bound (Q : Triangle) {ε : ℝ} (hε : 0 < ε)
    {f : DoublePhase → ℂ} {H : ℝ} (hH : 0 ≤ H) (hf : ∀ z, ‖f z‖ ≤ H)
    (z : DoublePhase) : ‖directGradS Q ε f z‖ ≤ (derivativeMass / ε) * H := by
  apply norm_integral_le_kernel_bound (μ := volume.restrict Q.table)
    (K := fun y => ENNReal.ofReal ‖fderiv ℝ (kernel ε) (z.1.1-y)‖) _ hH
    (div_nonneg derivativeMass_nonneg hε.le)
  · intro y
    rw [← ofReal_norm, ContinuousLinearMap.norm_smulRight_apply,
      ENNReal.ofReal_mul (norm_nonneg _)]
    exact mul_le_mul_right (ENNReal.ofReal_le_ofReal (hf ((y,z.1.2),z.2))) _
  · exact derivative_kernel_row_bound Q hε z.1.1

lemma reflectedGradS_norm_bound (Q : Triangle) (i : Fin 3) {ε : ℝ} (hε : 0 < ε)
    {f : DoublePhase → ℂ} {H : ℝ} (hH : 0 ≤ H) (hf : ∀ z, ‖f z‖ ≤ H)
    (z : DoublePhase) : ‖reflectedGradS Q i ε f z‖ ≤ (derivativeMass / ε) * H := by
  apply norm_integral_le_kernel_bound (μ := volume.restrict Q.table)
    (K := fun y => ENNReal.ofReal ‖fderiv ℝ (kernel ε) (z.1.1 - wallReflection Q i y)‖) _ hH
    (div_nonneg derivativeMass_nonneg hε.le)
  · intro y
    rw [← ofReal_norm, ContinuousLinearMap.norm_smulRight_apply,
      ENNReal.ofReal_mul (norm_nonneg _)]
    exact mul_le_mul_right (ENNReal.ofReal_le_ofReal (hf ((y,reflectedDirection Q i z.1.2),z.2+1))) _
  · exact reflected_derivative_kernel_row_bound Q i hε z.1.1

lemma scaled_gradient_norm_bound (Q : Triangle) {ε : ℝ} (hε : 0 < ε)
    {f : DoublePhase → ℂ} {H : ℝ} (hH : 0 ≤ H) (hf : ∀ z, ‖f z‖ ≤ H)
    (z : DoublePhase) : ‖ε • reflectedSmoothingGradient Q ε f z‖ ≤ 4 * derivativeMass * H := by
  have hb : ‖reflectedSmoothingGradient Q ε f z‖ ≤ 4 * (derivativeMass / ε) * H := by
    change ‖directGradS Q ε f z + ∑ i : Fin 3, reflectedGradS Q i ε f z‖ ≤ _
    calc
      _ ≤ ‖directGradS Q ε f z‖ + ∑ i : Fin 3, ‖reflectedGradS Q i ε f z‖ :=
        (norm_add_le _ _).trans (add_le_add le_rfl (norm_sum_le _ _))
      _ ≤ (derivativeMass / ε) * H + ∑ _i : Fin 3, (derivativeMass / ε) * H := by
        gcongr
        · exact directGradS_norm_bound Q hε hH hf z
        · exact reflectedGradS_norm_bound Q _ hε hH hf z
      _ = _ := by simp; ring
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hε]
  calc
    _ ≤ ε * (4 * (derivativeMass / ε) * H) := mul_le_mul_of_nonneg_left hb hε.le
    _ = _ := by field_simp

lemma ae_double_position_in_table (Q : Triangle) :
    ∀ᵐ z ∂doubleMeasure Q, z.1.1 ∈ Q.table := by
  exact (measurePreserving_fst (μ := phaseMeasure Q) (ν := parityMeasure)).quasiMeasurePreserving.ae
    (ae_position_in_table Q)

/-- The small-scaled-derivative estimate on the dense class of bounded
continuous fields, for the actual reflected convolution kernel. -/
lemma scaled_gradient_integral_tendsto (Q : Triangle) (f : DoublePhase →ᵇ ℂ) :
    Tendsto (fun ε : ℝ => ∫ z, ‖ε • reflectedSmoothingGradient Q ε f z‖ ^ 2 ∂doubleMeasure Q)
      (𝓝[>] 0) (𝓝 0) := by
  have hlim : Tendsto (fun ε : ℝ => ∫ z, ‖ε • reflectedSmoothingGradient Q ε f z‖ ^ 2 ∂doubleMeasure Q)
      (𝓝[>] 0) (𝓝 (∫ _ : DoublePhase, (0 : ℝ) ∂doubleMeasure Q)) := by
    apply tendsto_integral_filter_of_norm_le_const
    · exact Eventually.of_forall fun ε =>
        (((reflectedSmoothingGradient_stronglyMeasurable Q ε f.continuous.stronglyMeasurable).const_smul ε).measurable.norm.pow_const 2).aestronglyMeasurable
    · refine ⟨(4 * derivativeMass * ‖f‖) ^ 2, ?_⟩
      filter_upwards [self_mem_nhdsWithin] with ε hε
      exact Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact pow_le_pow_left₀ (norm_nonneg _) (scaled_gradient_norm_bound Q hε (norm_nonneg f) f.norm_coe_le_norm z) 2
    · filter_upwards [ae_double_position_in_table Q] with z hz
      simpa only [norm_zero, OfNat.ofNat_ne_zero, ne_eq, not_false_eq_true, zero_pow] using
        ((scaled_gradient_pointwise Q f z hz).norm.pow 2)
  simpa only [integral_zero] using hlim

end TriangularBilliards

namespace TriangularBilliards
open Filter SpatialSmoothing
open scoped Topology BoundedContinuousFunction

lemma integrable_slice_ae (Q : Triangle) {f : DoublePhase → ℂ}
    (hf : Integrable f (doubleMeasure Q)) :
    ∀ᵐ z ∂doubleMeasure Q, Integrable (fun y => f ((y,z.1.2),z.2)) (volume.restrict Q.table) := by
  let μ : Measure ℂ := (volume Q.table)⁻¹ • volume.restrict Q.table
  have hμ : IsProbabilityMeasure μ := ⟨Q.normalized_area_univ⟩
  have ha := measurePreserving_prodAssoc μ angularMeasure parityMeasure
  have hfi : Integrable (fun p : ℂ × (Circle × ZMod 2) => f ((p.1,p.2.1),p.2.2))
      (μ.prod (angularMeasure.prod parityMeasure)) := by
    exact (ha.integrable_comp_emb MeasurableEquiv.prodAssoc.measurableEmbedding).mp hf
  have hs : ∀ᵐ c ∂angularMeasure.prod parityMeasure,
      Integrable (fun y => f ((y,c.1),c.2)) (volume.restrict Q.table) := by
    filter_upwards [hfi.prod_left_ae] with c hc
    exact (integrable_smul_measure (by simpa using Q.area_lt_top.ne)
      (by simpa using Q.area_pos.ne')).mp hc
  exact ha.quasiMeasurePreserving.ae
    ((measurePreserving_snd (μ := μ) (ν := angularMeasure.prod parityMeasure)).quasiMeasurePreserving.ae hs)

lemma equal_slice_ae (Q : Triangle) {f g : DoublePhase → ℂ}
    (h : f =ᵐ[doubleMeasure Q] g) :
    ∀ᵐ z ∂doubleMeasure Q, (fun y => f ((y,z.1.2),z.2)) =ᵐ[volume.restrict Q.table]
      (fun y => g ((y,z.1.2),z.2)) := by
  let μ : Measure ℂ := (volume Q.table)⁻¹ • volume.restrict Q.table
  have hμ : IsProbabilityMeasure μ := ⟨Q.normalized_area_univ⟩
  have ha := measurePreserving_prodAssoc μ angularMeasure parityMeasure
  have hi := ha.symm MeasurableEquiv.prodAssoc
  have hc := (Measure.measurePreserving_swap (μ := angularMeasure.prod parityMeasure) (ν := μ)).quasiMeasurePreserving.ae
    (hi.quasiMeasurePreserving.ae h)
  have hs : ∀ᵐ c ∂angularMeasure.prod parityMeasure,
      (fun y => f ((y,c.1),c.2)) =ᵐ[volume.restrict Q.table] (fun y => g ((y,c.1),c.2)) := by
    filter_upwards [Measure.ae_ae_of_ae_prod hc] with c hc
    exact (Measure.ae_ennreal_smul_measure_iff (by simpa using Q.area_lt_top.ne)).mp hc
  exact ha.quasiMeasurePreserving.ae
    ((measurePreserving_snd (μ := μ) (ν := angularMeasure.prod parityMeasure)).quasiMeasurePreserving.ae hs)

lemma directGradS_congr_ae (Q : Triangle) (ε : ℝ) {f g : DoublePhase → ℂ}
    (h : f =ᵐ[doubleMeasure Q] g) : directGradS Q ε f =ᵐ[doubleMeasure Q] directGradS Q ε g := by
  filter_upwards [equal_slice_ae Q h] with z hz
  apply integral_congr_ae
  filter_upwards [hz] with y hy
  rw [hy]

lemma reflectedGradS_congr_ae (Q : Triangle) (i : Fin 3) (ε : ℝ) {f g : DoublePhase → ℂ}
    (h : f =ᵐ[doubleMeasure Q] g) :
    reflectedGradS Q i ε f =ᵐ[doubleMeasure Q] reflectedGradS Q i ε g := by
  filter_upwards [(measurePreserving_directionParityReflection Q i).quasiMeasurePreserving.ae
    (equal_slice_ae Q h)] with z hz
  apply integral_congr_ae
  filter_upwards [hz] with y hy
  rw [hy]

lemma reflectedSmoothingGradient_congr_ae (Q : Triangle) (ε : ℝ) {f g : DoublePhase → ℂ}
    (h : f =ᵐ[doubleMeasure Q] g) :
    reflectedSmoothingGradient Q ε f =ᵐ[doubleMeasure Q] reflectedSmoothingGradient Q ε g := by
  filter_upwards [directGradS_congr_ae Q ε h,
    Filter.eventually_all.mpr (fun i => reflectedGradS_congr_ae Q i ε h)] with z hd hr
  change directGradS Q ε f z + ∑ i, reflectedGradS Q i ε f z =
    directGradS Q ε g z + ∑ i, reflectedGradS Q i ε g z
  rw [hd]
  congr 1
  exact Finset.sum_congr rfl (fun i _ => hr i)

lemma smulRight_sub (k : ℂ →L[ℝ] ℝ) (a b : ℂ) :
    k.smulRight (a-b) = k.smulRight a - k.smulRight b := by
  ext v
  change k v • (a-b) = k v • a - k v • b
  exact smul_sub _ _ _

lemma smulRight_integrable {k : ℂ → (ℂ →L[ℝ] ℝ)} {f : ℂ → ℂ}
    {ν : Measure ℂ} (hk : StronglyMeasurable k) (hf : StronglyMeasurable f)
    (hi : Integrable f ν) {C : ℝ} (hb : ∀ y, ‖k y‖ ≤ C) :
    Integrable (fun y => (k y).smulRight (f y)) ν := by
  apply (hi.norm.const_mul C).mono' (smulRight_stronglyMeasurable hk hf).aestronglyMeasurable
  exact Eventually.of_forall fun y => by
    rw [ContinuousLinearMap.norm_smulRight_apply]
    exact mul_le_mul_of_nonneg_right (hb y) (norm_nonneg _)

lemma directGradS_integrable_ae (Q : Triangle) {ε : ℝ} (hε : 0 < ε)
    {f : DoublePhase → ℂ} (hf : StronglyMeasurable f) (hi : Integrable f (doubleMeasure Q)) :
    ∀ᵐ z ∂doubleMeasure Q, Integrable (fun y => (fderiv ℝ (kernel ε) (z.1.1-y)).smulRight
      (f ((y,z.1.2),z.2))) (volume.restrict Q.table) := by
  obtain ⟨C,hC⟩ := ((kernel_hasCompactSupport hε).fderiv ℝ).exists_bound_of_continuous
    ((kernel_contDiff ε).continuous_fderiv (by simp))
  filter_upwards [integrable_slice_ae Q hi] with z hz
  exact smulRight_integrable
    (((kernel_contDiff ε).continuous_fderiv (by simp)).stronglyMeasurable.comp_measurable
      (measurable_const.sub measurable_id))
    (hf.comp_measurable ((measurable_id.prodMk measurable_const).prodMk measurable_const))
    hz (fun y => hC (z.1.1-y))

lemma reflectedGradS_integrable_ae (Q : Triangle) (i : Fin 3) {ε : ℝ} (hε : 0 < ε)
    {f : DoublePhase → ℂ} (hf : StronglyMeasurable f) (hi : Integrable f (doubleMeasure Q)) :
    ∀ᵐ z ∂doubleMeasure Q, Integrable (fun y =>
      (fderiv ℝ (kernel ε) (z.1.1-wallReflection Q i y)).smulRight
      (f ((y,reflectedDirection Q i z.1.2),z.2+1))) (volume.restrict Q.table) := by
  obtain ⟨C,hC⟩ := ((kernel_hasCompactSupport hε).fderiv ℝ).exists_bound_of_continuous
    ((kernel_contDiff ε).continuous_fderiv (by simp))
  filter_upwards [(measurePreserving_directionParityReflection Q i).quasiMeasurePreserving.ae
    (integrable_slice_ae Q hi)] with z hz
  exact smulRight_integrable
    (((kernel_contDiff ε).continuous_fderiv (by simp)).stronglyMeasurable.comp_measurable
      (measurable_const.sub (wallReflection_contDiff Q i).continuous.measurable))
    (hf.comp_measurable ((measurable_id.prodMk measurable_const).prodMk measurable_const))
    hz (fun y => hC (z.1.1-wallReflection Q i y))

lemma directGradS_sub_ae (Q : Triangle) {ε : ℝ} (hε : 0 < ε)
    {f g : DoublePhase → ℂ} (hf : StronglyMeasurable f) (hg : StronglyMeasurable g)
    (hfi : Integrable f (doubleMeasure Q)) (hgi : Integrable g (doubleMeasure Q)) :
    directGradS Q ε (f-(g : DoublePhase → ℂ)) =ᵐ[doubleMeasure Q] directGradS Q ε f - directGradS Q ε g := by
  filter_upwards [directGradS_integrable_ae Q hε hf hfi,
    directGradS_integrable_ae Q hε hg hgi] with z hz hw
  change (∫ y in Q.table, (fderiv ℝ (kernel ε) (z.1.1-y)).smulRight (f ((y,z.1.2),z.2) - g ((y,z.1.2),z.2))) = _
  simp_rw [smulRight_sub]
  exact integral_sub hz hw

lemma reflectedGradS_sub_ae (Q : Triangle) (i : Fin 3) {ε : ℝ} (hε : 0 < ε)
    {f g : DoublePhase → ℂ} (hf : StronglyMeasurable f) (hg : StronglyMeasurable g)
    (hfi : Integrable f (doubleMeasure Q)) (hgi : Integrable g (doubleMeasure Q)) :
    reflectedGradS Q i ε (f-(g : DoublePhase → ℂ)) =ᵐ[doubleMeasure Q] reflectedGradS Q i ε f - reflectedGradS Q i ε g := by
  filter_upwards [reflectedGradS_integrable_ae Q i hε hf hfi,
    reflectedGradS_integrable_ae Q i hε hg hgi] with z hz hw
  change (∫ y in Q.table, (fderiv ℝ (kernel ε) (z.1.1-wallReflection Q i y)).smulRight
    (f ((y,reflectedDirection Q i z.1.2),z.2+1) - g ((y,reflectedDirection Q i z.1.2),z.2+1))) = _
  simp_rw [smulRight_sub]
  exact integral_sub hz hw

lemma reflectedSmoothingGradient_sub_ae (Q : Triangle) {ε : ℝ} (hε : 0 < ε)
    {f g : DoublePhase → ℂ} (hf : StronglyMeasurable f) (hg : StronglyMeasurable g)
    (hfi : Integrable f (doubleMeasure Q)) (hgi : Integrable g (doubleMeasure Q)) :
    reflectedSmoothingGradient Q ε (f-(g : DoublePhase → ℂ)) =ᵐ[doubleMeasure Q]
      reflectedSmoothingGradient Q ε f - reflectedSmoothingGradient Q ε g := by
  filter_upwards [directGradS_sub_ae Q hε hf hg hfi hgi,
    Filter.eventually_all.mpr (fun i => reflectedGradS_sub_ae Q i hε hf hg hfi hgi)] with z hd hr
  change directGradS Q ε (f-(g : DoublePhase → ℂ)) z + ∑ i, reflectedGradS Q i ε (f-(g : DoublePhase → ℂ)) z =
    (directGradS Q ε f z + ∑ i, reflectedGradS Q i ε f z) -
      (directGradS Q ε g z + ∑ i, reflectedGradS Q i ε g z)
  simp only [Pi.sub_apply] at hd hr
  rw [hd]
  simp_rw [hr]
  rw [Finset.sum_sub_distrib]
  abel

lemma scaled_gradient_lpNorm_bound (Q : Triangle) {ε : ℝ} (hε : 0 < ε)
    {f : DoublePhase → ℂ} (hf : StronglyMeasurable f) (hf₂ : MemLp f 2 (doubleMeasure Q)) :
    lpNorm (ε • reflectedSmoothingGradient Q ε f) 2 (doubleMeasure Q) ≤
      (4 * derivativeMass) * lpNorm f 2 (doubleMeasure Q) := by
  rw [← toReal_eLpNorm, ← toReal_eLpNorm]
  have hb : eLpNorm (ε • reflectedSmoothingGradient Q ε f) 2 (doubleMeasure Q) ≤
      ENNReal.ofReal (4 * derivativeMass) * eLpNorm f 2 (doubleMeasure Q) := by
    calc
      _ ≤ ‖ε‖ₑ * eLpNorm (reflectedSmoothingGradient Q ε f) 2 (doubleMeasure Q) := eLpNorm_const_smul_le
      _ ≤ ‖ε‖ₑ * (4 * ENNReal.ofReal (derivativeMass / ε) * eLpNorm f 2 (doubleMeasure Q)) := by
        gcongr
        exact reflectedSmoothingGradient_eLpNorm Q hε hf
      _ = _ := by
        rw [Real.enorm_eq_ofReal hε.le, ENNReal.ofReal_div_of_pos hε,
          ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 4)]
        have he : ENNReal.ofReal ε ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hε
        rw [div_eq_mul_inv]
        calc
          _ = 4 * ENNReal.ofReal derivativeMass * eLpNorm f 2 (doubleMeasure Q) *
              (ENNReal.ofReal ε * (ENNReal.ofReal ε)⁻¹) := by ac_rfl
          _ = _ := by rw [ENNReal.mul_inv_cancel he ENNReal.ofReal_ne_top, mul_one]; norm_num
  have ht : ENNReal.ofReal (4 * derivativeMass) * eLpNorm f 2 (doubleMeasure Q) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hf₂.eLpNorm_ne_top
  have h := ENNReal.toReal_mono ht hb
  have hC : 0 ≤ 4 * derivativeMass := mul_nonneg (by norm_num) derivativeMass_nonneg
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hC] using h

lemma lpNorm_congr_ae_of_strong {α : Type uAlpha} {E : Type uE} [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : Measure α} {p : ℝ≥0∞} {f g : α → E}
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ) (h : f =ᵐ[μ] g) :
    lpNorm f p μ = lpNorm g p μ := by
  rw [← toReal_eLpNorm, ← toReal_eLpNorm]
  exact congrArg ENNReal.toReal (eLpNorm_congr_enorm_ae hf hg (h.fun_comp enorm))

lemma scaled_gradient_lpNorm_tendsto_bounded (Q : Triangle) (f : DoublePhase →ᵇ ℂ) :
    Tendsto (fun ε : ℝ => lpNorm (ε • reflectedSmoothingGradient Q ε f) 2 (doubleMeasure Q))
      (𝓝[>] 0) (𝓝 0) := by
  have he (ε : ℝ) : lpNorm (ε • reflectedSmoothingGradient Q ε f) 2 (doubleMeasure Q) =
      Real.sqrt (∫ z, ‖ε • reflectedSmoothingGradient Q ε f z‖ ^ 2 ∂doubleMeasure Q) := by
    rw [lpNorm_eq_integral_norm_rpow_toReal (by norm_num) (by norm_num)
      ((reflectedSmoothingGradient_stronglyMeasurable Q ε f.continuous.stronglyMeasurable).const_smul ε).aestronglyMeasurable]
    simp only [ENNReal.toReal_ofNat, Pi.smul_apply, Real.rpow_two, Real.sqrt_eq_rpow]
    norm_num
  simp_rw [he]
  simpa only [Real.sqrt_zero, Function.comp_def] using Real.continuous_sqrt.continuousAt.tendsto.comp
    (scaled_gradient_integral_tendsto Q f)

/-- The small-scaled-derivative estimate for every L² input
and the reflected triangular kernel, not merely a dense test class. -/
lemma scaled_gradient_lpNorm_tendsto (Q : Triangle) {f : DoublePhase → ℂ}
    (hf : StronglyMeasurable f) (hf₂ : MemLp f 2 (doubleMeasure Q)) :
    Tendsto (fun ε : ℝ => lpNorm (ε • reflectedSmoothingGradient Q ε f) 2 (doubleMeasure Q))
      (𝓝[>] 0) (𝓝 0) := by
  let C : ℝ := 4 * derivativeMass
  have hC : 0 ≤ C := mul_nonneg (by norm_num) derivativeMass_nonneg
  apply Metric.tendsto_nhds.mpr
  intro δ hδ
  let η : ℝ := δ / (2 * (C+1))
  have hη : 0 < η := div_pos hδ (by positivity)
  obtain ⟨g,hg,hg₂⟩ := hf₂.exists_boundedContinuous_eLpNorm_sub_le
    (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) (ENNReal.ofReal_ne_zero_iff.mpr hη)
  have hsmall : lpNorm (f - (g : DoublePhase → ℂ)) 2 (doubleMeasure Q) ≤ η := by
    rw [← toReal_eLpNorm]
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hg).trans_eq (ENNReal.toReal_ofReal hη.le)
  have hgsmall := (Metric.tendsto_nhds.mp (scaled_gradient_lpNorm_tendsto_bounded Q g))
    (δ/2) (by positivity)
  filter_upwards [self_mem_nhdsWithin, hgsmall] with ε hε he
  have hgm := (reflectedSmoothingGradient_memLp Q hε g.continuous.stronglyMeasurable hg₂).const_smul ε
  have hfm := (reflectedSmoothingGradient_memLp Q hε hf hf₂).const_smul ε
  have hdiffm := (reflectedSmoothingGradient_memLp Q hε
    (hf.sub g.continuous.stronglyMeasurable) (hf₂.sub hg₂)).const_smul ε
  have hae : (ε • reflectedSmoothingGradient Q ε f - ε • reflectedSmoothingGradient Q ε g) =ᵐ[doubleMeasure Q]
      ε • reflectedSmoothingGradient Q ε (f - (g : DoublePhase → ℂ)) := by
    filter_upwards [reflectedSmoothingGradient_sub_ae Q hε hf g.continuous.stronglyMeasurable
      (hf₂.integrable (by norm_num)) (hg₂.integrable (by norm_num))] with z hz
    simp only [Pi.sub_apply, Pi.smul_apply] at hz ⊢
    rw [hz, smul_sub]
  have hn := lpNorm_le_lpNorm_add_lpNorm_sub' hgm (f := ε • reflectedSmoothingGradient Q ε f)
    (by norm_num : (1:ℝ≥0∞) ≤ 2)
  rw [lpNorm_congr_ae_of_strong (hfm.sub hgm).aestronglyMeasurable
    hdiffm.aestronglyMeasurable hae] at hn
  have hb := scaled_gradient_lpNorm_bound Q hε (hf.sub g.continuous.stronglyMeasurable) (hf₂.sub hg₂)
  have ht : C * η < δ/2 := by
    dsimp [η]
    have hc : (0:ℝ) < C+1 := by linarith
    rw [← mul_div_assoc, div_lt_iff₀ (by positivity : 0 < 2*(C+1))]
    nlinarith
  have hnonneg : 0 ≤ lpNorm (ε • reflectedSmoothingGradient Q ε g) 2 (doubleMeasure Q) := lpNorm_nonneg
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hnonneg] at he
  rw [Real.dist_eq, sub_zero, abs_of_nonneg lpNorm_nonneg]
  have hh : lpNorm (ε • reflectedSmoothingGradient Q ε (f - (g : DoublePhase → ℂ))) 2
      (doubleMeasure Q) ≤ C * η := hb.trans (mul_le_mul_of_nonneg_left hsmall hC)
  linarith

end TriangularBilliards

end
end
end

end OAI
