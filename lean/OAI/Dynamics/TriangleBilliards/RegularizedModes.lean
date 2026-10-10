import OAI.Dynamics.TriangleBilliards.Localization

namespace OAI

open MeasureTheory Set
open scoped ENNReal symmDiff
noncomputable section
open MeasureTheory Set Filter Function Metric
open scoped Topology Convolution ContDiff
noncomputable section
open MeasureTheory Set
open scoped ENNReal
noncomputable section
open MeasureTheory Set Filter BoundedContinuousFunction
open scoped ENNReal Topology ComplexConjugate
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ComplexConjugate
noncomputable section
open MeasureTheory Filter
open scoped ComplexConjugate
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ComplexConjugate
noncomputable section
open Filter Finset Set
open scoped Topology BigOperators
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff NNReal
open MeasureTheory Filter Set
open scoped Topology ComplexConjugate
noncomputable section

namespace TriangularBilliards
open Analysis SpatialSmoothing MeasureTheory Filter Set
open scoped Topology ContDiff NNReal
local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

/-- The uniform per-coefficient estimate for cutoff regularizations of an
actual bounded invariant. The constant depends on the triangle, not the
Fourier index, smoothing scale, or the bounded invariant. -/
lemma bounded_invariant_regularized_modes (Q : Triangle) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {H : ℝ} {f : DoublePhase → ℂ}
      (hm : StronglyMeasurable f) (hf : MemLp f 2 (doubleMeasure Q))
      (hH : ∀ z, ‖f z‖ ≤ H)
      (_hfi : (geodesicHilbertFlow Q).HasGenerator (hf.toLp f) 0)
      {ε : ℝ} (hε : 0 < ε)
      (_hsmall : 2 * ((Q.safetyFactor + 1) * ε) * Q.coordinateBound < 1) (j : ℤ),
      let w := supportedSmoothing Q ε ((Q.safetyFactor + 1) * ε) f
      let hw := supportedSmoothing_memLp Q hε ((Q.safetyFactor + 1) * ε) hm hH
      ∃ dx dy : Lp ℂ 2 (doubleMeasure Q),
        (geodesicHilbertFlow Q).HasGenerator ((angularCircleAction Q).projection j (hw.toLp w)) dx ∧
        (transverseHilbertFlow Q).HasGenerator ((angularCircleAction Q).projection j (hw.toLp w)) dy ∧
        ‖dx‖ ^ 2 ≤ C * H^2 ∧ ‖dy‖ ^ 2 ≤ C * H^2 := by
  obtain ⟨D,hDp,hD⟩ := exists_vertexCutoff_derivative_bound
  let K := Q.safetyFactor + 1
  have hK : 1 < K := by dsimp [K]; linarith [Q.safetyFactor_pos]
  let J := 4 * derivativeMass + 4 * D
  have hJ : 0 ≤ J := by
    dsimp [J]
    exact add_nonneg (mul_nonneg (by norm_num) derivativeMass_nonneg) (mul_nonneg (by norm_num) hDp)
  let B := ((volume Q.table).toReal)⁻¹ * (3 * (2*K+1)^2 * Real.pi)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  refine ⟨4 * J^2 * B, by positivity, ?_⟩
  intro H f hm hf hH hfi ε hε hsmall j
  have hH₀ : 0 ≤ H := (norm_nonneg _).trans (hH ((0,1),0))
  have hR : Q.safetyFactor * ε < K * ε := by dsimp [K]; nlinarith
  have hRp : 0 < K * ε := mul_pos (by linarith) hε
  let Cε : ℝ≥0 := ⟨J*H/ε, by positivity⟩
  have hC (x : ℂ) (v : Circle) (b : ZMod 2) :
      ‖fderiv ℝ (fun y => supportedSmoothing Q ε (K*ε) f ((y,v),b)) x‖ ≤ Cε := by
    rw [(supportedSmoothing_hasFDerivAt Q hε (K*ε) hm hH v b x).fderiv]
    apply (supportedSmoothingGradient_norm_bound Q hε hH₀ hH (hD Q (K*ε) hRp) ((x,v),b)).trans
    change 4*derivativeMass*H/ε + (D/(K*ε))*(4*H) ≤ J*H/ε
    have hh : D / (K*ε) ≤ D / ε :=
      div_le_div_of_nonneg_left hDp hε (by nlinarith)
    calc
      _ ≤ 4*derivativeMass*H/ε + (D/ε)*(4*H) := by gcongr
      _ = _ := by dsimp [J]; ring
  obtain ⟨M,hM⟩ := supportedSmoothing_second_bound Q hε hRp hm hH
  have hm' := (supportedSmoothing_stronglyMeasurable Q ε (K*ε) hm).measurable
  have hw := supportedSmoothing_memLp Q hε (K*ε) hm hH
  have hs := supportedSmoothing_seam Q hε hR hsmall f
  have hd := supportedSmoothing_contDiff Q hε (K*ε) hm hH
  have hA : 2 * (K*ε) + ε ≤ (2*K+1)*ε := by linarith
  obtain ⟨dx,dy,hgx,hgy,hbx,hby⟩ := seam_tip_energy hs hm' hd hC hM hw ((2*K+1)*ε)
    (supportedSmoothing_invariant_x_zero Q hε hR hsmall hA hm hf hfi hH) j
  have hmass : (doubleMeasure Q (unsafeSet Q ((2*K+1)*ε))).toReal ≤ B * ε^2 := by
    apply (unsafeSet_real_measure_bound Q (show 0 ≤ (2*K+1)*ε by positivity)).trans_eq
    dsimp [B]
    ring
  have hb : 4 * (Cε : ℝ)^2 * (doubleMeasure Q (unsafeSet Q ((2*K+1)*ε))).toReal ≤
      (4 * J^2 * B) * H^2 := by
    calc
      _ ≤ 4 * (Cε : ℝ)^2 * (B*ε^2) := by gcongr
      _ = _ := by
        change 4 * (J*H/ε)^2 * (B*ε^2) = _
        field_simp
  exact ⟨dx,dy,hgx,hgy,hbx.trans hb,hby.trans hb⟩

end TriangularBilliards

namespace TriangularBilliards
open Analysis SpatialSmoothing MeasureTheory Filter Set
open scoped Topology ContDiff NNReal BoundedContinuousFunction

lemma kernel_eq_zero_of_large {ε : ℝ} (hε : 0 < ε) {y : ℂ} (hy : ε ≤ ‖y‖) :
    kernel ε y = 0 := by
  by_contra h
  have hx : y ∈ support (kernel ε) := h
  rw [kernel_support hε, mem_ball_zero_iff] at hx
  exact (not_lt_of_ge hy) hx

lemma fullS_tendsto (f : ℂ →ᵇ ℂ) (x : ℂ) :
    Tendsto (fun ε : ℝ => ∫ y : ℂ, kernel ε (x-y) • f y) (𝓝[>] 0) (𝓝 (f x)) := by
  have hs : Tendsto (fun ε : ℝ => support (kernel ε)) (𝓝[>] 0) (𝓝 (0 : ℂ)).smallSets := by
    rw [tendsto_smallSets_iff]
    intro s hs
    obtain ⟨r,hr,hb⟩ := Metric.mem_nhds_iff.mp hs
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (gt_mem_nhds hr)] with ε hp he
    rw [kernel_support hp]
    exact (Metric.ball_subset_ball he.le).trans hb
  have hh := convolution_tendsto_right (μ := (volume : Measure ℂ))
    (g := fun _ : ℝ => (f : ℂ → ℂ)) (k := fun _ : ℝ => x)
    (Eventually.of_forall (fun ε => kernel_nonneg ε))
    (show ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∫ y, kernel ε y = 1 from
      (show ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε from self_mem_nhdsWithin).mono (fun ε hε => kernel_integral hε)) hs
    (Eventually.of_forall fun _ => f.continuous.aestronglyMeasurable)
    (f.continuous.continuousAt.tendsto.comp tendsto_snd) tendsto_const_nhds
  apply hh.congr (fun ε => ?_)
  rw [MeasureTheory.convolution_def]
  rw [← integral_sub_left_eq_self (fun y : ℂ => kernel ε (x-y) • f y) volume x]
  simp only [sub_sub_cancel, ContinuousLinearMap.lsmul_apply]

lemma directS_eq_full (Q : Triangle) {ε : ℝ} (hε : 0 < ε)
    (f : DoublePhase → ℂ) (z : DoublePhase) (hz : closedBall z.1.1 ε ⊆ Q.table) :
    directS Q ε f z.2 z.1.2 z.1.1 = ∫ y : ℂ, kernel ε (z.1.1-y) • f ((y,z.1.2),z.2) := by
  rw [directS, ← integral_indicator Q.measurableSet_table]
  apply integral_congr_ae
  exact Eventually.of_forall fun y => by
    by_cases hy : y ∈ Q.table
    · rw [indicator_of_mem hy]
    · rw [indicator_of_notMem hy]
      have hn : ε < ‖z.1.1-y‖ := by
        by_contra hh
        exact hy (hz (by rw [mem_closedBall, dist_comm, dist_eq_norm]; exact not_lt.mp hh))
      simp only [kernel_eq_zero_of_large hε hn.le, zero_smul]

lemma reflectedS_zero_of_coord_phase (Q : Triangle) (i : Fin 3) {ε : ℝ} (hε : 0 < ε)
    (f : DoublePhase → ℂ) (z : DoublePhase)
    (hz : Q.coordinateBound * ε < Q.basis.coord (i+2) z.1.1) :
    reflectedS Q i ε f z.2 z.1.2 z.1.1 = 0 := by
  apply integral_eq_zero_of_ae
  filter_upwards [ae_restrict_mem Q.measurableSet_table] with y hy
  have hn : ε < ‖z.1.1 - wallReflection Q i y‖ := by
    by_contra hh
    exact (not_le_of_gt hz) (Q.coord_small_of_reflected_near i hy (not_lt.mp hh))
  simp only [kernel_eq_zero_of_large hε hn.le, zero_smul, Pi.zero_apply]

lemma eventually_interior_smoothing (Q : Triangle) (f : DoublePhase → ℂ)
    (z : DoublePhase) (hz : z.1.1 ∈ Q.table) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), reflectedSmoothing Q ε f z =
      ∫ y : ℂ, kernel ε (z.1.1-y) • f ((y,z.1.2),z.2) := by
  obtain ⟨r,hr,hball⟩ := Metric.isOpen_iff.mp Q.isOpen_table _ hz
  have hcoords : ∀ᶠ ε in 𝓝 (0 : ℝ), ∀ i : Fin 3,
      Q.coordinateBound * ε < Q.basis.coord (i+2) z.1.1 := by
    rw [Filter.eventually_all]
    intro i
    have hp := (Q.table_iff_coords z.1.1).mp hz (i+2)
    have hc : Continuous (fun ε : ℝ => Q.coordinateBound * ε) := by fun_prop
    simpa only [mul_zero] using hc.continuousAt.eventually (gt_mem_nhds (by simpa only [mul_zero] using hp))
  filter_upwards [nhdsWithin_le_nhds hcoords,
    nhdsWithin_le_nhds (gt_mem_nhds hr), self_mem_nhdsWithin] with ε hc hεr hε
  have hfull := directS_eq_full Q hε f z (fun y hy => hball (by
    rw [mem_ball]
    exact (mem_closedBall.mp hy).trans_lt hεr))
  change directS Q ε f z.2 z.1.2 z.1.1 + ∑ i, reflectedS Q i ε f z.2 z.1.2 z.1.1 = _
  simp only [reflectedS_zero_of_coord_phase Q _ hε f z (hc _), Finset.sum_const_zero, add_zero]
  exact hfull

lemma smoothing_pointwise (Q : Triangle) (f : DoublePhase →ᵇ ℂ)
    (z : DoublePhase) (hz : z.1.1 ∈ Q.table) :
    Tendsto (fun ε : ℝ => reflectedSmoothing Q ε f z) (𝓝[>] 0) (𝓝 (f z)) := by
  let g : ℂ →ᵇ ℂ := f.compContinuous ⟨fun y => ((y,z.1.2),z.2), by fun_prop⟩
  exact (fullS_tendsto g z.1.1).congr' ((eventually_interior_smoothing Q f z hz).mono (fun _ h => h.symm))

end TriangularBilliards

namespace TriangularBilliards
open Analysis SpatialSmoothing MeasureTheory Filter Set
open scoped Topology ContDiff NNReal BoundedContinuousFunction

lemma Triangle.clearance_pos_of_mem_table (Q : Triangle) {x : ℂ} (hx : x ∈ Q.table) :
    0 < Q.clearance x := by
  apply ((finite_range Q.vertex).isClosed.notMem_iff_infDist_pos (range_nonempty _)).mp
  rintro ⟨i,rfl⟩
  have h := (Q.table_iff_coords _).mp hx (i+2)
  have hv : Q.basis.coord (i+2) (Q.vertex i) = 0 :=
    Q.basis.coord_apply (i+2) i |>.trans (ite_eq_right ((by decide : ∀ i : Fin 3, i+2 ≠ i) i))
  linarith

lemma supported_smoothing_pointwise (Q : Triangle) (K : ℝ) (hK : 0 < K)
    (f : DoublePhase →ᵇ ℂ) (z : DoublePhase) (hz : z.1.1 ∈ Q.table) :
    Tendsto (fun ε : ℝ => supportedSmoothing Q ε (K*ε) f z) (𝓝[>] 0) (𝓝 (f z)) := by
  have hc : ∀ᶠ ε in 𝓝 (0 : ℝ), 2*(K*ε) < Q.clearance z.1.1 := by
    have h : Continuous (fun ε : ℝ => 2*(K*ε)) := by fun_prop
    simpa only [mul_zero] using h.continuousAt.eventually
      (gt_mem_nhds (by simpa only [mul_zero] using Q.clearance_pos_of_mem_table hz))
  apply (smoothing_pointwise Q f z hz).congr'
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds hc] with ε hε hh
  simp only [supportedSmoothing, vertexCutoff_one Q (mul_pos hK hε) hh.le, one_smul]

lemma supported_smoothing_lpNorm_tendsto_bounded (Q : Triangle) {K : ℝ} (hK : 0 < K)
    (f : DoublePhase →ᵇ ℂ) :
    Tendsto (fun ε : ℝ => lpNorm (supportedSmoothing Q ε (K*ε) f - (f : DoublePhase → ℂ)) 2 (doubleMeasure Q))
      (𝓝[>] 0) (𝓝 0) := by
  have hi : Tendsto (fun ε : ℝ => ∫ z,
      ‖supportedSmoothing Q ε (K*ε) f z - f z‖^2 ∂doubleMeasure Q)
      (𝓝[>] 0) (𝓝 (∫ _ : DoublePhase, (0 : ℝ) ∂doubleMeasure Q)) := by
    apply tendsto_integral_filter_of_norm_le_const
    · exact Eventually.of_forall fun ε =>
        (((supportedSmoothing_stronglyMeasurable Q ε (K*ε) f.continuous.stronglyMeasurable).sub
          f.continuous.stronglyMeasurable).measurable.norm.pow_const 2).aestronglyMeasurable
    · refine ⟨(5*‖f‖)^2, ?_⟩
      filter_upwards [self_mem_nhdsWithin] with ε hε
      exact Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        apply pow_le_pow_left₀ (norm_nonneg _)
        exact (norm_sub_le _ _).trans (by
          have h := supportedSmoothing_norm_bound Q hε (K*ε) (norm_nonneg f) f.norm_coe_le_norm z
          linarith [f.norm_coe_le_norm z])
    · filter_upwards [ae_double_position_in_table Q] with z hz
      simpa only [sub_self, norm_zero, OfNat.ofNat_ne_zero, ne_eq, not_false_eq_true, zero_pow] using
        (((supported_smoothing_pointwise Q K hK f z hz).sub (tendsto_const_nhds (x := f z))).norm.pow 2)
  simp only [integral_zero] at hi
  have he (ε : ℝ) : lpNorm (supportedSmoothing Q ε (K*ε) f - (f : DoublePhase → ℂ)) 2 (doubleMeasure Q) =
      Real.sqrt (∫ z, ‖supportedSmoothing Q ε (K*ε) f z - f z‖^2 ∂doubleMeasure Q) := by
    rw [lpNorm_eq_integral_norm_rpow_toReal (by norm_num) (by norm_num)
      ((supportedSmoothing_stronglyMeasurable Q ε (K*ε) f.continuous.stronglyMeasurable).sub
        f.continuous.stronglyMeasurable).aestronglyMeasurable]
    simp only [ENNReal.toReal_ofNat, Pi.sub_apply, Real.rpow_two, Real.sqrt_eq_rpow]
    norm_num
  simp_rw [he]
  simpa only [Real.sqrt_zero, Function.comp_def] using Real.continuous_sqrt.continuousAt.tendsto.comp hi

lemma directS_integrable_ae (Q : Triangle) {ε : ℝ} (hε : 0 < ε)
    {f : DoublePhase → ℂ} (hi : Integrable f (doubleMeasure Q)) :
    ∀ᵐ z ∂doubleMeasure Q, Integrable (fun y => kernel ε (z.1.1-y) •
      f ((y,z.1.2),z.2)) (volume.restrict Q.table) := by
  obtain ⟨C,hC⟩ := (kernel_hasCompactSupport hε).exists_bound_of_continuous
    (kernel_contDiff ε).continuous
  filter_upwards [integrable_slice_ae Q hi] with z hz
  exact hz.bdd_smul C
    (((kernel_contDiff ε).continuous.comp (continuous_const.sub continuous_id)).aestronglyMeasurable)
    (Eventually.of_forall fun y => hC (z.1.1-y))

lemma reflectedS_integrable_ae (Q : Triangle) (i : Fin 3) {ε : ℝ} (hε : 0 < ε)
    {f : DoublePhase → ℂ} (hi : Integrable f (doubleMeasure Q)) :
    ∀ᵐ z ∂doubleMeasure Q, Integrable (fun y => kernel ε (z.1.1-wallReflection Q i y) •
      f ((y,reflectedDirection Q i z.1.2),z.2+1)) (volume.restrict Q.table) := by
  obtain ⟨C,hC⟩ := (kernel_hasCompactSupport hε).exists_bound_of_continuous
    (kernel_contDiff ε).continuous
  filter_upwards [(measurePreserving_directionParityReflection Q i).quasiMeasurePreserving.ae
    (integrable_slice_ae Q hi)] with z hz
  exact hz.bdd_smul C
    (((kernel_contDiff ε).continuous.comp (continuous_const.sub
      (wallReflection_contDiff Q i).continuous)).aestronglyMeasurable)
    (Eventually.of_forall fun y => hC (z.1.1-wallReflection Q i y))

lemma smoothing_sub_ae (Q : Triangle) {ε : ℝ} (hε : 0 < ε)
    {f g : DoublePhase → ℂ} (hfi : Integrable f (doubleMeasure Q)) (hgi : Integrable g (doubleMeasure Q)) :
    reflectedSmoothing Q ε (f-(g : DoublePhase → ℂ)) =ᵐ[doubleMeasure Q]
      reflectedSmoothing Q ε f - reflectedSmoothing Q ε g := by
  filter_upwards [directS_integrable_ae Q hε hfi, directS_integrable_ae Q hε hgi,
    Filter.eventually_all.mpr (fun i => reflectedS_integrable_ae Q i hε hfi),
    Filter.eventually_all.mpr (fun i => reflectedS_integrable_ae Q i hε hgi)] with z hf hg hrf hrg
  have hd : directS Q ε (f-(g : DoublePhase → ℂ)) z.2 z.1.2 z.1.1 = directS Q ε f z.2 z.1.2 z.1.1 - directS Q ε g z.2 z.1.2 z.1.1 := by
    simp only [directS, Pi.sub_apply, smul_sub]
    exact integral_sub hf hg
  have hr (i : Fin 3) : reflectedS Q i ε (f-(g : DoublePhase → ℂ)) z.2 z.1.2 z.1.1 =
      reflectedS Q i ε f z.2 z.1.2 z.1.1 - reflectedS Q i ε g z.2 z.1.2 z.1.1 := by
    simp only [reflectedS, Pi.sub_apply, smul_sub]
    exact integral_sub (hrf i) (hrg i)
  simp only [Pi.sub_apply, reflectedSmoothing, hd, hr, Finset.sum_sub_distrib]
  abel

lemma supported_smoothing_sub_ae (Q : Triangle) {ε : ℝ} (hε : 0 < ε) (R : ℝ)
    {f g : DoublePhase → ℂ} (hfi : Integrable f (doubleMeasure Q)) (hgi : Integrable g (doubleMeasure Q)) :
    supportedSmoothing Q ε R (f-(g : DoublePhase → ℂ)) =ᵐ[doubleMeasure Q]
      supportedSmoothing Q ε R f - supportedSmoothing Q ε R g := by
  filter_upwards [smoothing_sub_ae Q hε hfi hgi] with z hz
  simp only [Pi.sub_apply] at hz ⊢
  simp only [supportedSmoothing, hz, smul_sub]

lemma supportedSmoothing_norm_le (Q : Triangle) (ε R : ℝ) (f : DoublePhase → ℂ) (z : DoublePhase) :
    ‖supportedSmoothing Q ε R f z‖ ≤ ‖reflectedSmoothing Q ε f z‖ := by
  rw [supportedSmoothing, norm_smul, Real.norm_eq_abs, abs_of_nonneg (vertexCutoff_mem_Icc Q R _).1]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right (vertexCutoff_mem_Icc Q R _).2 (norm_nonneg _)

lemma supportedSmoothing_memLp_of_memLp (Q : Triangle) {ε : ℝ} (hε : 0 < ε) (R : ℝ)
    {f : DoublePhase → ℂ} (hf : StronglyMeasurable f) (hf₂ : MemLp f 2 (doubleMeasure Q)) :
    MemLp (supportedSmoothing Q ε R f) 2 (doubleMeasure Q) :=
  (reflectedSmoothing_memLp Q hε hf hf₂).norm.mono'
    (supportedSmoothing_stronglyMeasurable Q ε R hf).aestronglyMeasurable
    (Eventually.of_forall (supportedSmoothing_norm_le Q ε R f))

lemma supported_smoothing_lpNorm_bound (Q : Triangle) {ε : ℝ} (hε : 0 < ε) (R : ℝ)
    {f : DoublePhase → ℂ} (hf : StronglyMeasurable f) (hf₂ : MemLp f 2 (doubleMeasure Q)) :
    lpNorm (supportedSmoothing Q ε R f) 2 (doubleMeasure Q) ≤ 4 * lpNorm f 2 (doubleMeasure Q) := by
  rw [← toReal_eLpNorm, ← toReal_eLpNorm]
  have hh : eLpNorm (supportedSmoothing Q ε R f) 2 (doubleMeasure Q) ≤ 4 * eLpNorm f 2 (doubleMeasure Q) :=
    (eLpNorm_mono_ae (supportedSmoothing_stronglyMeasurable Q ε R hf).aestronglyMeasurable
      (Eventually.of_forall (supportedSmoothing_norm_le Q ε R f))).trans
      (reflectedSmoothing_eLpNorm Q hε hf)
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofNat] using
    ENNReal.toReal_mono (ENNReal.mul_ne_top (by norm_num) hf₂.eLpNorm_ne_top) hh

end TriangularBilliards

namespace TriangularBilliards
open Analysis SpatialSmoothing MeasureTheory Filter Set
open scoped Topology ContDiff NNReal BoundedContinuousFunction

/-- Strong L2 approximate identity for the actual supported triangular
mollifier. No smoothness or invariance is required of the input. -/
lemma supported_smoothing_lpNorm_tendsto (Q : Triangle) {K : ℝ} (hK : 0 < K)
    {f : DoublePhase → ℂ} (hf : StronglyMeasurable f) (hf₂ : MemLp f 2 (doubleMeasure Q)) :
    Tendsto (fun ε : ℝ => lpNorm (supportedSmoothing Q ε (K*ε) f - (f : DoublePhase → ℂ)) 2 (doubleMeasure Q))
      (𝓝[>] 0) (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro δ hδ
  let η : ℝ := δ/12
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨g,hg,hg₂⟩ := hf₂.exists_boundedContinuous_eLpNorm_sub_le
    (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) (ENNReal.ofReal_ne_zero_iff.mpr hη)
  have hsmall : lpNorm (f - (g : DoublePhase → ℂ)) 2 (doubleMeasure Q) ≤ η := by
    rw [← toReal_eLpNorm]
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hg).trans_eq (ENNReal.toReal_ofReal hη.le)
  have hgsmall := (Metric.tendsto_nhds.mp (supported_smoothing_lpNorm_tendsto_bounded Q hK g))
    (δ/2) (by positivity)
  filter_upwards [self_mem_nhdsWithin, hgsmall] with ε hε he
  let Sf := supportedSmoothing Q ε (K*ε) f
  let Sg := supportedSmoothing Q ε (K*ε) g
  have hfm := supportedSmoothing_memLp_of_memLp Q hε (K*ε) hf hf₂
  have hgm := supportedSmoothing_memLp_of_memLp Q hε (K*ε) g.continuous.stronglyMeasurable hg₂
  have hdm := supportedSmoothing_memLp_of_memLp Q hε (K*ε)
    (hf.sub g.continuous.stronglyMeasurable) (hf₂.sub hg₂)
  have hae : Sf - Sg =ᵐ[doubleMeasure Q] supportedSmoothing Q ε (K*ε) (f-(g : DoublePhase → ℂ)) :=
    (supported_smoothing_sub_ae Q hε (K*ε) (hf₂.integrable (by norm_num))
      (hg₂.integrable (by norm_num))).symm
  have hb : lpNorm (Sf-Sg) 2 (doubleMeasure Q) ≤ 4*η := by
    rw [lpNorm_congr_ae_of_strong (hfm.sub hgm).aestronglyMeasurable
      hdm.aestronglyMeasurable hae]
    exact (supported_smoothing_lpNorm_bound Q hε (K*ε)
      (hf.sub g.continuous.stronglyMeasurable) (hf₂.sub hg₂)).trans (by gcongr)
  have hn : lpNorm (Sf-f) 2 (doubleMeasure Q) ≤
      lpNorm (Sf-Sg) 2 (doubleMeasure Q) + lpNorm (Sg-(g : DoublePhase → ℂ)) 2 (doubleMeasure Q) +
        lpNorm (f-(g : DoublePhase → ℂ)) 2 (doubleMeasure Q) := by
    have heq : Sf-f = ((Sf-Sg)+(Sg-(g : DoublePhase → ℂ)))-(f-(g : DoublePhase → ℂ)) := by ext z; simp only [Pi.sub_apply, Pi.add_apply]; abel
    rw [heq]
    apply (lpNorm_sub_le ((hfm.sub hgm).add (hgm.sub hg₂)) (by norm_num)).trans
    exact add_le_add (lpNorm_add_le (hfm.sub hgm) (by norm_num)) le_rfl
  rw [Real.dist_eq, sub_zero, abs_of_nonneg lpNorm_nonneg] at he ⊢
  change lpNorm (Sf - f) 2 (doubleMeasure Q) < δ
  change lpNorm (Sg - (g : DoublePhase → ℂ)) 2 (doubleMeasure Q) < δ/2 at he
  dsimp [η] at hsmall hb
  linarith

end TriangularBilliards

end
end
end
end
end
end
end
end
end

end OAI
