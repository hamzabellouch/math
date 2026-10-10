import OAI.Geometry.Riemannian.HarmonicCore.Multipliers
import OAI.Geometry.Riemannian.HarmonicCore.WeakDerivative

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff Matrix InnerProductSpace Matrix.Norms.Elementwise
open scoped NNReal ENNReal

namespace HarmonicCounterexample.Main.SmoothMetric3
noncomputable def translateL2 {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (a : E3) : Lp V 2 (volume : Measure E3) →L[ℝ] Lp V 2 (volume : Measure E3) :=
  (Lp.compMeasurePreservingₗᵢ ℝ (fun x : E3 ↦ x+a) (measurePreserving_add_right volume a)).toContinuousLinearMap

lemma translateL2_coe {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (a : E3) (u : Lp V 2 (volume : Measure E3)) :
    (translateL2 a u : E3 → V) =ᵐ[volume] fun x ↦ u (x+a) :=
  Lp.coeFn_compMeasurePreserving u _

lemma translateL2_norm {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (a : E3) (u : Lp V 2 (volume : Measure E3)) : ‖translateL2 a u‖ = ‖u‖ :=
  Lp.norm_compMeasurePreserving u _

lemma gradient_translate {f : E3 → ℝ} (hf : ContDiff ℝ ∞ f) (a x : E3) :
    gradient (fun y ↦ f (y+a)) x = gradient f (x+a) := by
  have hd := (hf.differentiable (by simp) (x+a)).hasFDerivAt.comp x ((hasFDerivAt_id x).add_const a)
  have he := hd.fderiv
  simp only [ContinuousLinearMap.comp_id] at he
  exact congrArg (fun L : E3 →L[ℝ] ℝ ↦ (InnerProductSpace.toDual ℝ E3).symm L) he

noncomputable def translatePair (a : E3) : SobolevPair →L[ℝ] SobolevPair :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ ValueL2 DerivativeL2).symm.toContinuousLinearMap.comp
    (((translateL2 a).comp (WithLp.fstL 2 ℝ ValueL2 DerivativeL2)).prod
      ((translateL2 a).comp (WithLp.sndL 2 ℝ ValueL2 DerivativeL2)))

noncomputable def DirichletTest.translate {R : ℝ} (u : DirichletTest R) (a : E3) :
    DirichletTest (R+‖a‖) := by
  refine ⟨fun x ↦ (u:E3 → ℝ) (x+a), u.property.1.comp (contDiff_id.add contDiff_const), ?_, ?_⟩
  · exact u.property.2.1.comp_homeomorph (Homeomorph.addRight a)
  · intro x hx
    have hxs : x+a ∈ tsupport (u:E3 → ℝ) := by
      exact (tsupport_comp_subset_preimage (f:=fun x : E3 ↦ x+a) (u:E3 → ℝ) (continuous_id.add continuous_const)) hx
    have hnorm : ‖x+a‖ < R := by simpa using u.property.2.2 hxs
    have htriangle := norm_sub_le (x+a) a
    simp only [add_sub_cancel_right] at htriangle
    simp only [Metric.mem_ball,dist_zero_right]
    linarith

lemma translatePair_test (R : ℝ) (a : E3) (u : DirichletTest R) :
    translatePair a (testGraph R u) = testGraph (R+‖a‖) (u.translate a) := by
  apply (WithLp.prodContinuousLinearEquiv 2 ℝ ValueL2 DerivativeL2).injective
  apply Prod.ext
  · change translateL2 a (testValueLinear R u) = testValueLinear (R+‖a‖) (u.translate a)
    apply Lp.ext
    have ht := (measurePreserving_add_right (volume : Measure E3) a).quasiMeasurePreserving
    filter_upwards [translateL2_coe a (testValueLinear R u),
      ht.ae u.value_memLp.coeFn_toLp,(u.translate a).value_memLp.coeFn_toLp] with x h1 h2 h3
    change (translateL2 a (testValueLinear R u)) x = ((u.translate a).value_memLp.toLp _) x
    rw [h1,h3]
    exact h2
  · change translateL2 a (testDerivativeLinear R u) = testDerivativeLinear (R+‖a‖) (u.translate a)
    apply Lp.ext
    have ht := (measurePreserving_add_right (volume : Measure E3) a).quasiMeasurePreserving
    filter_upwards [translateL2_coe a (testDerivativeLinear R u),
      ht.ae u.derivative_memLp.coeFn_toLp,(u.translate a).derivative_memLp.coeFn_toLp] with x h1 h2 h3
    change (translateL2 a (testDerivativeLinear R u)) x = ((u.translate a).derivative_memLp.toLp _) x
    rw [h1,h3]
    change (u.derivative_memLp.toLp _) (x+a) = gradient (fun y ↦ (u:E3 → ℝ) (y+a)) x
    rw [gradient_translate u.property.1]
    exact h2

lemma translatePair_mem (R : ℝ) (a : E3) (u : ZeroSobolev R) :
    translatePair a (u:SobolevPair) ∈ zeroSobolevSpace (R+‖a‖) := by
  have hclosed : IsClosed ((translatePair a) ⁻¹' (zeroSobolevSpace (R+‖a‖) : Set SobolevPair)) :=
    (testGraph (R+‖a‖)).range.isClosed_topologicalClosure.preimage (translatePair a).continuous
  apply closure_minimal (s:=Set.range (testGraph R)) ?_ hclosed u.property
  rintro _ ⟨v,rfl⟩
  change translatePair a (testGraph R v) ∈ zeroSobolevSpace (R+‖a‖)
  rw [translatePair_test]
  exact subset_closure ⟨v.translate a,rfl⟩

noncomputable def translateSobolev (R : ℝ) (a : E3) (u : ZeroSobolev R) : ZeroSobolev (R+‖a‖) :=
  ⟨translatePair a u,translatePair_mem R a u⟩

lemma smooth_compact_derivative_lipschitz {f : E3 → ℝ} (hf : ContDiff ℝ ∞ f)
    (hs : HasCompactSupport f) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x y, ‖fderiv ℝ f y - fderiv ℝ f x‖ ≤ B * ‖y-x‖ := by
  have hdf : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (by simp)
  obtain ⟨B,hB⟩ := ContDiff.lipschitzWith_of_hasCompactSupport (hs.fderiv ℝ) hdf (by simp)
  refine ⟨(B:ℝ),B.coe_nonneg,fun x y ↦ ?_⟩
  exact hB.norm_sub_le y x

lemma smooth_compact_taylor_bound {f : E3 → ℝ} (hf : ContDiff ℝ ∞ f)
    (B : ℝ) (hB : 0 ≤ B)
    (hbound : ∀ x y, ‖fderiv ℝ f y - fderiv ℝ f x‖ ≤ B * ‖y-x‖) (x y : E3) :
    ‖f y-f x-fderiv ℝ f x (y-x)‖ ≤ B * ‖y-x‖^2 := by
  have hh := (convex_closedBall x ‖y-x‖).norm_image_sub_le_of_norm_fderiv_le'
    (φ:=fderiv ℝ f x) (fun z _ ↦ hf.differentiable (by simp) z)
    (C:=B*‖y-x‖) (fun z hz ↦ (hbound x z).trans
      (mul_le_mul_of_nonneg_left (by simpa only [Metric.mem_closedBall,dist_eq_norm] using hz) hB))
    (Metric.mem_closedBall_self (norm_nonneg _))
    (by simp only [Metric.mem_closedBall,dist_eq_norm]; exact le_rfl)
  simpa only [pow_two,mul_assoc] using hh

lemma translateL2_zero {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (u : Lp V 2 (volume : Measure E3)) : translateL2 0 u = u := by
  apply Lp.ext
  filter_upwards [translateL2_coe 0 u] with x hx
  simpa using hx

lemma translateL2_add {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (a b : E3) (u : Lp V 2 (volume : Measure E3)) :
    translateL2 a (translateL2 b u) = translateL2 (a+b) u := by
  apply Lp.ext
  have ht := (measurePreserving_add_right (volume : Measure E3) a).quasiMeasurePreserving
  filter_upwards [translateL2_coe a (translateL2 b u), ht.ae (translateL2_coe b u),
    translateL2_coe (a+b) u] with x h1 h2 h3
  rw [h1,h2,h3,add_assoc]

lemma translateL2_inner {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (a : E3) (u v : Lp V 2 (volume : Measure E3)) :
    ⟪translateL2 a u,v⟫_ℝ = ⟪u,translateL2 (-a) v⟫_ℝ := by
  have hv : v = translateL2 a (translateL2 (-a) v) := by
    rw [translateL2_add,add_neg_cancel,translateL2_zero]
  rw [hv]
  change ⟪(Lp.compMeasurePreservingₗᵢ ℝ (fun x : E3 ↦ x+a)
    (measurePreserving_add_right volume a)) u,
    (Lp.compMeasurePreservingₗᵢ ℝ (fun x : E3 ↦ x+a)
    (measurePreserving_add_right volume a)) (translateL2 (-a) v)⟫_ℝ = _
  rw [LinearIsometry.inner_map_map]
  rw [translateL2_add,translateL2_add]
  simp

lemma test_taylor_error_vanishes {R : ℝ} (u : DirichletTest R) (a : E3) (h : ℝ)
    (hh : ‖h‖ ≤ 1) (x : E3) (hx : |R|+‖a‖+1 ≤ ‖x‖) :
    (u:E3 → ℝ) (x+h • a) - (u:E3 → ℝ) x - h * fderiv ℝ (u:E3 → ℝ) x a = 0 := by
  have hn : x ∉ tsupport (u:E3 → ℝ) := by
    intro hs
    have hn : ‖x‖ < R := by simpa using u.property.2.2 hs
    have := le_abs_self R
    have := norm_nonneg a
    linarith
  have hn' : x+h • a ∉ tsupport (u:E3 → ℝ) := by
    intro hs
    have hnx : ‖x+h • a‖ < R := by simpa using u.property.2.2 hs
    have hd : ‖h • a‖ ≤ ‖a‖ := by
      rw [norm_smul]
      exact mul_le_of_le_one_left (norm_nonneg a) hh
    have ht := norm_sub_le (x+h • a) (h • a)
    simp only [add_sub_cancel_right] at ht
    have := le_abs_self R
    linarith
  rw [image_eq_zero_of_notMem_tsupport hn', image_eq_zero_of_notMem_tsupport hn,
    fderiv_of_notMem_tsupport ℝ hn]
  simp

noncomputable def testDirection {R : ℝ} (u : DirichletTest R) (a : E3) : ValueL2 :=
  (smooth_direction_memLp u.property.1 u.property.2.1 a).toLp _

lemma test_taylor_error_coe {R : ℝ} (u : DirichletTest R) (a : E3) (h : ℝ) :
    ((translateL2 (h • a) (testValueLinear R u) - testValueLinear R u - h • testDirection u a : ValueL2) : E3 → ℝ)
      =ᵐ[volume] fun x ↦ (u:E3 → ℝ) (x+h • a) - (u:E3 → ℝ) x - h * fderiv ℝ (u:E3 → ℝ) x a := by
  have ht := (measurePreserving_add_right (volume : Measure E3) (h • a)).quasiMeasurePreserving
  filter_upwards [translateL2_coe (h • a) (testValueLinear R u),ht.ae u.value_memLp.coeFn_toLp,
    u.value_memLp.coeFn_toLp,(smooth_direction_memLp u.property.1 u.property.2.1 a).coeFn_toLp,
    Lp.coeFn_smul h (testDirection u a),
    Lp.coeFn_sub (translateL2 (h • a) (testValueLinear R u)) (testValueLinear R u),
    Lp.coeFn_sub (translateL2 (h • a) (testValueLinear R u)-testValueLinear R u) (h • testDirection u a)]
    with x h1 h2 h3 h4 h5 h6 h7
  rw [h7,Pi.sub_apply,h6,Pi.sub_apply,h5,Pi.smul_apply,h1]
  change (u.value_memLp.toLp _) (x+h • a) - (u.value_memLp.toLp _) x -
    h * ((smooth_direction_memLp u.property.1 u.property.2.1 a).toLp _) x = _
  rw [h2,h3,h4]

lemma test_translation_taylor (R : ℝ) (u : DirichletTest R) (a : E3) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ h : ℝ, ‖h‖ ≤ 1 →
      ‖translateL2 (h • a) (testValueLinear R u) -testValueLinear R u-h • testDirection u a‖ ≤ K * ‖h‖^2 := by
  obtain ⟨B,hB,hbound⟩ := smooth_compact_derivative_lipschitz u.property.1 u.property.2.1
  let M := |R|+‖a‖+1

  let I : ValueL2 := indicatorConstLp 2 Metric.isClosed_closedBall.measurableSet
    (isCompact_closedBall (0:E3) M).measure_lt_top.ne (1:ℝ)
  refine ⟨(B*‖a‖^2)*‖I‖, by positivity, fun h hh ↦ ?_⟩
  have hbnd : ‖translateL2 (h • a) (testValueLinear R u) -testValueLinear R u-h • testDirection u a‖ ≤
      (B*‖h‖^2*‖a‖^2)*‖I‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [test_taylor_error_coe u a h,
      indicatorConstLp_coeFn (p:=2) (hs:=Metric.isClosed_closedBall.measurableSet)
        (hμs:=(isCompact_closedBall (0:E3) M).measure_lt_top.ne) (c:=(1:ℝ))] with x he hi
    rw [he,hi]
    by_cases hx : x ∈ Metric.closedBall (0:E3) M
    · rw [Set.indicator_of_mem hx,norm_one,mul_one]
      have hb := smooth_compact_taylor_bound u.property.1 B hB hbound x (x+h • a)
      simpa only [add_sub_cancel_left,map_smul,smul_eq_mul,norm_smul,mul_pow,mul_assoc] using hb
    · rw [Set.indicator_of_notMem hx,norm_zero,mul_zero]
      have hx' : M ≤ ‖x‖ := by
        simp only [Metric.mem_closedBall,dist_zero_right,not_le] at hx
        exact hx.le
      rw [test_taylor_error_vanishes u a h hh x hx']
      simp
  calc
    _ ≤ (B*‖h‖^2*‖a‖^2)*‖I‖ := hbnd
    _ = (B*‖a‖^2)*‖I‖*‖h‖^2 := by ring

lemma test_translation_hasDerivAt_zero (R : ℝ) (u : DirichletTest R) (a : E3) :
    HasDerivAt (fun t : ℝ ↦ translateL2 (t • a) (testValueLinear R u)) (testDirection u a) 0 := by
  obtain ⟨K,hK,hbound⟩ := test_translation_taylor R u a
  rw [hasDerivAt_iff_tendsto]
  simp only [sub_zero,zero_smul,translateL2_zero]
  apply squeeze_zero' (Eventually.of_forall fun h ↦ mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) (norm_nonneg _))
    (g:=fun h : ℝ ↦ K*‖h‖)
  · filter_upwards [Metric.ball_mem_nhds (0:ℝ) (by norm_num : 0 < (1:ℝ))] with h hh
    have hh' : ‖h‖ ≤ 1 := by
      have hx : ‖h‖ < 1 := by simpa only [Metric.mem_ball,dist_zero_right] using hh
      exact hx.le
    calc
      _ ≤ ‖h‖⁻¹ * (K*‖h‖^2) := mul_le_mul_of_nonneg_left (hbound h hh') (inv_nonneg.mpr (norm_nonneg _))
      _ = K*‖h‖ := by
        by_cases hh0 : h = 0
        · simp [hh0]
        · have hhne : ‖h‖ ≠ 0 := norm_ne_zero_iff.mpr hh0
          field_simp

  · simpa using (tendsto_const_nhds.mul (continuous_norm.tendsto (0:ℝ)) : Tendsto (fun h : ℝ ↦ K*‖h‖) (𝓝 0) (𝓝 (K*‖(0:ℝ)‖)))

lemma test_translation_hasDerivAt (R : ℝ) (u : DirichletTest R) (a : E3) (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ translateL2 (s • a) (testValueLinear R u))
      (translateL2 (t • a) (testDirection u a)) t := by
  have h0 := (translateL2 (t • a)).hasFDerivAt.comp_hasDerivAt 0 (test_translation_hasDerivAt_zero R u a)
  have ht := (show HasDerivAt _ _ (t-t) by simpa only [sub_self] using h0).comp_sub_const t t
  apply ht.congr_of_eventuallyEq
  apply Eventually.of_forall
  intro s
  change translateL2 (s • a) (testValueLinear R u) = translateL2 (t • a) (translateL2 ((s-t) • a) (testValueLinear R u))
  rw [translateL2_add,← add_smul]
  congr 2
  ring_nf

lemma testDirection_norm_le (R : ℝ) (u : DirichletTest R) (a : E3) :
    ‖testDirection u a‖ ≤ ‖a‖ * ‖testDerivativeLinear R u‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [(smooth_direction_memLp u.property.1 u.property.2.1 a).coeFn_toLp,
    u.derivative_memLp.coeFn_toLp] with x h1 h2
  change ‖((smooth_direction_memLp u.property.1 u.property.2.1 a).toLp _) x‖ ≤ ‖a‖ * ‖(u.derivative_memLp.toLp _) x‖
  rw [h1,h2,gradient_norm_fderiv]
  simpa only [mul_comm] using (fderiv ℝ (u:E3 → ℝ) x).le_opNorm a

lemma test_translation_bound (R : ℝ) (u : DirichletTest R) (a : E3) :
    ‖translateL2 a (testValueLinear R u)-testValueLinear R u‖ ≤ ‖a‖ * ‖testDerivativeLinear R u‖ := by
  have h := norm_image_sub_le_of_norm_deriv_le_segment_01'
    (fun t _ ↦ (test_translation_hasDerivAt R u a t).hasDerivWithinAt)
    (C:=‖testDirection u a‖) (fun t _ ↦ (translateL2_norm (t • a) (testDirection u a)).le)
  have h' : ‖translateL2 a (testValueLinear R u)-testValueLinear R u‖ ≤ ‖testDirection u a‖ := by
    simpa only [one_smul,zero_smul,translateL2_zero] using h
  exact h'.trans (testDirection_norm_le R u a)

lemma sobolev_translation_bound (R : ℝ) (u : ZeroSobolev R) (a : E3) :
    ‖translateL2 a (sobolevValue R u)-sobolevValue R u‖ ≤ ‖a‖ * ‖sobolevDerivative R u‖ := by
  have hc : IsClosed {z : SobolevPair | ‖translateL2 a z.fst-z.fst‖ ≤ ‖a‖ * ‖z.snd‖} :=
    isClosed_le (by fun_prop) (by fun_prop)
  apply closure_minimal (s:=Set.range (testGraph R)) ?_ hc u.property
  rintro _ ⟨v,rfl⟩
  exact test_translation_bound R v a

end HarmonicCounterexample.Main.SmoothMetric3

end

end OAI
