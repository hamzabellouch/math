import OAI.Geometry.EinsteinFour.GeodesicGeometry04
import OAI.Geometry.EinsteinFour.ScalarRegularity06
import OAI.Geometry.EinsteinFour.WeylEstimates03

namespace OAI


section

/-! Actual chart integral formulas for the L2 and covariant energy
pairings against a compactly supported orthonormal-frame test. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix MeasureTheory Set Function
open scoped BigOperators Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] {g : SmoothMetric M} {o : FrameOrientation g}

omit [T3Space M] in
theorem twoFormLocalNabla_zero_off (c : M) (S : Mat4) (a : FourSpace → TwoFormFour)
    (z : FourSpace) (hz : z ∉ tsupport a) (i : Fin 4) :
    twoFormLocalNabla (g := g) c S a i z = 0 := by
  have he : a =ᶠ[𝓝 z] fun _ => 0 := notMem_tsupport_iff_eventuallyEq.mp hz
  unfold twoFormLocalNabla
  rw [he.fderiv_eq, he.self_of_nhds]
  simp only [fderiv_const_apply, _root_.zero_apply, zero_add]
  change (twoFormSkewActionLinear (twoFormExtract (chartTwoFormConnection (g := g) c S i z))) 0 = 0
  exact map_zero _

theorem twoFormGramTest_support (c : M) (S : Mat4)
    (a : FourSpace → TwoFormFour) (ha : ContDiffOn ℝ ∞ a (chartAt FourSpace c).target)
    {K : Set FourSpace} (hK : IsCompact K) (hKt : K ⊆ (chartAt FourSpace c).target)
    (has : tsupport a ⊆ K) :
    tsupport (twoFormGramTest o c S a ha hK hKt has).val ⊆ (chartAt FourSpace c).symm '' K :=
  twoFormChartTest_support c _ _ _ hK hKt _

theorem twoFormGramTest_pairing (u : smoothTwoForms o)
    (c : M) (S : Mat4) (hS : Sᵀ * S = 1)
    (a : FourSpace → TwoFormFour) (ha : ContDiffOn ℝ ∞ a (chartAt FourSpace c).target)
    {K : Set FourSpace} (hK : IsCompact K) (hKt : K ⊆ (chartAt FourSpace c).target)
    (has : tsupport a ⊆ K) (U : Set FourSpace) (hU : IsOpen U)
    (hUt : U ⊆ (chartAt FourSpace c).target) (hKU : K ⊆ U)
    (hp : ∀ w (hw : w ∈ U), chartGramSection g c S hS ⟨w, hUt hw⟩ ∈ o.positive)
    (z : FourSpace) (hz : z ∈ (chartAt FourSpace c).target) :
    twoFormCovariantPairing o u.val (twoFormGramTest o c S a ha hK hKt has).val
      ((chartAt FourSpace c).symm z) =
      ∑ i, ∑ j, (metricInChart g c z)⁻¹ i j *
        inner ℝ (twoFormLocalNabla (g := g) c S (twoFormChartValue o u.val c S hS) i z)
          (twoFormLocalNabla (g := g) c S a j z) := by
  by_cases hzU : z ∈ U
  · rw [u.property.covariantPairing_chart (twoFormGramTest o c S a ha hK hKt has).property
      c S hS U hU hUt hp z hzU]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [twoFormGramTest_nabla c S hS a ha hK hKt has z hz j]
  · have hzK : z ∉ K := fun h => hzU (hKU h)
    have hxK : (chartAt FourSpace c).symm z ∉ (chartAt FourSpace c).symm '' K := by
      rintro ⟨w, hw, he⟩
      have he' := congrArg (chartAt FourSpace c) he
      rw [(chartAt FourSpace c).right_inv (hKt hw), (chartAt FourSpace c).right_inv hz] at he'
      exact hzK (he' ▸ hw)
    have hleft : twoFormCovariantPairing o u.val (twoFormGramTest o c S a ha hK hKt has).val
        ((chartAt FourSpace c).symm z) = 0 :=
      image_eq_zero_of_notMem_tsupport (fun h => hxK
        (twoFormGramTest_support c S a ha hK hKt has
          (twoFormCovariantPairing_tsupport_right _ _ h)))
    rw [hleft]
    have hn (j : Fin 4) := twoFormLocalNabla_zero_off (g := g) c S a z
      (fun h => hzK (has h)) j
    simp only [hn, inner_zero_right, mul_zero, Finset.sum_const_zero]

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [Nonempty M]

omit [CompactSpace M] [Nonempty M] in
theorem smoothTwoFormL2Inner_gramTest (u : smoothTwoForms o)
    (c : M) (S : Mat4) (hS : Sᵀ * S = 1)
    (a : FourSpace → TwoFormFour) (ha : ContDiffOn ℝ ∞ a (chartAt FourSpace c).target)
    {K : Set FourSpace} (hK : IsCompact K) (hKt : K ⊆ (chartAt FourSpace c).target)
    (has : tsupport a ⊆ K) :
    smoothTwoFormL2Inner u (twoFormGramTest o c S a ha hK hKt has) =
      (normalizedChartFactor g).toReal * ∫ z in (chartAt FourSpace c).target,
        chartVolumeDensity g c z * inner ℝ (twoFormChartValue o u.val c S hS z) (a z) := by
  unfold smoothTwoFormL2Inner
  rw [normalizedVolume_integral_chart g c _ (by
    intro x hx
    have hn : x ∉ tsupport (twoFormGramTest o c S a ha hK hKt has).val := by
      intro h
      obtain ⟨z, hz, rfl⟩ := twoFormGramTest_support c S a ha hK hKt has h
      exact hx ((chartAt FourSpace c).map_target (hKt hz))
    rw [image_eq_zero_of_notMem_tsupport hn, inner_zero_right])]
  congr 1
  apply setIntegral_congr_fun (chartAt FourSpace c).open_target.measurableSet
  intro z hz
  have he := twoFormFrameValue_inner (o := o) u.val
    (twoFormGramTest o c S a ha hK hKt has).val (chartGramSection g c S hS ⟨z, hz⟩)
  change inner ℝ (twoFormFrameValue o u.val (chartGramSection g c S hS ⟨z, hz⟩))
    (twoFormFrameValue o (twoFormGramTest o c S a ha hK hKt has).val
      (chartGramSection g c S hS ⟨z, hz⟩)) =
    inner ℝ (u.val ((chartAt FourSpace c).symm z))
      ((twoFormGramTest o c S a ha hK hKt has).val ((chartAt FourSpace c).symm z)) at he
  have he' : inner ℝ (twoFormChartValue o u.val c S hS z)
      (twoFormChartValue o (twoFormGramTest o c S a ha hK hKt has).val c S hS z) =
      inner ℝ (u.val ((chartAt FourSpace c).symm z))
        ((twoFormGramTest o c S a ha hK hKt has).val ((chartAt FourSpace c).symm z)) := by
    simpa only [twoFormChartValue, dite_eq_left hz] using he
  rw [twoFormGramTest_value c S hS a ha hK hKt has z hz] at he'
  exact congrArg (fun r : ℝ => chartVolumeDensity g c z * r) he'.symm

omit [CompactSpace M] [Nonempty M] in
theorem smoothTwoFormCovariantEnergy_gramTest (u : smoothTwoForms o)
    (c : M) (S : Mat4) (hS : Sᵀ * S = 1)
    (a : FourSpace → TwoFormFour) (ha : ContDiffOn ℝ ∞ a (chartAt FourSpace c).target)
    {K : Set FourSpace} (hK : IsCompact K) (hKt : K ⊆ (chartAt FourSpace c).target)
    (has : tsupport a ⊆ K) (U : Set FourSpace) (hU : IsOpen U)
    (hUt : U ⊆ (chartAt FourSpace c).target) (hKU : K ⊆ U)
    (hp : ∀ w (hw : w ∈ U), chartGramSection g c S hS ⟨w, hUt hw⟩ ∈ o.positive) :
    smoothTwoFormCovariantEnergy u (twoFormGramTest o c S a ha hK hKt has) =
      (normalizedChartFactor g).toReal * ∫ z in (chartAt FourSpace c).target,
        chartVolumeDensity g c z * (∑ i, ∑ j, (metricInChart g c z)⁻¹ i j *
          inner ℝ (twoFormLocalNabla (g := g) c S (twoFormChartValue o u.val c S hS) i z)
            (twoFormLocalNabla (g := g) c S a j z)) := by
  unfold smoothTwoFormCovariantEnergy
  rw [normalizedVolume_integral_chart g c _ (by
    intro x hx
    apply image_eq_zero_of_notMem_tsupport
    intro h
    obtain ⟨z, hz, rfl⟩ := twoFormGramTest_support c S a ha hK hKt has
      (twoFormCovariantPairing_tsupport_right _ _ h)
    exact hx ((chartAt FourSpace c).map_target (hKt hz)))]
  congr 1
  apply setIntegral_congr_fun (chartAt FourSpace c).open_target.measurableSet
  intro z hz
  exact congrArg (fun r : ℝ => chartVolumeDensity g c z * r)
    (twoFormGramTest_pairing u c S hS a ha hK hKt has U hU hUt hKU hp z hz)

end
end PositiveEinsteinFour.Geometry
end


section

/-! An intrinsic continuous scalar controls the local first jet of a
smooth two-form. Its L2 norm is bounded by twice the actual H1 norm. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

local instance twoFormControl_probability : IsProbabilityMeasure (normalizedVolume g) :=
  normalizedVolume_isProbability (actual_finitePositiveVolume g)

def twoFormValueNorm (u : smoothTwoForms o) : C(M, ℝ) :=
  ⟨fun x => ‖u.val x‖, smoothTwoForm_norm_continuous u⟩

def twoFormEnergyRoot (u : smoothTwoForms o) : C(M, ℝ) :=
  ⟨fun x => Real.sqrt (twoFormCovariantPairing o u.val u.val x),
    Real.continuous_sqrt.comp (u.property.covariantPairing_continuous u.property)⟩

def twoFormControl (u : smoothTwoForms o) : C(M, ℝ) := twoFormValueNorm u + twoFormEnergyRoot u

omit [T3Space M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [Nonempty M] in
theorem twoFormControl_nonneg (u : smoothTwoForms o) (x : M) : 0 ≤ twoFormControl u x := by
  change 0 ≤ ‖u.val x‖ + Real.sqrt (twoFormCovariantPairing o u.val u.val x)
  positivity

def twoFormValueNormL2 (u : smoothTwoForms o) : Lp ℝ 2 (normalizedVolume g) :=
  ContinuousMap.toLp 2 (normalizedVolume g) ℝ (twoFormValueNorm u)

def twoFormEnergyRootL2 (u : smoothTwoForms o) : Lp ℝ 2 (normalizedVolume g) :=
  ContinuousMap.toLp 2 (normalizedVolume g) ℝ (twoFormEnergyRoot u)

def twoFormControlL2 (u : smoothTwoForms o) : Lp ℝ 2 (normalizedVolume g) :=
  ContinuousMap.toLp 2 (normalizedVolume g) ℝ (twoFormControl u)

theorem twoFormValueNormL2_coe (u : smoothTwoForms o) :
    twoFormValueNormL2 u =ᵐ[normalizedVolume g] fun x => ‖u.val x‖ :=
  ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) (normalizedVolume g) (twoFormValueNorm u)

theorem twoFormValueNormL2_norm_sq (u : smoothTwoForms o) :
    ‖twoFormValueNormL2 u‖ ^ 2 = smoothTwoFormL2Inner u u := by
  rw [← real_inner_self_eq_norm_sq]
  change inner ℝ (ContinuousMap.toLp 2 (normalizedVolume g) ℝ (twoFormValueNorm u))
    (ContinuousMap.toLp 2 (normalizedVolume g) ℝ (twoFormValueNorm u)) = _
  rw [ContinuousMap.inner_toLp, smoothTwoFormL2Inner_self]
  apply integral_congr_ae
  filter_upwards [] with x
  change ‖u.val x‖ * ‖u.val x‖ = ‖u.val x‖ ^ 2
  ring

theorem twoFormEnergyRootL2_norm_sq (u : smoothTwoForms o) :
    ‖twoFormEnergyRootL2 u‖ ^ 2 = smoothTwoFormCovariantEnergy u u := by
  rw [← real_inner_self_eq_norm_sq]
  change inner ℝ (ContinuousMap.toLp 2 (normalizedVolume g) ℝ (twoFormEnergyRoot u))
    (ContinuousMap.toLp 2 (normalizedVolume g) ℝ (twoFormEnergyRoot u)) = _
  rw [ContinuousMap.inner_toLp]
  apply integral_congr_ae
  filter_upwards [] with x
  change Real.sqrt (twoFormCovariantPairing o u.val u.val x) *
    Real.sqrt (twoFormCovariantPairing o u.val u.val x) = _
  rw [← pow_two, Real.sq_sqrt (twoFormCovariantPairing_self_nonneg o u.val x)]

theorem twoFormControlL2_norm_le (u : SmoothH1TwoForm o) :
    ‖twoFormControlL2 (u : smoothTwoForms o)‖ ≤ 2 * ‖u‖ := by
  have hv : ‖twoFormValueNormL2 (u : smoothTwoForms o)‖ ≤ ‖u‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    have h₁ := twoFormValueNormL2_norm_sq (u : smoothTwoForms o)
    have h₂ := smoothH1TwoForm_norm_sq u
    have h₃ := smoothTwoFormCovariantEnergy_nonneg (u : smoothTwoForms o)
    linarith only [h₁, h₂, h₃]
  have he : ‖twoFormEnergyRootL2 (u : smoothTwoForms o)‖ ≤ ‖u‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    have h₁ := twoFormEnergyRootL2_norm_sq (u : smoothTwoForms o)
    have h₂ := smoothH1TwoForm_norm_sq u
    have h₃ := smoothTwoFormL2Inner_nonneg (u : smoothTwoForms o)
    linarith only [h₁, h₂, h₃]
  have hid : twoFormControlL2 (u : smoothTwoForms o) =
      twoFormValueNormL2 (u : smoothTwoForms o) + twoFormEnergyRootL2 (u : smoothTwoForms o) :=
    map_add (ContinuousMap.toLp 2 (normalizedVolume g) ℝ) _ _
  rw [hid]
  exact (norm_add_le _ _).trans ((add_le_add hv he).trans_eq (by ring))

end
end PositiveEinsteinFour.Geometry
end


section

/-! Bounded extension of the metric's actual curvature action to L2
two-forms. No bound on curvature is an additional input. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

omit [MeasurableSpace M] [BorelSpace M] [Nonempty M] in
theorem twoFormCurvatureField_bound :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (u : M → TwoFormFour) (x : M),
      ‖twoFormCurvatureField o u x‖ ≤ A * ‖u x‖ := by
  obtain ⟨C, hC, hb⟩ := twoFormMetricCurvatureTensor_bound g
  refine ⟨‖twoFormCurvatureOperator‖ * C,
    mul_nonneg (ContinuousLinearMap.opNorm_nonneg _) hC, fun u x => ?_⟩
  exact (twoFormCurvatureAction_norm_le _ _).trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hb ⟨x,o.frame x⟩)
        (ContinuousLinearMap.opNorm_nonneg _)) (norm_nonneg _))

def smoothL2CurvatureLinear : SmoothL2TwoForm o →ₗ[ℝ] SmoothL2TwoForm o where
  toFun u := smoothTwoFormCurvature (u : smoothTwoForms o)
  map_add' u v := by
    apply Subtype.ext
    funext x
    exact map_add (twoFormCurvatureLinear _) _ _
  map_smul' r u := by
    apply Subtype.ext
    funext x
    exact map_smul (twoFormCurvatureLinear _) r _

theorem twoFormValueNormL2_eq_L2norm (u : SmoothL2TwoForm o) :
    ‖twoFormValueNormL2 (u : smoothTwoForms o)‖ = ‖u‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  have h := twoFormValueNormL2_norm_sq (u : smoothTwoForms o)
  have hi : ‖u‖ ^ 2 = smoothTwoFormL2Inner (u : smoothTwoForms o) u := by
    rw [← real_inner_self_eq_norm_sq]
    rfl
  exact h.trans hi.symm

theorem smoothL2CurvatureLinear_bound :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ u : SmoothL2TwoForm o, ‖smoothL2CurvatureLinear u‖ ≤ A * ‖u‖ := by
  obtain ⟨A, hA, hb⟩ := twoFormCurvatureField_bound (o := o)
  refine ⟨A, hA, fun u => ?_⟩
  have hLp : ‖twoFormValueNormL2 (smoothL2CurvatureLinear u : smoothTwoForms o)‖ ≤
      A * ‖twoFormValueNormL2 (u : smoothTwoForms o)‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [twoFormValueNormL2_coe (smoothL2CurvatureLinear u : smoothTwoForms o),
      twoFormValueNormL2_coe (u : smoothTwoForms o)] with x hv hu
    rw [hv, hu, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg _), abs_of_nonneg (norm_nonneg _)]
    exact hb (u : smoothTwoForms o).val x
  calc
    _ = ‖twoFormValueNormL2 (smoothL2CurvatureLinear u : smoothTwoForms o)‖ :=
      (twoFormValueNormL2_eq_L2norm (smoothL2CurvatureLinear u)).symm
    _ ≤ A * ‖twoFormValueNormL2 (u : smoothTwoForms o)‖ := hLp
    _ = A * ‖u‖ := congrArg (A * ·) (twoFormValueNormL2_eq_L2norm u)

def twoFormCurvatureBound (o : FrameOrientation g) : ℝ :=
  Classical.choose (smoothL2CurvatureLinear_bound (o := o))

theorem smoothL2CurvatureLinear_norm_le (u : SmoothL2TwoForm o) :
    ‖smoothL2CurvatureLinear u‖ ≤ twoFormCurvatureBound o * ‖u‖ :=
  (Classical.choose_spec (smoothL2CurvatureLinear_bound (o := o))).2 u

def smoothL2Curvature : SmoothL2TwoForm o →L[ℝ] SmoothL2TwoForm o :=
  (smoothL2CurvatureLinear (o := o)).mkContinuous (twoFormCurvatureBound o)
    (fun u => smoothL2CurvatureLinear_norm_le u)

def twoFormL2Curvature : TwoFormL2 o →L[ℝ] TwoFormL2 o :=
  (smoothL2Curvature (o := o)).completion

theorem twoFormL2Curvature_smooth (u : SmoothL2TwoForm o) :
    twoFormL2Curvature (smoothTwoFormToL2 u) = smoothTwoFormToL2 (smoothL2Curvature u) :=
  ContinuousLinearMap.completion_apply_coe _ u

/-- The bounded potential in `1 + ∇*∇ = 2 R - 5` for harmonic two-forms
when Ricci is normalized to `3g`. -/
def twoFormWeitzenbockPotential : TwoFormL2 o →L[ℝ] TwoFormL2 o :=
  (2 : ℝ) • twoFormL2Curvature - (5 : ℝ) • ContinuousLinearMap.id ℝ (TwoFormL2 o)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Transfer of the intrinsic two-form H1 control to supported scalar
functions on a compact coordinate set. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set
open scoped Manifold ContDiff ENNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

local instance twoFormLocalization_probability : IsProbabilityMeasure (normalizedVolume g) :=
  normalizedVolume_isProbability (actual_finitePositiveVolume g)

theorem twoForm_chart_localization_bound (g : SmoothMetric M) (o : FrameOrientation g)
    (c : M) {K : Set FourSpace} (hK : IsCompact K)
    (hKt : K ⊆ (chartAt FourSpace c).target) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ (u : SmoothH1TwoForm o) (f : FourSpace → ℝ)
      (hf : MemLp f 2 (volume : Measure FourSpace)) (C : ℝ), 0 ≤ C →
      Function.support f ⊆ K →
      (∀ z ∈ K, |f z| ≤ C * twoFormControl (u : smoothTwoForms o) ((chartAt FourSpace c).symm z)) →
      ‖hf.toLp f‖ ≤ C * L * ‖u‖ := by
  obtain ⟨D, hD, hDb⟩ := scalarChart_eLpNorm_bound g c hK hKt
  refine ⟨2 * D.toReal, mul_nonneg (by norm_num) ENNReal.toReal_nonneg, ?_⟩
  intro u f hf C hC hs hb
  let F := twoFormControl (u : smoothTwoForms o)
  have hF : MemLp F 2 (normalizedVolume g) :=
    F.continuous.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hfi : K.indicator f = f := indicator_eq_self.mpr hs
  have hlocal : eLpNorm f 2 volume ≤ ENNReal.ofReal C *
      eLpNorm (fun z => F ((chartAt FourSpace c).symm z)) 2 (volume.restrict K) := by
    calc
      _ = eLpNorm f 2 (volume.restrict K) := by
        conv_lhs => rw [← hfi]
        exact eLpNorm_indicator_eq_eLpNorm_restrict hK.isClosed.measurableSet
      _ ≤ _ := eLpNorm_le_mul_eLpNorm_of_ae_le_mul hf.aestronglyMeasurable.restrict (by
        filter_upwards [ae_restrict_mem hK.isClosed.measurableSet] with z hz
        rw [Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg (show 0 ≤ F ((chartAt FourSpace c).symm z) from twoFormControl_nonneg _ _)]
        exact hb z hz) 2
  have htotal := hlocal.trans (mul_le_mul' le_rfl (hDb F))
  have hfinite : ENNReal.ofReal C * (D * eLpNorm F 2 (normalizedVolume g)) ≠ (∞ : ℝ≥0∞) :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.mul_ne_top hD hF.eLpNorm_ne_top)
  have hr := ENNReal.toReal_mono hfinite htotal
  have hnorm : (eLpNorm F 2 (normalizedVolume g)).toReal =
      ‖twoFormControlL2 (u : smoothTwoForms o)‖ := by
    change (eLpNorm F 2 (normalizedVolume g)).toReal = ‖hF.toLp F‖
    exact (Lp.norm_toLp F hF).symm
  rw [← Lp.norm_toLp f hf] at hr
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hC, hnorm] at hr
  calc
    ‖hf.toLp f‖ ≤ C * (D.toReal * ‖twoFormControlL2 (u : smoothTwoForms o)‖) := hr
    _ ≤ C * (D.toReal * (2 * ‖u‖)) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (twoFormControlL2_norm_le u) ENNReal.toReal_nonneg) hC
    _ = _ := by ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual curvature operator is self-adjoint for the intrinsic L2
pairing; symmetry follows from the metric curvature symmetries. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix MeasureTheory
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem twoFormMetricCurvatureAction_symmetric (e : FrameBundle g) (a b : TwoFormFour) :
    inner ℝ (twoFormCurvatureAction (twoFormMetricCurvatureTensor g e) a) b =
      inner ℝ a (twoFormCurvatureAction (twoFormMetricCurvatureTensor g e) b) := by
  apply twoFormCurvatureAction_symmetric
  · intro i j k l
    change frameTensor e.frame.matrix _ ![i,j,l,k] = -frameTensor e.frame.matrix _ ![i,j,k,l]
    rw [frameTensor_curvatureCoordinates, frameTensor_curvatureCoordinates]
    exact frame_algebraic_lastSkew e.frame i j k l
  · intro i j k l
    change frameTensor e.frame.matrix _ ![k,l,i,j] = frameTensor e.frame.matrix _ ![i,j,k,l]
    rw [frameTensor_curvatureCoordinates, frameTensor_curvatureCoordinates]
    exact frame_algebraic_pairSymmetric e.frame (frame_algebraic_lastSkew e.frame) i j k l

variable [T3Space M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [Nonempty M]

theorem smoothL2Curvature_inner (u v : SmoothL2TwoForm o) :
    inner ℝ (smoothL2Curvature u) v = inner ℝ u (smoothL2Curvature v) := by
  change (∫ x, inner ℝ (twoFormCurvatureField o (u : smoothTwoForms o).val x)
    ((v : smoothTwoForms o).val x) ∂normalizedVolume g) =
      ∫ x, inner ℝ ((u : smoothTwoForms o).val x)
        (twoFormCurvatureField o (v : smoothTwoForms o).val x) ∂normalizedVolume g
  apply integral_congr_ae
  filter_upwards [] with x
  exact twoFormMetricCurvatureAction_symmetric ⟨x,o.frame x⟩ _ _

theorem twoFormL2Curvature_selfAdjoint (u v : TwoFormL2 o) :
    inner ℝ (twoFormL2Curvature u) v = inner ℝ u (twoFormL2Curvature v) := by
  have hs (b : SmoothL2TwoForm o) (a : TwoFormL2 o) :
      inner ℝ (twoFormL2Curvature a) (smoothTwoFormToL2 b) =
        inner ℝ a (twoFormL2Curvature (smoothTwoFormToL2 b)) := by
    refine UniformSpace.Completion.induction_on a
      (isClosed_eq (twoFormL2Curvature.continuous.inner continuous_const)
        (continuous_id.inner continuous_const)) ?_
    intro w
    change inner ℝ (twoFormL2Curvature (smoothTwoFormToL2 w)) (smoothTwoFormToL2 b) =
      inner ℝ (smoothTwoFormToL2 w) (twoFormL2Curvature (smoothTwoFormToL2 b))
    rw [twoFormL2Curvature_smooth, twoFormL2Curvature_smooth,
      smoothTwoFormToL2.inner_map_map, smoothTwoFormToL2.inner_map_map]
    exact smoothL2Curvature_inner w b
  refine UniformSpace.Completion.induction_on v
    (isClosed_eq (continuous_const.inner continuous_id)
      (continuous_const.inner twoFormL2Curvature.continuous)) ?_
  intro b
  exact hs b u

end
end PositiveEinsteinFour.Geometry
end


section

/-! The bounded metric curvature potential commutes with the actual
Hodge involution on an Einstein four-manifold. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem smoothL2Curvature_hodge (hRic : RicciThree g) (u : SmoothL2TwoForm o) :
    smoothL2Curvature (smoothL2Hodge u) = smoothL2Hodge (smoothL2Curvature u) := by
  apply Subtype.ext
  funext x
  exact twoFormMetricCurvatureAction_hodge hRic ⟨x,o.frame x⟩ ((u : smoothTwoForms o).val x)

theorem twoFormL2Curvature_hodge (hRic : RicciThree g) (u : TwoFormL2 o) :
    twoFormL2Curvature (twoFormL2Hodge u) = twoFormL2Hodge (twoFormL2Curvature u) := by
  refine UniformSpace.Completion.induction_on u
    (isClosed_eq (twoFormL2Curvature.continuous.comp twoFormL2Hodge.continuous)
      (twoFormL2Hodge.continuous.comp twoFormL2Curvature.continuous)) ?_
  intro v
  change twoFormL2Curvature (twoFormL2Hodge (smoothTwoFormToL2 v)) =
    twoFormL2Hodge (twoFormL2Curvature (smoothTwoFormToL2 v))
  rw [twoFormL2Hodge_smooth, twoFormL2Curvature_smooth, twoFormL2Curvature_smooth,
    twoFormL2Hodge_smooth, smoothL2Curvature_hodge hRic]

theorem twoFormWeitzenbockPotential_hodge (hRic : RicciThree g) (u : TwoFormL2 o) :
    twoFormWeitzenbockPotential (twoFormL2Hodge u) =
      twoFormL2Hodge (twoFormWeitzenbockPotential u) := by
  change (2 : ℝ) • twoFormL2Curvature (twoFormL2Hodge u) - (5 : ℝ) • twoFormL2Hodge u = _
  rw [twoFormL2Curvature_hodge hRic]
  change _ = twoFormL2Hodge ((2 : ℝ) • twoFormL2Curvature u - (5 : ℝ) • u)
  rw [map_sub, map_smul, map_smul]

end
end PositiveEinsteinFour.Geometry
end

end OAI
