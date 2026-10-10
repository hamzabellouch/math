import OAI.Analysis.StrictMeans.HorizontalAveraging

namespace OAI

section
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal ComplexConjugate
open Set Filter Metric Complex
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function MeasureTheory
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology

open Set Filter Function MeasureTheory
open scoped Topology

namespace StrictInverseFirstPower
noncomputable section

def expScalePoint (t : ℝ) : UpperHalfPlane := xyPoint 0 (Real.exp t) (Real.exp_pos t)

lemma continuous_expScalePoint : Continuous expScalePoint :=
  continuous_xyPoint continuous_const Real.continuous_exp _

lemma affineProduct_expScale (s t : ℝ) :
    affineProduct (expScalePoint s) (expScalePoint t) = expScalePoint (s + t) := by
  simp [expScalePoint, affineProduct_xyPoint, Real.exp_add]

lemma halfScale_expScale (t : ℝ) :
    affineProduct halfScalePoint (expScalePoint (t + Real.log 2)) = expScalePoint t := by
  have he : Real.exp (t + Real.log 2) = Real.exp t * 2 := by
    rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  simp [halfScalePoint, expScalePoint, affineProduct_xyPoint, he]
  congr 1
  ring

lemma expScale_horizontal (t s : ℝ) :
    affineProduct (expScalePoint t) (horizontalPoint s) =
      affineProduct (horizontalPoint (Real.exp t * s)) (expScalePoint t) := by
  simp [expScalePoint, horizontalPoint, affineProduct_xyPoint]

lemma weighted_scale_periodic (Λ : C(DiskFamily, ℝ) →L[ℝ] ℝ) (β ρ : ℝ)
    (hpower : Real.exp (β * Real.log 2) = ρ)
    (hscale : ∀ φ, Λ (affineOperator halfScalePoint φ) = ρ * Λ φ)
    (φ : C(DiskFamily, ℝ)) :
    Periodic (fun t => Real.exp (β * t) * Λ (affineOperator (expScalePoint t) φ)) (Real.log 2) := by
  intro t
  have hs := hscale (affineOperator (expScalePoint (t + Real.log 2)) φ)
  rw [← mul_apply_eq_comp, affineOperator_mul, halfScale_expScale] at hs
  change Real.exp (β * (t + Real.log 2)) * _ = _
  rw [mul_add, Real.exp_add, hpower, mul_assoc, ← hs]

lemma weighted_scale_bound (β a b : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ uIcc a b,
      ‖Real.exp (β * t) • affineOperator (expScalePoint t)‖ ≤ C := by
  obtain ⟨C, hC, hbound⟩ := affineOperator_compact_bound expScalePoint continuous_expScalePoint a b
  let : CompactSpace (uIcc a b) := isCompact_iff_compactSpace.mp isCompact_uIcc
  let W : C(uIcc a b, ℝ) := ⟨fun t => Real.exp (β * t),
    Real.continuous_exp.comp (continuous_const.mul continuous_subtype_val)⟩
  refine ⟨‖W‖ * C, mul_nonneg (norm_nonneg _) hC, fun t ht => ?_⟩
  calc
    ‖Real.exp (β * t) • affineOperator (expScalePoint t)‖ ≤
        ‖Real.exp (β * t)‖ * ‖affineOperator (expScalePoint t)‖ :=
      ContinuousLinearMap.opNorm_smul_le _ _
    _ ≤ ‖W‖ * C := mul_le_mul (W.norm_coe_le_norm ⟨t, ht⟩) (hbound t ht)
      (ContinuousLinearMap.opNorm_nonneg _) (norm_nonneg _)

def scaleAverage (Λ : C(DiskFamily, ℝ) →L[ℝ] ℝ) (β : ℝ) : C(DiskFamily, ℝ) →L[ℝ] ℝ :=
  intervalFunctional Λ (fun t => Real.exp (β * t) • affineOperator (expScalePoint t))
    (fun φ => (Real.continuous_exp.comp (continuous_const.mul continuous_id)).smul
      ((continuous_affineOperator_strong φ).comp continuous_expScalePoint))
    0 (Real.log 2) (weighted_scale_bound β 0 (Real.log 2))

@[simp] lemma scaleAverage_apply (Λ : C(DiskFamily, ℝ) →L[ℝ] ℝ) (β : ℝ)
    (φ : C(DiskFamily, ℝ)) :
    scaleAverage Λ β φ = ∫ t in 0..Real.log 2,
      Real.exp (β * t) * Λ (affineOperator (expScalePoint t) φ) := by
  simp only [scaleAverage, intervalFunctional_apply, smul_apply, map_smul,
    smul_eq_mul]

lemma scaleAverage_horizontal (Λ : C(DiskFamily, ℝ) →L[ℝ] ℝ) (β s : ℝ)
    (hΛ : ∀ x φ, Λ (affineOperator (horizontalPoint x) φ) = Λ φ)
    (φ : C(DiskFamily, ℝ)) :
    scaleAverage Λ β (affineOperator (horizontalPoint s) φ) = scaleAverage Λ β φ := by
  simp only [scaleAverage_apply]
  congr 1
  ext t
  rw [← mul_apply_eq_comp, affineOperator_mul, expScale_horizontal, ← affineOperator_mul,
    mul_apply_eq_comp, hΛ]

lemma scaleAverage_scale (Λ : C(DiskFamily, ℝ) →L[ℝ] ℝ) (β ρ s : ℝ)
    (hpower : Real.exp (β * Real.log 2) = ρ)
    (hscale : ∀ φ, Λ (affineOperator halfScalePoint φ) = ρ * Λ φ)
    (φ : C(DiskFamily, ℝ)) :
    scaleAverage Λ β (affineOperator (expScalePoint s) φ) =
      Real.exp (-β * s) * scaleAverage Λ β φ := by
  simp only [scaleAverage_apply]
  have he (t : ℝ) : Real.exp (β * t) *
      Λ (affineOperator (expScalePoint t) (affineOperator (expScalePoint s) φ)) =
      Real.exp (-β * s) * (Real.exp (β * (t + s)) *
        Λ (affineOperator (expScalePoint (t + s)) φ)) := by
    rw [← mul_apply_eq_comp, affineOperator_mul, affineProduct_expScale,
      ← mul_assoc, ← Real.exp_add]
    congr 2
    ring
  simp_rw [he]
  rw [intervalIntegral.integral_const_mul]
  have hp := weighted_scale_periodic Λ β ρ hpower hscale φ
  have hi := intervalIntegral.integral_comp_add_right
    (fun t => Real.exp (β * t) * Λ (affineOperator (expScalePoint t) φ)) s
    (a := 0) (b := Real.log 2)
  rw [hi, zero_add, add_comm (Real.log 2) s, hp.intervalIntegral_add_eq s 0, zero_add]

lemma scaleAverage_affine (Λ : C(DiskFamily, ℝ) →L[ℝ] ℝ) (β ρ : ℝ)
    (hpower : Real.exp (β * Real.log 2) = ρ)
    (hscale : ∀ φ, Λ (affineOperator halfScalePoint φ) = ρ * Λ φ)
    (hΛ : ∀ x φ, Λ (affineOperator (horizontalPoint x) φ) = Λ φ)
    (z : UpperHalfPlane) (φ : C(DiskFamily, ℝ)) :
    scaleAverage Λ β (affineOperator z φ) = z.im ^ (-β) * scaleAverage Λ β φ := by
  have he : z = affineProduct (horizontalPoint z.re) (expScalePoint (Real.log z.im)) := by
    apply UpperHalfPlane.ext
    simp [coe_affineProduct, affineAt, horizontalPoint, expScalePoint, xyPoint,
      Real.exp_log z.im_pos]
    exact (Complex.re_add_im (z : ℂ)).symm
  conv_lhs => rw [he]
  rw [← affineOperator_mul, mul_apply_eq_comp,
    scaleAverage_horizontal Λ β z.re hΛ, scaleAverage_scale Λ β ρ _ hpower hscale]
  congr 1
  rw [Real.rpow_def_of_pos z.im_pos]
  congr 1
  ring

end
end StrictInverseFirstPower

open Set Filter Function MeasureTheory
open scoped Topology

namespace StrictInverseFirstPower
noncomputable section

lemma positiveFunctional_strict (Λ : C(DiskFamily, ℝ) →L[ℝ] ℝ) (hΛ : Monotone Λ)
    (h1 : 0 < Λ 1) (φ : C(DiskFamily, ℝ)) (hφ : ∀ f, 0 < φ f) : 0 < Λ φ := by
  obtain ⟨f, _, hf⟩ := isCompact_univ.exists_isMinOn (univ_nonempty : (univ : Set DiskFamily).Nonempty)
    φ.continuous.continuousOn
  have hle : φ f • (1 : C(DiskFamily, ℝ)) ≤ φ := by
    intro g
    change φ f * 1 ≤ φ g
    rw [mul_one]
    exact hf (mem_univ g)
  have hh := hΛ hle
  rw [map_smul, smul_eq_mul] at hh
  exact lt_of_lt_of_le (mul_pos (hφ f) h1) hh

lemma positiveFunctional_affine_one (Λ : C(DiskFamily, ℝ) →L[ℝ] ℝ) (hΛ : Monotone Λ)
    (h1 : 0 < Λ 1) (z : UpperHalfPlane) : 0 < Λ (affineOperator z 1) := by
  apply positiveFunctional_strict Λ hΛ h1
  intro f
  simpa using norm_pos_iff.mpr (halfPlaneQ_ne_zero f z)

lemma horizontalAverage_monotone (Λ : C(DiskFamily, ℝ) →L[ℝ] ℝ) (hΛ : Monotone Λ) :
    Monotone (horizontalAverage Λ) := by
  intro φ ψ h
  simp only [horizontalAverage_apply]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply intervalIntegral.integral_mono (by norm_num)
    (((continuous_functional_affine Λ φ).comp continuous_horizontalPoint).intervalIntegrable _ _)
    (((continuous_functional_affine Λ ψ).comp continuous_horizontalPoint).intervalIntegrable _ _)
  intro t
  exact hΛ (affineOperator_monotone _ h)

lemma horizontalAverage_one_pos (Λ : C(DiskFamily, ℝ) →L[ℝ] ℝ) (hΛ : Monotone Λ)
    (h1 : 0 < Λ 1) : 0 < horizontalAverage Λ 1 := by
  rw [horizontalAverage_apply]
  apply mul_pos (by norm_num)
  apply intervalIntegral.intervalIntegral_pos_of_pos
    (((continuous_functional_affine Λ 1).comp continuous_horizontalPoint).intervalIntegrable _ _)
    (fun t => positiveFunctional_affine_one Λ hΛ h1 _) (by norm_num)

lemma scaleAverage_monotone (Λ : C(DiskFamily, ℝ) →L[ℝ] ℝ) (hΛ : Monotone Λ) (β : ℝ) :
    Monotone (scaleAverage Λ β) := by
  intro φ ψ h
  simp only [scaleAverage_apply]
  have hc (φ : C(DiskFamily, ℝ)) : Continuous
      (fun t => Real.exp (β * t) * Λ (affineOperator (expScalePoint t) φ)) :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
      ((continuous_functional_affine Λ φ).comp continuous_expScalePoint)
  apply intervalIntegral.integral_mono (Real.log_nonneg (by norm_num))
    ((hc φ).intervalIntegrable _ _) ((hc ψ).intervalIntegrable _ _)
  intro t
  exact mul_le_mul_of_nonneg_left (hΛ (affineOperator_monotone _ h)) (Real.exp_pos _).le

lemma scaleAverage_one_pos (Λ : C(DiskFamily, ℝ) →L[ℝ] ℝ) (hΛ : Monotone Λ)
    (h1 : 0 < Λ 1) (β : ℝ) : 0 < scaleAverage Λ β 1 := by
  rw [scaleAverage_apply]
  have hc : Continuous (fun t => Real.exp (β * t) * Λ (affineOperator (expScalePoint t) 1)) :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
      ((continuous_functional_affine Λ 1).comp continuous_expScalePoint)
  exact intervalIntegral.intervalIntegral_pos_of_pos (hc.intervalIntegrable _ _)
    (fun t => mul_pos (Real.exp_pos _) (positiveFunctional_affine_one Λ hΛ h1 _))
    (Real.log_pos (by norm_num))

lemma dyadicExponent_power : Real.exp (dyadicExponent * Real.log 2) = dyadicRadius := by
  unfold dyadicExponent dyadicRadius
  rw [div_mul_cancel₀ _ (ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 2)))]

lemma dyadicExponent_pos_iff : 0 < dyadicExponent ↔ 1 < dyadicRadius := by
  rw [dyadicExponent, dyadicRadius, Real.one_lt_exp_iff, div_pos_iff_of_pos_right
    (Real.log_pos (by norm_num))]

theorem exists_exact_affine_functional (hβ : 0 < dyadicExponent) :
    ∃ Λ : C(DiskFamily, ℝ) →L[ℝ] ℝ, Monotone Λ ∧ Λ 1 = 1 ∧
      ∀ (z : UpperHalfPlane) (φ : C(DiskFamily, ℝ)),
        Λ (affineOperator z φ) = z.im ^ (-dyadicExponent) * Λ φ := by
  obtain ⟨Λ, hΛ, h1, heigen⟩ := exists_dyadic_eigenfunctional
  have hper := eigenfunctional_horizontal_period Λ dyadicRadius
    (dyadicExponent_pos_iff.mp hβ) heigen
  let Λh := horizontalAverage Λ
  have hΛh : Monotone Λh := horizontalAverage_monotone Λ hΛ
  have hh1 : 0 < Λh 1 := horizontalAverage_one_pos Λ hΛ (by rw [h1]; norm_num)
  let ν := scaleAverage Λh dyadicExponent
  have hν : Monotone ν := scaleAverage_monotone Λh hΛh _
  have hν1 : 0 < ν 1 := scaleAverage_one_pos Λh hΛh hh1 _
  refine ⟨(ν 1)⁻¹ • ν, ?_, ?_, ?_⟩
  · intro φ ψ h
    exact mul_le_mul_of_nonneg_left (hν h) (inv_nonneg.mpr hν1.le)
  · change (ν 1)⁻¹ * ν 1 = 1
    exact inv_mul_cancel₀ hν1.ne'
  · intro z φ
    change (ν 1)⁻¹ * ν (affineOperator z φ) = z.im ^ (-dyadicExponent) * ((ν 1)⁻¹ * ν φ)
    rw [show ν (affineOperator z φ) = z.im ^ (-dyadicExponent) * ν φ from
      scaleAverage_affine Λh dyadicExponent dyadicRadius dyadicExponent_power
        (horizontalAverage_halfScale Λ dyadicRadius hper heigen)
        (horizontalAverage_invariant Λ hper) z φ]
    ring

theorem exists_exact_affine_probability_continuous (hβ : 0 < dyadicExponent) :
    ∃ μ : ProbabilityMeasure DiskFamily, ∀ (z : UpperHalfPlane) (φ : C(DiskFamily, ℝ)),
      (∫ f, ‖halfPlaneQ f z‖ * φ (rebase f z) ∂(μ : Measure DiskFamily)) =
        z.im ^ (-dyadicExponent) * ∫ f, φ f ∂(μ : Measure DiskFamily) := by
  obtain ⟨Λ, hΛ, h1, hlaw⟩ := exists_exact_affine_functional hβ
  obtain ⟨μ, hμ⟩ := exists_probabilityMeasure_of_positiveFunctional Λ hΛ h1
  refine ⟨μ, fun z φ => ?_⟩
  change (∫ f, affineOperator z φ f ∂(μ : Measure DiskFamily)) = _
  rw [hμ, hμ, hlaw]

end
end StrictInverseFirstPower

open Set Filter Function MeasureTheory
open scoped Topology ENNReal NNReal

namespace StrictInverseFirstPower
noncomputable section

def weightedRebaseMeasure (μ : Measure DiskFamily) (z : UpperHalfPlane) : Measure DiskFamily :=
  (μ.withDensity (fun f => ‖halfPlaneQ f z‖₊)).map (fun f => rebase f z)

lemma measurable_rebase_fixed (z : UpperHalfPlane) : Measurable (fun f => rebase f z) :=
  (continuous_rebase.comp (continuous_id.prodMk continuous_const)).measurable

lemma measurable_Qnorm_fixed (z : UpperHalfPlane) : Measurable (fun f => ‖halfPlaneQ f z‖₊) :=
  ((continuous_halfPlaneQ.comp (continuous_id.prodMk continuous_const)).nnnorm).measurable

instance weightedRebaseMeasure_isFinite (μ : Measure DiskFamily) [IsFiniteMeasure μ]
    (z : UpperHalfPlane) : IsFiniteMeasure (weightedRebaseMeasure μ z) := by
  have hi : Integrable (fun f => halfPlaneQ f z) μ :=
    (continuous_halfPlaneQ.comp (continuous_id.prodMk continuous_const)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have : IsFiniteMeasure (μ.withDensity (fun f => ‖halfPlaneQ f z‖₊)) :=
    isFiniteMeasure_withDensity hi.hasFiniteIntegral.ne
  unfold weightedRebaseMeasure
  infer_instance

lemma weightedRebaseMeasure_integral (μ : Measure DiskFamily) (z : UpperHalfPlane)
    (φ : C(DiskFamily, ℝ)) :
    (∫ f, φ f ∂weightedRebaseMeasure μ z) = ∫ f, affineOperator z φ f ∂μ := by
  rw [weightedRebaseMeasure, integral_map (measurable_rebase_fixed z).aemeasurable
    φ.continuous.aestronglyMeasurable, integral_withDensity_eq_integral_smul (measurable_Qnorm_fixed z)]
  rfl

lemma weightedRebaseMeasure_lintegral (μ : Measure DiskFamily) (z : UpperHalfPlane)
    (φ : DiskFamily → ℝ≥0∞) (hφ : Measurable φ) :
    (∫⁻ f, φ f ∂weightedRebaseMeasure μ z) =
      ∫⁻ f, (‖halfPlaneQ f z‖₊ : ℝ≥0∞) * φ (rebase f z) ∂μ := by
  rw [weightedRebaseMeasure, lintegral_map hφ (measurable_rebase_fixed z)]
  exact lintegral_withDensity_eq_lintegral_mul _ (measurable_Qnorm_fixed z).coe_nnreal_ennreal
    (hφ.comp (measurable_rebase_fixed z))

lemma weightedRebaseMeasure_eq_smul (μ : ProbabilityMeasure DiskFamily) (β : ℝ)
    (hlaw : ∀ (z : UpperHalfPlane) (φ : C(DiskFamily, ℝ)),
      (∫ f, affineOperator z φ f ∂(μ : Measure DiskFamily)) =
        z.im ^ (-β) * ∫ f, φ f ∂(μ : Measure DiskFamily)) (z : UpperHalfPlane) :
    weightedRebaseMeasure (μ : Measure DiskFamily) z =
      ENNReal.ofReal (z.im ^ (-β)) • (μ : Measure DiskFamily) := by
  have : IsFiniteMeasure (ENNReal.ofReal (z.im ^ (-β)) • (μ : Measure DiskFamily)) :=
    ⟨by simp [Measure.smul_apply]⟩
  apply MeasureTheory.ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro φ
  change (∫ f, φ.toContinuousMap f ∂weightedRebaseMeasure (μ : Measure DiskFamily) z) =
    ∫ f, φ.toContinuousMap f ∂ENNReal.ofReal (z.im ^ (-β)) • (μ : Measure DiskFamily)
  rw [weightedRebaseMeasure_integral _ _ φ.toContinuousMap, hlaw]
  rw [integral_smul_measure, ENNReal.toReal_ofReal (Real.rpow_nonneg z.im_pos.le _)]
  rfl

theorem exists_exact_affine_probability (hβ : 0 < dyadicExponent) :
    ∃ μ : ProbabilityMeasure DiskFamily, ∀ (z : UpperHalfPlane)
      (φ : DiskFamily → ℝ≥0∞), Measurable φ →
      (∫⁻ f, (‖halfPlaneQ f z‖₊ : ℝ≥0∞) * φ (rebase f z) ∂(μ : Measure DiskFamily)) =
        ENNReal.ofReal (z.im ^ (-dyadicExponent)) * ∫⁻ f, φ f ∂(μ : Measure DiskFamily) := by
  obtain ⟨μ, hμ⟩ := exists_exact_affine_probability_continuous hβ
  refine ⟨μ, fun z φ hφ => ?_⟩
  rw [← weightedRebaseMeasure_lintegral _ _ _ hφ,
    weightedRebaseMeasure_eq_smul μ dyadicExponent hμ z, lintegral_smul_measure]
  rfl

end
end StrictInverseFirstPower

end

end OAI
