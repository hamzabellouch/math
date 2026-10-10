import Mathlib
import OAI.Analysis.AffineBernstein.WeightedDivergence

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

section CompactIntegration

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [μ.IsAddHaarMeasure]

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
/-- Integrability uses continuity only on a compact set containing the support. -/
theorem integrable_of_support_subset_compact {f : E → ℝ} {K : Set E}
    (hK : IsCompact K) (hs : Function.support f ⊆ K) (hf : ContinuousOn f K) :
    Integrable f μ :=
  (integrableOn_iff_integrable_of_support_subset hs).mp
    (ContinuousOn.integrableOn_compact hK hf)

/-- Compact support of the test function removes any global regularity requirement
on the coefficient. This is the integration-by-parts form used on the original Ω. -/
theorem integral_mul_fderiv_compact (f g : E → ℝ) (v : E)
    (hf : ∀ x ∈ tsupport g, ContDiffAt ℝ 1 f x)
    (hg : ContDiff ℝ 1 g) (hgc : HasCompactSupport g) :
    (∫ x, f x * fderiv ℝ g x v ∂μ) =
      -(∫ x, fderiv ℝ f x v * g x ∂μ) := by
  have hf0 : ContinuousOn f (tsupport g) := fun x hx =>
    (hf x hx).continuousAt.continuousWithinAt
  have hf1 : ContinuousOn (fun x => fderiv ℝ f x v) (tsupport g) := fun x hx =>
    (((hf x hx).fderiv_right (m := 0) (by norm_num)).continuousAt.clm_apply
      continuousAt_const).continuousWithinAt
  have hg1 : Continuous (fun x => fderiv ℝ g x v) :=
    (hg.continuous_fderiv (by norm_num)).clm_apply continuous_const
  apply integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
  · exact integrable_of_support_subset_compact hgc.isCompact
      ((Function.support_mul_subset_right _ _).trans (subset_tsupport g))
      (hf1.mul hg.continuous.continuousOn)
  · exact integrable_of_support_subset_compact hgc.isCompact
      ((Function.support_mul_subset_right _ _).trans
        ((subset_tsupport _).trans (tsupport_fderiv_apply_subset ℝ v)))
      (hf0.mul hg1.continuousOn)
  · exact integrable_of_support_subset_compact hgc.isCompact
      ((Function.support_mul_subset_right _ _).trans (subset_tsupport g))
      (hf0.mul hg.continuous.continuousOn)
  · intro x hx
    exact (hf x hx).differentiableAt (by norm_num)
  · intro x hx
    exact hg.differentiable (by norm_num) x

/-- Two integrations by parts, without an artificial globally smooth coefficient. -/
theorem integral_mul_second_fderiv_compact (a η : E → ℝ) (v z : E)
    (ha : ∀ x ∈ tsupport η, ContDiffAt ℝ 2 a x)
    (hη : ContDiff ℝ 2 η) (hηc : HasCompactSupport η) :
    (∫ x, a x * fderiv ℝ (fun y => fderiv ℝ η y v) x z ∂μ) =
      ∫ x, fderiv ℝ (fun y => fderiv ℝ a y z) x v * η x ∂μ := by
  have hdη : ContDiff ℝ 1 (fun y => fderiv ℝ η y v) :=
    (hη.fderiv_right (by norm_num)).clm_apply contDiff_const
  have hda : ∀ x ∈ tsupport η, ContDiffAt ℝ 1 (fun y => fderiv ℝ a y z) x :=
    fun x hx => ((ha x hx).fderiv_right (by norm_num)).clm_apply contDiffAt_const
  rw [integral_mul_fderiv_compact a (fun y => fderiv ℝ η y v) z
    (fun x hx => (ha x (tsupport_fderiv_apply_subset ℝ v hx)).of_le (by norm_num))
    hdη (hηc.fderiv_apply ℝ v)]
  rw [integral_mul_fderiv_compact _ η v hda (hη.of_le (by norm_num)) hηc, neg_neg]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Global smoothness of a fixed-direction derivative. -/
theorem contDiff_dirDeriv {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (v : E) :
    ContDiff ℝ ∞ (dirDeriv v f) :=
  (hf.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

/-- The weak double-divergence formula with precisely a compactly supported test. -/
theorem integral_double_contraction_compact {ι : Type*} [Fintype ι]
    (a : ι → ι → E → ℝ) (e : ι → E) (η : E → ℝ)
    (ha : ∀ i j x, x ∈ tsupport η → ContDiffAt ℝ ∞ (a i j) x)
    (hη : ContDiff ℝ ∞ η) (hηc : HasCompactSupport η) :
    (∫ x, ∑ i, ∑ j, a i j x * dirDeriv (e i) (dirDeriv (e j) η) x ∂μ) =
      ∫ x, (∑ j, ∑ i, dirDeriv (e j) (dirDeriv (e i) (a i j)) x) * η x ∂μ := by
  have hleft (i j : ι) : Integrable
      (fun x => a i j x * dirDeriv (e i) (dirDeriv (e j) η) x) μ := by
    apply integrable_of_support_subset_compact hηc.isCompact
    · exact (Function.support_mul_subset_right _ _).trans
        ((subset_tsupport _).trans ((tsupport_fderiv_apply_subset ℝ (e i)).trans
          (tsupport_fderiv_apply_subset ℝ (e j))))
    · exact (show ContinuousOn (a i j) (tsupport η) from
        fun x hx => (ha i j x hx).continuousAt.continuousWithinAt).mul
        ((contDiff_dirDeriv (contDiff_dirDeriv hη (e j)) (e i)).continuous.continuousOn)
  have hright (i j : ι) : Integrable
      (fun x => dirDeriv (e j) (dirDeriv (e i) (a i j)) x * η x) μ := by
    apply integrable_of_support_subset_compact hηc.isCompact
    · exact (Function.support_mul_subset_right _ _).trans (subset_tsupport η)
    · exact (show ContinuousOn (dirDeriv (e j) (dirDeriv (e i) (a i j))) (tsupport η) from
        fun x hx => (contDiffAt_dirDeriv (contDiffAt_dirDeriv (ha i j x hx) (e i)) (e j)).continuousAt.continuousWithinAt).mul
        hη.continuous.continuousOn
  calc
    _ = ∑ i, ∑ j, ∫ x, a i j x * dirDeriv (e i) (dirDeriv (e j) η) x ∂μ := by
      rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hleft i j))]
      apply Finset.sum_congr rfl
      intro i hi
      exact integral_finsetSum _ (fun j _ => hleft i j)
    _ = ∑ i, ∑ j, ∫ x, dirDeriv (e j) (dirDeriv (e i) (a i j)) x * η x ∂μ := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      exact integral_mul_second_fderiv_compact (a i j) η (e j) (e i)
        (fun x hx => (ha i j x hx).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
        (hη.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)) hηc
    _ = _ := by
      rw [Finset.sum_comm]
      simp_rw [Finset.sum_mul]
      rw [integral_finsetSum _ (fun j _ => integrable_finsetSum _ (fun i _ => hright i j))]
      apply Finset.sum_congr rfl
      intro j hj
      exact (integral_finsetSum _ (fun i _ => hright i j)).symm

end CompactIntegration

/-- Graph-direction stationarity for the source's equation and actual coefficient.
All regularity of `u` is needed only on the original open domain. -/
theorem affineMaximal_weak_stationarity {n : ℕ} {Ω : Set (Space n)} (hΩ : IsOpen Ω)
    {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
    (hpos : ∀ y ∈ Ω, (hessian u y).PosDef) (hmax : AffineMaximalOn Ω u)
    (η : Space n → ℝ) (hη : ContDiff ℝ ∞ η) (hηc : HasCompactSupport η)
    (hηΩ : tsupport η ⊆ Ω) :
    (∫ x, ∑ i, ∑ j, affineWeight u x * cofactorHessian u x i j * hessian η x i j) = 0 := by
  have ha (i j : Fin n) (x : Space n) (hx : x ∈ tsupport η) :
      ContDiffAt ℝ ∞ (fun y => affineWeight u y * cofactorHessian u y i j) x :=
    (contDiffAt_affineWeight (hu.contDiffAt (hΩ.mem_nhds (hηΩ hx))) (hpos x (hηΩ hx))).mul
      (contDiffAt_cofactorHessian_entry hΩ hu hpos (hηΩ hx) i j)
  change (∫ x, ∑ i, ∑ j, affineWeight u x * cofactorHessian u x i j *
    dirDeriv (coordinateVector n i) (dirDeriv (coordinateVector n j) η) x) = 0
  rw [integral_double_contraction_compact (fun i j x => affineWeight u x * cofactorHessian u x i j)
    (coordinateVector n) η ha hη hηc]
  apply integral_eq_zero_of_ae
  filter_upwards [] with x
  by_cases hx : η x = 0
  · rw [hx, mul_zero]
    rfl
  · have hxΩ := hηΩ (subset_tsupport η hx)
    rw [affine_operator_eq_double_divergence hΩ hu hpos hxΩ, hmax x hxΩ, zero_mul]
    rfl

/-- The density of affine area in the original graph coordinates. -/
def affineAreaDensity {n : ℕ} (u : Space n → ℝ) (x : Space n) : ℝ :=
  Real.rpow (hessian u x).det (1 / ((n : ℝ) + 2))

/-- The variation coefficient has exactly the exponent in the manuscript. -/
theorem affineWeight_mul_det {n : ℕ} {u : Space n → ℝ} {x : Space n}
    (hpos : (hessian u x).PosDef) :
    affineWeight u x * (hessian u x).det = affineAreaDensity u x := by
  unfold affineWeight affineAreaDensity
  simp only [Real.rpow_eq_pow]
  rw [← Real.rpow_add_one (ne_of_gt hpos.det_pos)]
  congr 1
  have hn : (n : ℝ) + 2 ≠ 0 := by positivity
  field_simp
  ring

/-- `wU` is not a surrogate for the affine-area coefficient. -/
theorem affine_weight_cofactor_entry {n : ℕ} {u : Space n → ℝ} {x : Space n}
    (hpos : (hessian u x).PosDef) (i j : Fin n) :
    affineWeight u x * cofactorHessian u x i j =
      affineAreaDensity u x * (hessian u x)⁻¹ i j := by
  change affineWeight u x * ((hessian u x).det * (hessian u x)⁻¹ i j) = _
  rw [← mul_assoc, affineWeight_mul_det hpos]

/-- The source's first-variation integral, over its original open domain. -/
theorem affineMaximal_area_stationarity {n : ℕ} {Ω : Set (Space n)} (hΩ : IsOpen Ω)
    {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
    (hpos : ∀ y ∈ Ω, (hessian u y).PosDef) (hmax : AffineMaximalOn Ω u)
    (η : Space n → ℝ) (hη : ContDiff ℝ ∞ η) (hηc : HasCompactSupport η)
    (hηΩ : tsupport η ⊆ Ω) :
    (∫ x in Ω, affineAreaDensity u x *
      (∑ i, ∑ j, (hessian u x)⁻¹ i j * hessian η x i j)) = 0 := by
  have hzero (x : Space n) (hx : x ∉ Ω) (i j : Fin n) : hessian η x i j = 0 := by
    have hn : x ∉ tsupport η := fun h => hx (hηΩ h)
    unfold hessian
    rw [fderiv_of_notMem_tsupport ℝ (fun h => hn (tsupport_fderiv_apply_subset ℝ _ h))]
    rfl
  calc
    _ = ∫ x in Ω, ∑ i, ∑ j,
        affineWeight u x * cofactorHessian u x i j * hessian η x i j := by
      apply setIntegral_congr_fun hΩ.measurableSet
      intro x hx
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      rw [affine_weight_cofactor_entry (hpos x hx), mul_assoc]
    _ = ∫ x, ∑ i, ∑ j,
        affineWeight u x * cofactorHessian u x i j * hessian η x i j :=
      setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
        simp only [hzero x hx, mul_zero, Finset.sum_const_zero]
    _ = 0 := affineMaximal_weak_stationarity hΩ hu hpos hmax η hη hηc hηΩ

end AffineBernstein
end

end OAI
