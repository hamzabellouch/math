import OAI.Analysis.StrictMeans.RegularTargets

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
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology ENNReal NNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
open Set Filter Metric Complex MeasureTheory
open scoped Topology
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
open Set Filter Complex
open scoped Topology
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
open Set Filter Metric Complex
open scoped Topology
open Set Filter Metric Complex
open scoped Topology
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal ComplexConjugate
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff
open Set Filter Metric Complex MeasureTheory
open scoped Topology
open Set Filter Metric Complex MeasureTheory
open scoped Topology ContDiff
open Set Filter Metric Complex MeasureTheory
open scoped Topology ContDiff
open Set Filter Metric Complex MeasureTheory
open scoped Topology ContDiff
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
open Set Filter MeasureTheory
open scoped Topology
open Set Filter Metric Complex MeasureTheory
open scoped Topology
open Set Filter Metric Complex MeasureTheory
open scoped Topology
open Set Filter MeasureTheory Complex
open scoped Topology
open Set Filter MeasureTheory
open scoped Topology

open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
namespace StrictInverseFirstPower
noncomputable section

lemma real_complex_log_norm_fderiv {H : ℂ → ℂ} {ξ : ℂ}
    (hH : DifferentiableAt ℝ H ξ) (hne : H ξ ≠ 0) (v : ℂ) :
    fderiv ℝ (fun η => Real.log ‖H η‖) ξ v = ((fderiv ℝ H ξ v) / H ξ).re := by
  have hh := ((hH.hasFDerivAt.norm_sq).log
    (pow_ne_zero 2 (norm_ne_zero_iff.mpr hne))).const_mul (1/2)
  have he : (fun η => (1/2:ℝ) * Real.log (‖H η‖^2)) = (fun η => Real.log ‖H η‖) := by
    funext η
    rw [Real.log_pow]
    ring
  rw [he] at hh
  rw [hh.fderiv]
  simp only [smul_apply, ContinuousLinearMap.comp_apply, smul_eq_mul, innerSL_apply_apply]
  simp only [Complex.inner, Complex.mul_re, Complex.div_re, Complex.conj_re, Complex.conj_im]
  rw [← Complex.normSq_eq_norm_sq]
  field_simp
  ring

lemma logPotential_branch_contDiffAt {k : ℝ} {F Z : ℂ → ℂ} {ξ : ℂ}
    (hF : AnalyticAt ℂ F (Z ξ)) (hZ : ContDiffAt ℝ 1 Z ξ)
    (hy : 0 < (Z ξ).im) (hp : F (Z ξ) ≠ ξ) :
    ContDiffAt ℝ 1 (fun η => logPotential k F η (Z η)) ξ := by
  have hh := (hF.restrictScalars (𝕜 := ℝ)).contDiffAt (n := 1)
  exact (contDiffAt_const.mul ((Complex.imCLM.contDiff.contDiffAt.comp ξ hZ).log hy.ne')).sub
    ((((hh.comp ξ hZ).sub contDiffAt_id).norm ℝ (sub_ne_zero.mpr hp)).log
      (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hp)))

lemma critical_branch_derivative {k : ℝ} {F Z : ℂ → ℂ} {ξ : ℂ}
    (hk : k ≠ 0) (hy : 0 < (Z ξ).im) (hF : DifferentiableAt ℂ F (Z ξ))
    (hp : F (Z ξ) ≠ ξ) (hZ : DifferentiableAt ℝ Z ξ)
    (hG : criticalMap k F (Z ξ) = ξ) (v : ℂ) :
    fderiv ℝ (fun η => logPotential k F η (Z η)) ξ v = (v / (F (Z ξ)-ξ)).re := by
  have h1 := (((Complex.imCLM.hasFDerivAt (x := Z ξ)).comp ξ hZ.hasFDerivAt).log hy.ne').const_mul k
  change HasFDerivAt (fun η => k * Real.log (Z η).im)
    (k • (Z ξ).im⁻¹ • (Complex.imCLM.comp (fderiv ℝ Z ξ))) ξ at h1
  have hpr : DifferentiableAt ℝ (fun η => F (Z η)-η) ξ :=
    ((hF.restrictScalars (𝕜 := ℝ)).comp ξ hZ).sub differentiableAt_id
  have h2 := (hpr.norm ℝ (sub_ne_zero.mpr hp)).log
    (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hp))
  have hcomp : fderiv ℝ (fun η => F (Z η)-η) ξ v =
      deriv F (Z ξ) * fderiv ℝ Z ξ v - v := by
    have hd := ((hF.hasDerivAt.complexToReal_fderiv).comp ξ hZ.hasFDerivAt).sub (hasFDerivAt_id ξ)
    change (fderiv ℝ (F ∘ Z - id) ξ) v = _
    rw [hd.fderiv]
    simp only [sub_apply, ContinuousLinearMap.comp_apply, one_apply_eq_self,
      ContinuousLinearMap.id_apply, smul_apply, smul_eq_mul]
  change (fderiv ℝ ((fun η => k * Real.log (Z η).im) -
    (fun η => Real.log ‖F (Z η)-η‖)) ξ) v = _
  rw [fderiv_sub h1.differentiableAt h2, sub_apply, h1.fderiv,
    real_complex_log_norm_fderiv hpr (sub_ne_zero.mpr hp), hcomp]
  simp only [smul_apply, smul_eq_mul, ContinuousLinearMap.comp_apply, Complex.imCLM_apply]
  have hz := congrArg (fun L : ℂ →L[ℝ] ℝ => L (fderiv ℝ Z ξ v))
    ((logPotential_critical_iff hk hy hF hp).mpr hG)
  rw [logPotential_fderiv_apply hy hF hp, zero_apply] at hz
  have he : (deriv F (Z ξ) * fderiv ℝ Z ξ v - v) / (F (Z ξ)-ξ) =
      (deriv F (Z ξ) / (F (Z ξ)-ξ)) * fderiv ℝ Z ξ v - v/(F (Z ξ)-ξ) := by ring
  rw [he, Complex.sub_re]
  linear_combination hz

lemma critical_branch_difference_nz {k : ℝ} {F Z W : ℂ → ℂ} {ξ : ℂ}
    (hk : k ≠ 0) (hZy : 0 < (Z ξ).im) (hWy : 0 < (W ξ).im)
    (hFZ : DifferentiableAt ℂ F (Z ξ)) (hFW : DifferentiableAt ℂ F (W ξ))
    (hpZ : F (Z ξ) ≠ ξ) (hpW : F (W ξ) ≠ ξ)
    (hZ : DifferentiableAt ℝ Z ξ) (hW : DifferentiableAt ℝ W ξ)
    (hGZ : criticalMap k F (Z ξ) = ξ) (hGW : criticalMap k F (W ξ) = ξ)
    (hne : F (Z ξ) ≠ F (W ξ)) :
    fderiv ℝ (fun η => logPotential k F η (Z η) - logPotential k F η (W η)) ξ ≠ 0 := by
  have hdZ : DifferentiableAt ℝ (fun η => logPotential k F η (Z η)) ξ := by
    exact (((Complex.imCLM.differentiableAt.comp ξ hZ).log hZy.ne').const_mul k).sub
      (((((hFZ.restrictScalars (𝕜 := ℝ)).comp ξ hZ).sub differentiableAt_id).norm ℝ
        (sub_ne_zero.mpr hpZ)).log (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hpZ)))
  have hdW : DifferentiableAt ℝ (fun η => logPotential k F η (W η)) ξ := by
    exact (((Complex.imCLM.differentiableAt.comp ξ hW).log hWy.ne').const_mul k).sub
      (((((hFW.restrictScalars (𝕜 := ℝ)).comp ξ hW).sub differentiableAt_id).norm ℝ
        (sub_ne_zero.mpr hpW)).log (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hpW)))
  intro hh
  have he (v : ℂ) : (v / (F (Z ξ)-ξ)).re = (v/(F (W ξ)-ξ)).re := by
    have h := congrArg (fun L : ℂ →L[ℝ] ℝ => L v) hh
    change (fderiv ℝ ((fun η => logPotential k F η (Z η)) -
      (fun η => logPotential k F η (W η))) ξ) v = (0 : ℂ →L[ℝ] ℝ) v at h
    rw [fderiv_sub hdZ hdW, sub_apply, critical_branch_derivative hk hZy hFZ hpZ hZ hGZ,
      critical_branch_derivative hk hWy hFW hpW hW hGW, zero_apply] at h
    exact sub_eq_zero.mp h
  have hc : (F (Z ξ)-ξ)⁻¹ = (F (W ξ)-ξ)⁻¹ := by
    apply Complex.ext
    · simpa only [one_div] using he 1
    · have ht := he I
      simp only [div_eq_mul_inv, I_mul_re] at ht
      linarith
  have hc' := inv_injective hc
  exact hne (by simpa using congrArg (fun w : ℂ => w + ξ) hc')

end
end StrictInverseFirstPower

open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
namespace StrictInverseFirstPower
noncomputable section

lemma singular_values_null {G : ℂ → ℂ} {U : Set ℂ}
    (hG : ∀ z ∈ U, DifferentiableAt ℝ G z) :
    volume (G '' {z ∈ U | (fderiv ℝ G z).det = 0}) = 0 := by
  apply MeasureTheory.addHaar_image_eq_zero_of_det_fderivWithin_eq_zero volume
    (f' := fderiv ℝ G)
  · intro z hz
    exact (hG z hz.1).hasFDerivAt.hasFDerivWithinAt
  · intro z hz
    exact hz.2

lemma criticalMap_contDiffOn (k : ℝ) (f : DiskFamily) :
    ContDiffOn ℝ 1 (criticalMap k (halfPlaneFunction f)) {z : ℂ | 0 < z.im} := by
  intro z hz
  exact ((criticalMap_contDiffAt k f hz).of_le (by simp)).contDiffWithinAt

lemma logPotential_eq_log_criticalHeight {k : ℝ} (f : DiskFamily) {ξ z : ℂ}
    (hk : 0 < k) (hz : 0 < z.im) (hg : criticalMap k (halfPlaneFunction f) z = ξ) :
    logPotential k (halfPlaneFunction f) ξ z = Real.log (criticalHeight k (halfPlaneFunction f) z) := by
  have hp : halfPlaneFunction f z ≠ ξ := by
    intro he
    exact criticalMap_ne_image hk.ne' hz (halfPlaneFunction_deriv_ne_zero f hz) (hg.trans he.symm)
  rw [← criticalHeight_value hk hz hg, Real.log_div
    (Real.rpow_pos_of_pos hz k).ne' (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hp)),
    Real.log_rpow hz]
  unfold logPotential
  rw [mul_comm k]

lemma critical_inverse_chart_data {k : ℝ} (hk : k ≠ 0) (f : DiskFamily)
    (e : OpenPartialHomeomorph ℂ ℂ) (he : (e : ℂ → ℂ) = criticalMap k (halfPlaneFunction f))
    (hs : e.source ⊆ {z ∈ {z : ℂ | 0 < z.im} | (fderiv ℝ (criticalMap k (halfPlaneFunction f)) z).det ≠ 0})
    {ξ : ℂ} (hξ : ξ ∈ e.target) :
    0 < (e.symm ξ).im ∧ halfPlaneFunction f (e.symm ξ) ≠ ξ ∧
      criticalMap k (halfPlaneFunction f) (e.symm ξ) = ξ := by
  have hy := (hs (e.map_target hξ)).1
  have hg : criticalMap k (halfPlaneFunction f) (e.symm ξ) = ξ := by
    rw [← he]
    exact e.right_inv hξ
  refine ⟨hy,?_,hg⟩
  intro hp
  exact criticalMap_ne_image hk hy (halfPlaneFunction_deriv_ne_zero f hy) (hg.trans hp.symm)

lemma critical_inverse_branch_contDiffOn {k : ℝ} (hk : k ≠ 0) (f : DiskFamily)
    (e : OpenPartialHomeomorph ℂ ℂ) (he : (e : ℂ → ℂ) = criticalMap k (halfPlaneFunction f))
    (hs : e.source ⊆ {z ∈ {z : ℂ | 0 < z.im} | (fderiv ℝ (criticalMap k (halfPlaneFunction f)) z).det ≠ 0})
    (hd : ContDiffOn ℝ 1 e.symm e.target) :
    ContDiffOn ℝ 1 (fun ξ => logPotential k (halfPlaneFunction f) ξ (e.symm ξ)) e.target := by
  intro ξ hξ
  obtain ⟨hy,hp,_⟩ := critical_inverse_chart_data hk f e he hs hξ
  exact (logPotential_branch_contDiffAt
    ((halfPlaneFunction_differentiableOn f).analyticAt (isOpen_halfPlane.mem_nhds hy))
    (hd.contDiffAt (e.open_target.mem_nhds hξ)) hy hp).contDiffWithinAt

lemma inverse_chart_pair_ties_null {k : ℝ} (hk : k ≠ 0) (f : DiskFamily)
    (e d : OpenPartialHomeomorph ℂ ℂ)
    (he : (e : ℂ → ℂ) = criticalMap k (halfPlaneFunction f))
    (hd : (d : ℂ → ℂ) = criticalMap k (halfPlaneFunction f))
    (heS : e.source ⊆ {z ∈ {z : ℂ | 0 < z.im} | (fderiv ℝ (criticalMap k (halfPlaneFunction f)) z).det ≠ 0})
    (hdS : d.source ⊆ {z ∈ {z : ℂ | 0 < z.im} | (fderiv ℝ (criticalMap k (halfPlaneFunction f)) z).det ≠ 0})
    (heD : ContDiffOn ℝ 1 e.symm e.target) (hdD : ContDiffOn ℝ 1 d.symm d.target) :
    volume {ξ | ξ ∈ e.target ∧ ξ ∈ d.target ∧ e.symm ξ ≠ d.symm ξ ∧
      logPotential k (halfPlaneFunction f) ξ (e.symm ξ) =
        logPotential k (halfPlaneFunction f) ξ (d.symm ξ)} = 0 := by
  let U := e.target ∩ d.target
  let V := {ξ ∈ U | e.symm ξ ≠ d.symm ξ}
  let φ := fun ξ => logPotential k (halfPlaneFunction f) ξ (e.symm ξ) -
    logPotential k (halfPlaneFunction f) ξ (d.symm ξ)
  have hU : IsOpen U := e.open_target.inter d.open_target
  have hV : IsOpen V := by
    have ht := (e.continuousOn_symm.mono inter_subset_left |>.sub
      (d.continuousOn_symm.mono inter_subset_right)).isOpen_inter_preimage hU
        (isOpen_compl_singleton (x := (0:ℂ)))
    convert ht using 1
    ext ξ
    simp only [V,U, mem_inter_iff, mem_ofPred_eq,
      mem_preimage, mem_compl_iff, mem_singleton_iff, Pi.sub_apply, sub_ne_zero]
  have hφ : ContDiffOn ℝ 1 φ V :=
    ((critical_inverse_branch_contDiffOn hk f e he heS heD).mono
      (fun _ hx => hx.1.1)).sub
      ((critical_inverse_branch_contDiffOn hk f d hd hdS hdD).mono (fun _ hx => hx.1.2))
  have hn (ξ : ℂ) (hξ : ξ ∈ V) : fderiv ℝ φ ξ ≠ 0 := by
    obtain ⟨hy,hp,hg⟩ := critical_inverse_chart_data hk f e he heS hξ.1.1
    obtain ⟨hy',hp',hg'⟩ := critical_inverse_chart_data hk f d hd hdS hξ.1.2
    exact critical_branch_difference_nz hk hy hy'
      ((halfPlaneFunction_differentiableOn f).differentiableAt (isOpen_halfPlane.mem_nhds hy))
      ((halfPlaneFunction_differentiableOn f).differentiableAt (isOpen_halfPlane.mem_nhds hy')) hp hp'
      ((heD.contDiffAt (e.open_target.mem_nhds hξ.1.1)).differentiableAt one_ne_zero)
      ((hdD.contDiffAt (d.open_target.mem_nhds hξ.1.2)).differentiableAt one_ne_zero) hg hg'
      (fun hh => hξ.2 (halfPlaneFunction_injOn f hy hy' hh))
  apply measure_mono_null (t := {ξ ∈ V | φ ξ = 0 ∧ fderiv ℝ φ ξ ≠ 0}) _
    (complex_regular_level_null hV hφ)
  intro ξ hξ
  have hv : ξ ∈ V := ⟨⟨hξ.1,hξ.2.1⟩,hξ.2.2.1⟩
  exact ⟨hv,sub_eq_zero.mpr hξ.2.2.2,hn ξ hv⟩

theorem ae_regular_distinct_critical_heights {k : ℝ} (hk : 0 < k) (f : DiskFamily) :
    ∀ᵐ ξ : ℂ,
      (∀ z : UpperHalfPlane, criticalMap k (halfPlaneFunction f) z = ξ →
        jacobianExpression k (halfPlaneFunction f) z ≠ 0) ∧
      (∀ z w : UpperHalfPlane, criticalMap k (halfPlaneFunction f) z = ξ →
        criticalMap k (halfPlaneFunction f) w = ξ →
        criticalHeight k (halfPlaneFunction f) z = criticalHeight k (halfPlaneFunction f) w → z = w) := by
  classical
  let G := criticalMap k (halfPlaneFunction f)
  let H := {z : ℂ | 0 < z.im}
  have hc : ContDiffOn ℝ 1 G H := criticalMap_contDiffOn k f
  have hs := singular_values_null (U := H) (G := G)
    (fun z hz => (hc.contDiffAt (isOpen_halfPlane.mem_nhds hz)).differentiableAt one_ne_zero)
  have ha : ∀ᵐ ξ : ℂ, ξ ∉ G '' {z ∈ H | (fderiv ℝ G z).det = 0} := by
    apply ae_iff.mpr
    simpa only [not_not, ofPred_mem_eq] using hs
  obtain ⟨C,hC,hcharts,hcover⟩ := countable_regular_inverse_charts isOpen_halfPlane hc
  have : Countable C := hC.to_subtype
  have ht : ∀ᵐ ξ : ℂ, ∀ e d : C,
      ¬ (ξ ∈ e.1.target ∧ ξ ∈ d.1.target ∧ e.1.symm ξ ≠ d.1.symm ξ ∧
        logPotential k (halfPlaneFunction f) ξ (e.1.symm ξ) =
          logPotential k (halfPlaneFunction f) ξ (d.1.symm ξ)) := by
    apply ae_all_iff.mpr
    intro e
    apply ae_all_iff.mpr
    intro d
    apply ae_iff.mpr
    simpa only [not_not] using inverse_chart_pair_ties_null hk.ne' f e.1 d.1
      (hcharts e.1 e.2).1 (hcharts d.1 d.2).1
      (hcharts e.1 e.2).2.1 (hcharts d.1 d.2).2.1
      (hcharts e.1 e.2).2.2 (hcharts d.1 d.2).2.2
  filter_upwards [ha,ht] with ξ hξ htξ
  have hreg (z : ℂ) (hz : z ∈ H) (hg : G z = ξ) : (fderiv ℝ G z).det ≠ 0 := by
    intro hh
    exact hξ ⟨z,⟨hz,hh⟩,hg⟩
  refine ⟨?_,?_⟩
  · intro z hz
    exact fun hJ => hreg z z.im_pos hz ((jacobianExpression_zero_iff k hk.ne' f z.im_pos).mp hJ)
  · intro z w hz hw hv
    by_contra hne
    have hzR : (z:ℂ) ∈ {z ∈ H | (fderiv ℝ G z).det ≠ 0} := ⟨z.im_pos,hreg z z.im_pos hz⟩
    have hwR : (w:ℂ) ∈ {z ∈ H | (fderiv ℝ G z).det ≠ 0} := ⟨w.im_pos,hreg w w.im_pos hw⟩
    obtain ⟨e,he,hze⟩ := mem_iUnion₂.mp (hcover hzR)
    obtain ⟨d,hd,hwd⟩ := mem_iUnion₂.mp (hcover hwR)
    have heξ : e z = ξ := by rw [(hcharts e he).1]; exact hz
    have hdξ : d w = ξ := by rw [(hcharts d hd).1]; exact hw
    have hξe : ξ ∈ e.target := heξ ▸ e.map_source hze
    have hξd : ξ ∈ d.target := hdξ ▸ d.map_source hwd
    have hzeq : e.symm ξ = z := heξ ▸ e.left_inv hze
    have hwdeq : d.symm ξ = w := hdξ ▸ d.left_inv hwd
    apply htξ ⟨e,he⟩ ⟨d,hd⟩
    refine ⟨hξe,hξd,?_,?_⟩
    · rw [hzeq,hwdeq]
      exact fun hh => hne (UpperHalfPlane.ext hh)
    · rw [hzeq,hwdeq, logPotential_eq_log_criticalHeight f hk z.im_pos hz,
        logPotential_eq_log_criticalHeight f hk w.im_pos hw,hv]

theorem affine_law_ae_good_pairs (μ : ProbabilityMeasure DiskFamily) (β : ℝ)
    (hβ : 0 ≤ β)
    (hlaw : ∀ (z : UpperHalfPlane) (φ : DiskFamily → ℝ≥0∞), Measurable φ →
      (∫⁻ f, (‖halfPlaneQ f z‖₊ : ℝ≥0∞) * φ (rebase f z) ∂(μ : Measure DiskFamily)) =
        ENNReal.ofReal (z.im ^ (-β)) * ∫⁻ f, φ f ∂(μ : Measure DiskFamily)) :
    ∀ᵐ f ∂(μ : Measure DiskFamily), ∀ᵐ ξ : ℂ, GoodPair ((β+2)/3) (f,ξ) := by
  filter_upwards [weightedAreaTail_ae_finite μ β hlaw] with f hf
  filter_upwards [ae_compact_positive_superlevels f β hβ hf,ae_regular_distinct_critical_heights (by linarith : 0 < (β+2)/3) f]
    with ξ hc hr
  exact ⟨hc,hr⟩

end
end StrictInverseFirstPower

end

end OAI
