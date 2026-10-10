import OAI.Analysis.StrictMeans.GreenIdentity

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
namespace StrictInverseFirstPower
noncomputable section

def horizontalCutoff (f : DiskFamily) (ψ : ℂ → ℝ) (s : ℝ) (z : ℂ) : ℝ :=
  Real.smoothTransition (4 * z.im / s - 2) * ψ (halfPlaneFunction f z)

lemma horizontalCutoff_zero (f : DiskFamily) (ψ : ℂ → ℝ) {s : ℝ} (hs : 0 < s)
    {z : ℂ} (hz : z.im ≤ s / 2) : horizontalCutoff f ψ s z = 0 := by
  have h : 4 * z.im / s - 2 ≤ 0 := by
    have hd : 4 * z.im / s ≤ 2 := (div_le_iff₀ hs).mpr (by linarith)
    linarith
  simp only [horizontalCutoff, Real.smoothTransition.zero_of_nonpos h, zero_mul]

lemma horizontalCutoff_one (f : DiskFamily) (ψ : ℂ → ℝ) {s : ℝ} (hs : 0 < s)
    {z : ℂ} (hz : 3 * s / 4 ≤ z.im) : horizontalCutoff f ψ s z = ψ (halfPlaneFunction f z) := by
  have h : 1 ≤ 4 * z.im / s - 2 := by
    have hd : 3 ≤ 4 * z.im / s := (le_div_iff₀ hs).mpr (by linarith)
    linarith
  simp only [horizontalCutoff, Real.smoothTransition.one_of_one_le h, one_mul]

lemma horizontalCutoff_eq_nhds (f : DiskFamily) (ψ : ℂ → ℝ) {s : ℝ} (hs : 0 < s)
    {z : ℂ} (hz : s ≤ z.im) :
    horizontalCutoff f ψ s =ᶠ[𝓝 z] fun w => ψ (halfPlaneFunction f w) := by
  have hlt : 3 * s / 4 < z.im := by linarith
  filter_upwards [Complex.continuous_im.continuousAt.eventually (lt_mem_nhds hlt)] with w hw
  exact horizontalCutoff_one f ψ hs hw.le

lemma horizontalCutoff_contDiff (f : DiskFamily) {ψ : ℂ → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    {s : ℝ} (hs : 0 < s) : ContDiff ℝ ∞ (horizontalCutoff f ψ s) := by
  apply contDiff_iff_contDiffAt.mpr
  intro z
  by_cases hz : 0 < z.im
  · have hF : AnalyticAt ℂ (halfPlaneFunction f) z :=
      (halfPlaneFunction_differentiableOn f).analyticAt (isOpen_halfPlane.mem_nhds hz)
    have hf : ContDiffAt ℝ ∞ (halfPlaneFunction f) z := hF.contDiffAt.restrict_scalars ℝ
    exact (Real.smoothTransition.contDiffAt.comp z
      (((contDiffAt_const.mul Complex.imCLM.contDiff.contDiffAt).div_const s).sub contDiffAt_const)).mul
      (hψ.contDiffAt.comp z hf)
  · have hlt : z.im < s / 2 := (le_of_not_gt hz).trans_lt (half_pos hs)
    have he : horizontalCutoff f ψ s =ᶠ[𝓝 z] fun _ => 0 := by
      filter_upwards [Complex.continuous_im.continuousAt.eventually (gt_mem_nhds hlt)] with w hw
      exact horizontalCutoff_zero f ψ hs hw.le
    exact contDiffAt_const.congr_of_eventuallyEq he

lemma horizontalCutoff_compact (f : DiskFamily) (β : ℝ) (hβ : 0 ≤ β)
    (hfin : weightedAreaTail β f < ⊤) {ψ : ℂ → ℝ} (hc : HasCompactSupport ψ)
    {s : ℝ} (hs : 0 < s) : HasCompactSupport (horizontalCutoff f ψ s) := by
  apply HasCompactSupport.of_support_subset_isCompact
    (compact_strip_preimage_plane f β hβ hfin (half_pos hs) hc)
  intro z hz
  have hn : horizontalCutoff f ψ s z ≠ 0 := hz
  refine ⟨?_, ?_⟩
  · by_contra h
    exact hn (horizontalCutoff_zero f ψ hs (le_of_not_ge h))
  · apply subset_tsupport ψ
    exact (mul_ne_zero_iff.mp hn).2

end
end StrictInverseFirstPower

open Set Filter Metric Complex MeasureTheory
open scoped Topology ContDiff
namespace StrictInverseFirstPower
noncomputable section

lemma planeLaplacian_continuous {ψ : ℂ → ℝ} (hψ : ContDiff ℝ ∞ ψ) :
    Continuous (planeLaplacian ψ) :=
  ((planePartial_contDiff (planePartial_contDiff hψ 1) 1).continuous).add
    ((planePartial_contDiff (planePartial_contDiff hψ I) I).continuous)

lemma planeLaplacian_compact {ψ : ℂ → ℝ} (hc : HasCompactSupport ψ) :
    HasCompactSupport (planeLaplacian ψ) :=
  ((hc.fderiv_apply ℝ 1).fderiv_apply ℝ 1).add
    ((hc.fderiv_apply ℝ I).fderiv_apply ℝ I)

lemma holomorphic_integrable_image {F : ℂ → ℂ} {s : Set ℂ} (hs : MeasurableSet s)
    (hd : ∀ z ∈ s, DifferentiableAt ℂ F z) (hi : InjOn F s) (g : ℂ → ℝ) :
    IntegrableOn g (F '' s) ↔ IntegrableOn (fun z => ‖deriv F z‖ ^ 2 * g (F z)) s := by
  have hreal (z : ℂ) (hz : z ∈ s) :=
    (hd z hz).hasDerivAt.complexToReal_fderiv.hasFDerivWithinAt (s := s)
  simpa only [det_complexDerivative, abs_sq, smul_eq_mul] using
    integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume hs hreal hi g

lemma horizontal_smooth_green (f : DiskFamily) (β : ℝ) (hβ : 0 ≤ β)
    (hfin : weightedAreaTail β f < ⊤) {ψ : ℂ → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hc : HasCompactSupport ψ) {s : ℝ} (hs : 0 < s) :
    (∫ x : ℝ, ψ (halfPlaneFunction f ((x : ℂ) + (s : ℂ) * I))) =
      ∫ z in {z : ℂ | s < z.im},
        (z.im-s) * (‖deriv (halfPlaneFunction f) z‖ ^ 2 * planeLaplacian ψ (halfPlaneFunction f z)) := by
  have hg := horizontalCutoff_contDiff f hψ hs
  have hgc := horizontalCutoff_compact f β hβ hfin hc hs
  have he := compact_complex_horizontal_green hg hgc s
  have hline (x : ℝ) : horizontalCutoff f ψ s ((x : ℂ) + (s : ℂ) * I) =
      ψ (halfPlaneFunction f ((x : ℂ) + (s : ℂ) * I)) :=
    horizontalCutoff_one f ψ hs (by simp; linarith)
  simp only [hline] at he
  rw [he]
  apply setIntegral_congr_fun (isOpen_lt continuous_const Complex.continuous_im).measurableSet
  intro z hz
  dsimp only
  rw [planeLaplacian_congr_nhds (horizontalCutoff_eq_nhds f ψ hs hz.le),
    planeLaplacian_comp_holomorphic
      ((halfPlaneFunction_differentiableOn f).analyticAt (isOpen_halfPlane.mem_nhds (hs.trans hz)))
      ((contDiff_infty.mp hψ 2).contDiffAt)]

lemma pullback_laplacian_integrable (f : DiskFamily) {ψ : ℂ → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ) :
    IntegrableOn (fun z => ‖deriv (halfPlaneFunction f) z‖ ^ 2 *
      |planeLaplacian ψ (halfPlaneFunction f z)|) {z : ℂ | 0 < z.im} := by
  apply (holomorphic_integrable_image isOpen_halfPlane.measurableSet
    (fun z hz => (halfPlaneFunction_differentiableOn f).differentiableAt (isOpen_halfPlane.mem_nhds hz))
    (halfPlaneFunction_injOn f) (fun w => |planeLaplacian ψ w|)).mp
  exact ((planeLaplacian_continuous hψ).abs.integrable_of_hasCompactSupport
    (planeLaplacian_compact hc).abs).integrableOn

lemma pullback_laplacian_integral_le (f : DiskFamily) {ψ : ℂ → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ) :
    (∫ z in {z : ℂ | 0 < z.im}, ‖deriv (halfPlaneFunction f) z‖ ^ 2 *
      |planeLaplacian ψ (halfPlaneFunction f z)|) ≤ ∫ w : ℂ, |planeLaplacian ψ w| := by
  rw [← holomorphic_integral_image isOpen_halfPlane.measurableSet
    (fun z hz => (halfPlaneFunction_differentiableOn f).differentiableAt (isOpen_halfPlane.mem_nhds hz))
    (halfPlaneFunction_injOn f) (fun w => |planeLaplacian ψ w|)]
  exact setIntegral_le_integral
    ((planeLaplacian_continuous hψ).abs.integrable_of_hasCompactSupport
      (planeLaplacian_compact hc).abs)
    (ae_of_all _ (fun w => abs_nonneg _))

lemma horizontal_smooth_bound (f : DiskFamily) (β : ℝ) (hβ : 0 ≤ β)
    (hfin : weightedAreaTail β f < ⊤) {ψ : ℂ → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hc : HasCompactSupport ψ) :
    ∃ C : ℝ, ∀ s : ℝ, 0 < s →
      (∫ x : ℝ, ψ (halfPlaneFunction f ((x : ℂ) + (s : ℂ) * I))) ≤ C := by
  obtain ⟨R, hR⟩ := (planeLaplacian_compact hc).isBounded.subset_closedBall (0 : ℂ)
  obtain ⟨Y, hY, hheight⟩ := bounded_preimage_height f β hβ hfin R
  refine ⟨Y * ∫ w : ℂ, |planeLaplacian ψ w|, fun s hs => ?_⟩
  let A : ℂ → ℝ := fun z => ‖deriv (halfPlaneFunction f) z‖ ^ 2 *
    |planeLaplacian ψ (halfPlaneFunction f z)|
  have hiA : IntegrableOn A {z : ℂ | 0 < z.im} := pullback_laplacian_integrable f hψ hc
  have hiAs : IntegrableOn A {z : ℂ | s < z.im} := hiA.mono_set (fun z hz => hs.trans hz)
  have hA (z : ℂ) : 0 ≤ A z := mul_nonneg (sq_nonneg _) (abs_nonneg _)
  have hpoint (z : ℂ) (hz : s < z.im) :
      |(z.im-s) * (‖deriv (halfPlaneFunction f) z‖ ^ 2 * planeLaplacian ψ (halfPlaneFunction f z))| ≤ Y * A z := by
    rw [abs_mul, abs_mul, abs_of_pos (sub_pos.mpr hz), abs_sq]
    change (z.im-s) * A z ≤ Y * A z
    by_cases hd : planeLaplacian ψ (halfPlaneFunction f z) = 0
    · simp [A, hd]
    · apply mul_le_mul_of_nonneg_right _ (hA z)
      have hmem := hR (subset_tsupport (planeLaplacian ψ) hd)
      have hn : ‖halfPlaneFunction f z‖ ≤ R := by simpa using hmem
      have hy := hheight ⟨z, hs.trans hz⟩ hn
      change z.im ≤ Y at hy
      linarith
  rw [horizontal_smooth_green f β hβ hfin hψ hc hs]
  calc
    _ ≤ |∫ z in {z : ℂ | s < z.im}, (z.im-s) *
        (‖deriv (halfPlaneFunction f) z‖ ^ 2 * planeLaplacian ψ (halfPlaneFunction f z))| := le_abs_self _
    _ ≤ ∫ z in {z : ℂ | s < z.im}, |(z.im-s) *
        (‖deriv (halfPlaneFunction f) z‖ ^ 2 * planeLaplacian ψ (halfPlaneFunction f z))| :=
      by
        simpa only [Real.norm_eq_abs] using (norm_integral_le_integral_norm
          (μ := volume.restrict {z : ℂ | s < z.im})
          (fun z : ℂ => (z.im-s) * (‖deriv (halfPlaneFunction f) z‖ ^ 2 * planeLaplacian ψ (halfPlaneFunction f z))))
    _ ≤ ∫ z in {z : ℂ | s < z.im}, Y * A z := by
      apply integral_mono_of_nonneg (ae_of_all _ (fun _ => abs_nonneg _)) (hiAs.const_mul Y)
      exact (ae_restrict_mem (isOpen_lt continuous_const Complex.continuous_im).measurableSet).mono hpoint
    _ = Y * ∫ z in {z : ℂ | s < z.im}, A z := integral_const_mul _ _
    _ ≤ Y * ∫ z in {z : ℂ | 0 < z.im}, A z := by
      apply mul_le_mul_of_nonneg_left _ hY.le
      exact setIntegral_mono_set hiA (ae_of_all _ hA) (ae_of_all _ (fun z hz => hs.trans hz))
    _ ≤ _ := mul_le_mul_of_nonneg_left (pullback_laplacian_integral_le f hψ hc) hY.le

lemma horizontal_smooth_integrable (f : DiskFamily) (β : ℝ) (hβ : 0 ≤ β)
    (hfin : weightedAreaTail β f < ⊤) {ψ : ℂ → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hc : HasCompactSupport ψ) {s : ℝ} (hs : 0 < s) :
    Integrable (fun x : ℝ => ψ (halfPlaneFunction f ((x : ℂ) + (s : ℂ) * I))) := by
  let g := horizontalCutoff f ψ s
  have hg : ContDiff ℝ ∞ g := horizontalCutoff_contDiff f hψ hs
  have hgc : HasCompactSupport g := horizontalCutoff_compact f β hβ hfin hc hs
  have hcP : HasCompactSupport (fun p => g (Complex.equivRealProdCLM.symm p)) :=
    hgc.comp_isClosedEmbedding Complex.equivRealProdCLM.symm.toHomeomorph.isClosedEmbedding
  have hL : Continuous (fun x : ℝ => g (Complex.equivRealProdCLM.symm (x,s))) :=
    (hg.continuous.comp Complex.equivRealProdCLM.symm.continuous).comp
      (continuous_id.prodMk continuous_const)
  have hi : Integrable (fun x : ℝ => g (Complex.equivRealProdCLM.symm (x,s))) :=
    hL.integrable_of_hasCompactSupport (compact_horizontal_line hcP s)
  have he (x : ℝ) : g (Complex.equivRealProdCLM.symm (x,s)) =
      ψ (halfPlaneFunction f ((x : ℂ) + (s : ℂ) * I)) := by
    have hz : Complex.equivRealProdCLM.symm (x,s) = (x : ℂ) + (s : ℂ) * I := by
      apply Complex.ext <;> simp
    rw [hz]
    exact horizontalCutoff_one f ψ hs (by simp; linarith)
  simpa only [he] using hi

lemma continuous_halfPlaneFunction_line (f : DiskFamily) {s : ℝ} (hs : 0 < s) :
    Continuous (fun x : ℝ => halfPlaneFunction f ((x : ℂ) + (s : ℂ) * I)) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  have hz : 0 < ((x : ℂ) + (s : ℂ) * I).im := by simpa using hs
  have hC : ContinuousAt (fun x : ℝ => (x : ℂ) + (s : ℂ) * I) x :=
    Complex.continuous_ofReal.continuousAt.add continuousAt_const
  exact ContinuousAt.comp (f := fun x : ℝ => (x : ℂ) + (s : ℂ) * I)
    ((halfPlaneFunction_differentiableOn f).differentiableAt
      (isOpen_halfPlane.mem_nhds hz)).continuousAt hC

lemma compact_smooth_majorant {K : Set ℂ} (hK : IsCompact K) :
    ∃ ψ : ℂ → ℝ, ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧
      (∀ z, 0 ≤ ψ z) ∧ ∀ z ∈ K, 1 ≤ ψ z := by
  obtain ⟨R, hRpos, hR⟩ := hK.isBounded.subset_ball_lt 0 (0 : ℂ)
  let b : ContDiffBump (0 : ℂ) :=
    { rIn := R
      rOut := R + 1
      rIn_pos := hRpos
      rIn_lt_rOut := by linarith }
  refine ⟨b, b.contDiff, b.hasCompactSupport, fun _ => b.nonneg, ?_⟩
  intro z hz
  have he : b z = 1 := b.one_of_mem_closedBall (ball_subset_closedBall (hR hz))
  exact he.ge

theorem horizontal_length_bound (f : DiskFamily) (β : ℝ) (hβ : 0 ≤ β)
    (hfin : weightedAreaTail β f < ⊤) {K : Set ℂ} (hK : IsCompact K) :
    ∃ C : ℝ, ∀ s : ℝ, 0 < s →
      volume {x : ℝ | halfPlaneFunction f ((x : ℂ) + (s : ℂ) * I) ∈ K} ≤ ENNReal.ofReal C := by
  obtain ⟨ψ, hψ, hc, hnonneg, hmajor⟩ := compact_smooth_majorant hK
  obtain ⟨C, hC⟩ := horizontal_smooth_bound f β hβ hfin hψ hc
  refine ⟨C, fun s hs => ?_⟩
  let A : Set ℝ := {x | halfPlaneFunction f ((x : ℂ) + (s : ℂ) * I) ∈ K}
  have hA : MeasurableSet A := hK.isClosed.measurableSet.preimage
    (continuous_halfPlaneFunction_line f hs).measurable
  rw [← lintegral_indicator_one hA]
  calc
    _ ≤ ∫⁻ x : ℝ, ENNReal.ofReal (ψ (halfPlaneFunction f ((x : ℂ) + (s : ℂ) * I))) := by
      apply lintegral_mono
      intro x
      by_cases hx : x ∈ A
      · simp only [indicator_of_mem hx, Pi.one_apply]
        exact_mod_cast (ENNReal.ofReal_le_ofReal (hmajor _ hx))
      · simp only [indicator_of_notMem hx]
        exact bot_le
    _ = ENNReal.ofReal (∫ x : ℝ, ψ (halfPlaneFunction f ((x : ℂ) + (s : ℂ) * I))) :=
      (ofReal_integral_eq_lintegral_ofReal
        (horizontal_smooth_integrable f β hβ hfin hψ hc hs)
        (ae_of_all _ (fun x => hnonneg _))).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal (hC s hs)

end
end StrictInverseFirstPower

end

end OAI
