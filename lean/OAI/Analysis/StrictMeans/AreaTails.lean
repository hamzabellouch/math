import OAI.Analysis.StrictMeans.ImageBounds

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
namespace StrictInverseFirstPower
noncomputable section

def affineInversePlane (z : ℂ) : ℂ := (-(z.re : ℂ) + I) / (z.im : ℂ)

lemma affineInversePlane_re (z : ℂ) : (affineInversePlane z).re = -z.re / z.im := by
  simp [affineInversePlane, Complex.div_ofReal_re]
lemma affineInversePlane_im (z : ℂ) : (affineInversePlane z).im = 1 / z.im := by
  simp [affineInversePlane, Complex.div_ofReal_im]

lemma coe_affineInverse (z : UpperHalfPlane) :
    (affineInverse z : ℂ) = affineInversePlane z := rfl

lemma affineInversePlane_mapsTo :
    MapsTo affineInversePlane {z : ℂ | 0 < z.im} {z : ℂ | 0 < z.im} := by
  intro z hz
  change 0 < (affineInversePlane z).im
  rw [affineInversePlane_im]
  exact one_div_pos.mpr hz

lemma affineInversePlane_involution {z : ℂ} (hz : z.im ≠ 0) :
    affineInversePlane (affineInversePlane z) = z := by
  apply Complex.ext
  · simp only [affineInversePlane_re, affineInversePlane_im]
    field_simp
  · simp [affineInversePlane_im]

lemma affineInversePlane_injOn : InjOn affineInversePlane {z : ℂ | 0 < z.im} := by
  intro z hz w hw he
  have hh := congrArg affineInversePlane he
  rwa [affineInversePlane_involution (ne_of_gt hz),
    affineInversePlane_involution (ne_of_gt hw)] at hh

lemma continuous_affineInverse : Continuous affineInverse := by
  apply UpperHalfPlane.isEmbedding_coe.continuous_iff.mpr
  exact (((Complex.continuous_ofReal.comp UpperHalfPlane.continuous_re).neg.add continuous_const).div
    (Complex.continuous_ofReal.comp UpperHalfPlane.continuous_im) (fun z => Complex.ofReal_ne_zero.mpr z.im_ne_zero))

def outsideCenter : Set ℂ := {z | 0 < z.im ∧ 1 / 2 ≤ ‖cayleyToDisk z‖}

def outsideCenterH : Set UpperHalfPlane := {z | 1 / 2 ≤ ‖cayleyToDisk z‖}

lemma measurableSet_outsideCenter : MeasurableSet outsideCenter := by
  have hc : Measurable (fun z : ℂ => ‖cayleyToDisk z‖) := by
    unfold cayleyToDisk
    fun_prop
  exact (isOpen_halfPlane.measurableSet).inter (measurableSet_le measurable_const hc)

lemma measurableSet_outsideCenterH : MeasurableSet outsideCenterH := by
  have hc : Continuous (fun z : UpperHalfPlane => cayleyToDisk z) :=
    continuous_subtype_val.comp cayleyDiskMap.continuous
  exact measurableSet_le measurable_const hc.norm.measurable

lemma norm_cayley_inverse {z : ℂ} (hz : 0 < z.im) :
    ‖cayleyToDisk (affineInversePlane z)‖ = ‖cayleyToDisk z‖ := by
  have hy : (z.im : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hz.ne'
  have hnum : affineInversePlane z - I = -(z - I) / (z.im : ℂ) := by
    apply Complex.ext <;>
      simp [affineInversePlane_re, affineInversePlane_im, Complex.div_ofReal_re,
        Complex.div_ofReal_im]; field_simp
  have hden : affineInversePlane z + I = -(conj (z + I)) / (z.im : ℂ) := by
    apply Complex.ext <;>
      simp [affineInversePlane_re, affineInversePlane_im, Complex.div_ofReal_re,
        Complex.div_ofReal_im]; field_simp
  simp only [cayleyToDisk, hnum, hden, norm_div, norm_neg, norm_conj]
  exact div_div_div_cancel_right₀ (norm_ne_zero_iff.mpr hy) _ _

lemma affineInversePlane_outside_image : affineInversePlane '' outsideCenter = outsideCenter := by
  apply Subset.antisymm
  · rintro _ ⟨z, hz, rfl⟩
    exact ⟨affineInversePlane_mapsTo hz.1, by simpa only [norm_cayley_inverse hz.1] using hz.2⟩
  · intro z hz
    refine ⟨affineInversePlane z, ⟨affineInversePlane_mapsTo hz.1, ?_⟩,
      affineInversePlane_involution hz.1.ne'⟩
    simpa only [norm_cayley_inverse hz.1] using hz.2

lemma affineInversePlane_hasFDerivAt {z : ℂ} (hz : z.im ≠ 0) :
    HasFDerivAt affineInversePlane
      ((z.im : ℂ)⁻¹ • -(Complex.ofRealCLM.comp Complex.reCLM) -
        ((-(z.re : ℂ) + I) / (z.im : ℂ)^2) •
          (Complex.ofRealCLM.comp Complex.imCLM)) z := by
  have h1 := ((Complex.ofRealCLM.comp Complex.reCLM).hasFDerivAt (x := z)).neg.add_const I
  have h2 := (Complex.ofRealCLM.comp Complex.imCLM).hasFDerivAt (x := z)
  have hinv := ((hasDerivAt_inv (Complex.ofReal_ne_zero.mpr hz)).hasFDerivAt.restrictScalars ℝ).comp z h2
  have hh := h1.mul hinv
  convert hh using 1
  all_goals first | rfl | (ext w; simp [smul_eq_mul, div_eq_mul_inv]; ring)

lemma det_affineInversePlane {z : ℂ} (hz : z.im ≠ 0) :
    (fderiv ℝ affineInversePlane z).det = (z.im ^ 3)⁻¹ := by
  change LinearMap.det (fderiv ℝ affineInversePlane z : ℂ →ₗ[ℝ] ℂ) = _
  rw [(affineInversePlane_hasFDerivAt hz).fderiv, real_det_eq]
  simp only [ContinuousLinearMap.coe_coe, sub_apply,
    smul_apply, neg_apply,
    ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply, Complex.reCLM_apply,
    Complex.imCLM_apply, one_re, one_im, I_re, I_im, Complex.ofReal_one,
    Complex.ofReal_zero, neg_zero, smul_eq_mul, mul_zero, sub_zero, mul_one]
  simp [pow_two, Complex.mul_re, Complex.mul_im, Complex.inv_re, Complex.inv_im,
    Complex.div_re, Complex.div_im, Complex.normSq_apply]
  field_simp [hz]

lemma lintegral_affineInverse_outside (g : ℂ → ℝ≥0∞) :
    (∫⁻ z in outsideCenter, g z) =
      ∫⁻ z in outsideCenter, ENNReal.ofReal ((z.im ^ 3)⁻¹) * g (affineInversePlane z) := by
  have h := lintegral_image_eq_lintegral_abs_det_fderiv_mul volume
    measurableSet_outsideCenter
    (fun z (hz : z ∈ outsideCenter) =>
      (affineInversePlane_hasFDerivAt hz.1.ne').differentiableAt.hasFDerivAt.hasFDerivWithinAt)
    (affineInversePlane_injOn.mono (fun _ hz => hz.1)) g
  rw [affineInversePlane_outside_image] at h
  rw [h]
  apply setLIntegral_congr_fun measurableSet_outsideCenter
  intro z hz
  dsimp only
  rw [det_affineInversePlane hz.1.ne',
    abs_of_pos (inv_pos.mpr (pow_pos hz.1 3))]

end
end StrictInverseFirstPower

open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
namespace StrictInverseFirstPower
noncomputable section

lemma holomorphic_lintegral_image {F : ℂ → ℂ} {s : Set ℂ} (hs : MeasurableSet s)
    (hd : ∀ z ∈ s, DifferentiableAt ℂ F z) (hi : InjOn F s) (g : ℂ → ℝ≥0∞) :
    (∫⁻ w in F '' s, g w) = ∫⁻ z in s, ENNReal.ofReal (‖deriv F z‖ ^ 2) * g (F z) := by
  have hreal (z : ℂ) (hz : z ∈ s) :=
    (hd z hz).hasDerivAt.complexToReal_fderiv.hasFDerivWithinAt (s := s)
  have h := lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hs hreal hi g
  simpa only [det_complexDerivative, abs_sq] using h

lemma integrable_inverse_cube_outside {r : ℝ} (hr : 0 < r) :
    IntegrableOn (fun w : ℂ => ‖w‖⁻¹ ^ 3) {w : ℂ | r ≤ ‖w‖} := by
  have h1 : IntegrableOn (fun y : ℝ => y ^ (-2 : ℝ)) (Ici r) :=
    (integrableOn_Ici_iff_integrableOn_Ioi).mpr
      (integrableOn_Ioi_rpow_of_lt (by norm_num) hr)
  have h2 : Integrable ((Ici r).indicator (fun y : ℝ => y ^ (-2 : ℝ))) :=
    h1.integrable_indicator measurableSet_Ici
  have h3 : IntegrableOn (fun y : ℝ => y ^ (Module.finrank ℝ ℂ - 1) •
      (Ici r).indicator (fun t : ℝ => t⁻¹ ^ 3) y) (Ioi 0) := by
    apply h2.integrableOn.congr_fun _ measurableSet_Ioi
    intro y hy
    by_cases hyr : r ≤ y
    · simp only [indicator_of_mem (show y ∈ Ici r from hyr), Complex.finrank_real_complex, Nat.reduceSub,
        pow_one, smul_eq_mul]
      have he : y ^ (-2 : ℝ) = (y ^ 2)⁻¹ := by
        rw [Real.rpow_neg (le_of_lt hy)]
        congr 1
        exact Real.rpow_two y
      rw [he]
      field_simp
    · simp [hyr, Complex.finrank_real_complex]
  have h4 : Integrable (fun w : ℂ => (Ici r).indicator (fun t : ℝ => t⁻¹ ^ 3) ‖w‖) :=
    (integrable_fun_norm_addHaar volume).mpr h3
  have hset : MeasurableSet {w : ℂ | r ≤ ‖w‖} := measurableSet_le measurable_const (by fun_prop)
  apply (integrable_indicator_iff hset).mp
  convert h4 using 1
  all_goals rfl

lemma inverse_cube_tail_finite {r : ℝ} (hr : 0 < r) :
    (∫⁻ w : ℂ in {w : ℂ | r ≤ ‖w‖}, ENNReal.ofReal (‖w‖⁻¹ ^ 3)) < ∞ := by
  exact (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall (fun _ => by positivity))).mp
    (integrable_inverse_cube_outside hr).hasFiniteIntegral

lemma halfPlane_area_tail_uniform (f : DiskFamily) :
    (∫⁻ z in outsideCenter, ENNReal.ofReal (‖deriv (halfPlaneFunction f) z‖ ^ 2) *
      ENNReal.ofReal (‖halfPlaneFunction f z‖⁻¹ ^ 3)) ≤
    ∫⁻ w : ℂ in {w : ℂ | 1 / 4 ≤ ‖w‖}, ENNReal.ofReal (‖w‖⁻¹ ^ 3) := by
  rw [← holomorphic_lintegral_image measurableSet_outsideCenter
    (fun z hz => (halfPlaneFunction_differentiableOn f).differentiableAt
      (isOpen_halfPlane.mem_nhds hz.1))
    ((halfPlaneFunction_injOn f).mono (fun _ hz => hz.1))
    (fun w => ENNReal.ofReal (‖w‖⁻¹ ^ 3))]
  apply lintegral_mono_set
  rintro _ ⟨z, hz, rfl⟩
  exact halfPlaneFunction_outside_norm_lower f hz.1 hz.2

end
end StrictInverseFirstPower

open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
namespace StrictInverseFirstPower
noncomputable section

def halfPlaneProjection : ℂ → UpperHalfPlane :=
  UpperHalfPlane.measurableEmbedding_coe.invFun

lemma measurable_halfPlaneProjection : Measurable halfPlaneProjection :=
  UpperHalfPlane.measurableEmbedding_coe.measurable_invFun

@[simp] lemma halfPlaneProjection_coe (z : UpperHalfPlane) : halfPlaneProjection z = z :=
  UpperHalfPlane.measurableEmbedding_coe.leftInverse_invFun z

lemma halfPlaneProjection_of_pos {z : ℂ} (hz : 0 < z.im) :
    halfPlaneProjection z = ⟨z, hz⟩ := halfPlaneProjection_coe ⟨z, hz⟩

lemma halfPlaneFunction_inverse_rebase (f : DiskFamily) (z : UpperHalfPlane) :
    halfPlaneFunction (rebase f z) (affineInverse z) =
      -halfPlaneFunction f z / ((z.im : ℂ) * deriv (halfPlaneFunction f) z) := by
  rw [halfPlaneFunction_rebase f z (affineInverse z).im_pos, affineAt_inverse,
    halfPlaneFunction_I, zero_sub]

def inverseCubeValue (f : DiskFamily) (z : UpperHalfPlane) : ℝ≥0∞ :=
  ENNReal.ofReal (‖halfPlaneFunction f z‖⁻¹ ^ 3)

def conformalAreaCube (f : DiskFamily) (z : UpperHalfPlane) : ℝ≥0∞ :=
  ENNReal.ofReal (‖deriv (halfPlaneFunction f) z‖ ^ 2) * inverseCubeValue f z

lemma measurable_inverseCubeValue : Measurable (fun p : DiskFamily × UpperHalfPlane =>
    inverseCubeValue p.1 p.2) := by
  exact ENNReal.measurable_ofReal.comp (continuous_halfPlaneFunction.measurable.norm.inv.pow_const 3)

lemma measurable_conformalAreaCube : Measurable (fun p : DiskFamily × UpperHalfPlane =>
    conformalAreaCube p.1 p.2) := by
  exact (ENNReal.measurable_ofReal.comp (continuous_halfPlaneFunction_deriv.measurable.norm.pow_const 2)).mul
    measurable_inverseCubeValue

lemma weighted_inverse_cube_rebase (f : DiskFamily) (z : UpperHalfPlane) :
    (‖halfPlaneQ f z‖₊ : ℝ≥0∞) * inverseCubeValue (rebase f z) (affineInverse z) =
      ENNReal.ofReal (z.im ^ 3) * conformalAreaCube f z := by
  have hd : ‖deriv (halfPlaneFunction f) z‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (halfPlaneFunction_deriv_ne_zero f z.im_pos)
  rw [inverseCubeValue, halfPlaneFunction_inverse_rebase]
  simp only [norm_div, norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos z.im_pos]
  rw [show (‖halfPlaneQ f z‖₊ : ℝ≥0∞) = ENNReal.ofReal (‖deriv (halfPlaneFunction f) z‖⁻¹) by
    rw [← ENNReal.ofReal_coe_nnreal]
    simp only [coe_nnnorm, halfPlaneQ, norm_inv]]
  unfold conformalAreaCube inverseCubeValue
  rw [← ENNReal.ofReal_mul (inv_nonneg.mpr (norm_nonneg _)),
    ← ENNReal.ofReal_mul (sq_nonneg _), ← ENNReal.ofReal_mul (pow_nonneg z.im_pos.le 3)]
  congr 1
  rw [inv_div, div_pow]
  field_simp

lemma area_cube_expectation (μ : ProbabilityMeasure DiskFamily) (β : ℝ)
    (hlaw : ∀ (z : UpperHalfPlane) (φ : DiskFamily → ℝ≥0∞), Measurable φ →
      (∫⁻ f, (‖halfPlaneQ f z‖₊ : ℝ≥0∞) * φ (rebase f z) ∂(μ : Measure DiskFamily)) =
        ENNReal.ofReal (z.im ^ (-β)) * ∫⁻ f, φ f ∂(μ : Measure DiskFamily))
    (z : UpperHalfPlane) :
    (∫⁻ f, conformalAreaCube f z ∂(μ : Measure DiskFamily)) =
      ENNReal.ofReal ((z.im ^ 3)⁻¹) *
        (ENNReal.ofReal (z.im ^ (-β)) * ∫⁻ f, inverseCubeValue f (affineInverse z) ∂(μ : Measure DiskFamily)) := by
  have he := hlaw z (fun f => inverseCubeValue f (affineInverse z))
    (measurable_inverseCubeValue.comp (f := fun f : DiskFamily => (f, affineInverse z)) measurable_prodMk_right)
  simp only [weighted_inverse_cube_rebase] at he
  have hm : Measurable (fun f : DiskFamily => conformalAreaCube f z) :=
    measurable_conformalAreaCube.comp (f := fun f : DiskFamily => (f, z)) measurable_prodMk_right
  rw [lintegral_const_mul (ENNReal.ofReal (z.im ^ 3)) hm] at he
  rw [← he, ENNReal.ofReal_inv_of_pos (pow_pos z.im_pos 3)]
  exact (ENNReal.inv_mul_cancel_left (by positivity) ENNReal.ofReal_ne_top).symm

def weightedAreaTail (β : ℝ) (f : DiskFamily) : ℝ≥0∞ :=
  ∫⁻ z in outsideCenter, ENNReal.ofReal (z.im ^ β) * inverseCubeValue f (halfPlaneProjection z)

lemma measurable_inverseCube_plane : Measurable (fun p : DiskFamily × ℂ =>
    inverseCubeValue p.1 (halfPlaneProjection p.2)) :=
  measurable_inverseCubeValue.comp (f := fun p : DiskFamily × ℂ => (p.1, halfPlaneProjection p.2))
    ((measurable_fst : Measurable (fun p : DiskFamily × ℂ => p.1)).prodMk
      (measurable_halfPlaneProjection.comp measurable_snd))

lemma measurable_conformalArea_plane : Measurable (fun p : DiskFamily × ℂ =>
    conformalAreaCube p.1 (halfPlaneProjection p.2)) :=
  measurable_conformalAreaCube.comp (f := fun p : DiskFamily × ℂ => (p.1, halfPlaneProjection p.2))
    ((measurable_fst : Measurable (fun p : DiskFamily × ℂ => p.1)).prodMk
      (measurable_halfPlaneProjection.comp measurable_snd))

lemma measurable_areaTail_density (β : ℝ) : Measurable (fun p : DiskFamily × ℂ =>
    ENNReal.ofReal (p.2.im ^ β) * inverseCubeValue p.1 (halfPlaneProjection p.2)) :=
  (ENNReal.measurable_ofReal.comp
    ((Complex.measurable_im.comp (measurable_snd : Measurable (fun p : DiskFamily × ℂ => p.2))).pow_const β)).mul
    measurable_inverseCube_plane

lemma measurable_weightedAreaTail (β : ℝ) : Measurable (weightedAreaTail β) :=
  (measurable_areaTail_density β).lintegral_prod_right' (ν := volume.restrict outsideCenter)

lemma expected_area_tail (μ : ProbabilityMeasure DiskFamily) (β : ℝ)
    (hlaw : ∀ (z : UpperHalfPlane) (φ : DiskFamily → ℝ≥0∞), Measurable φ →
      (∫⁻ f, (‖halfPlaneQ f z‖₊ : ℝ≥0∞) * φ (rebase f z) ∂(μ : Measure DiskFamily)) =
        ENNReal.ofReal (z.im ^ (-β)) * ∫⁻ f, φ f ∂(μ : Measure DiskFamily)) :
    (∫⁻ f, weightedAreaTail β f ∂(μ : Measure DiskFamily)) =
      ∫⁻ f, (∫⁻ z in outsideCenter, conformalAreaCube f (halfPlaneProjection z)) ∂(μ : Measure DiskFamily) := by
  have hm := measurable_areaTail_density β
  have ha := measurable_conformalArea_plane
  change (∫⁻ f, (∫⁻ z in outsideCenter, ENNReal.ofReal (z.im ^ β) * inverseCubeValue f (halfPlaneProjection z)) ∂(μ : Measure DiskFamily)) = _
  conv_lhs => rw [lintegral_lintegral_swap hm.aemeasurable]
  conv_rhs => rw [lintegral_lintegral_swap ha.aemeasurable]
  have hfun (z : ℂ) :
      (∫⁻ f, ENNReal.ofReal (z.im ^ β) * inverseCubeValue f (halfPlaneProjection z) ∂(μ : Measure DiskFamily)) =
      ENNReal.ofReal (z.im ^ β) * ∫⁻ f, inverseCubeValue f (halfPlaneProjection z) ∂(μ : Measure DiskFamily) :=
    lintegral_const_mul _ (measurable_inverseCubeValue.comp (f := fun f : DiskFamily => (f, halfPlaneProjection z)) measurable_prodMk_right)
  simp only [hfun]
  rw [lintegral_affineInverse_outside]
  apply setLIntegral_congr_fun measurableSet_outsideCenter
  intro z hz
  have hpos := affineInversePlane_mapsTo hz.1
  dsimp only
  rw [halfPlaneProjection_of_pos hz.1,
    halfPlaneProjection_of_pos hpos, affineInversePlane_im]
  change ENNReal.ofReal ((z.im ^ 3)⁻¹) *
    (ENNReal.ofReal ((1 / z.im) ^ β) * ∫⁻ f, inverseCubeValue f (affineInverse ⟨z, hz.1⟩) ∂(μ : Measure DiskFamily)) = _
  rw [one_div, Real.inv_rpow hz.1.le, ← Real.rpow_neg hz.1.le]
  exact (area_cube_expectation μ β hlaw ⟨z, hz.1⟩).symm

 theorem weightedAreaTail_ae_finite (μ : ProbabilityMeasure DiskFamily) (β : ℝ)
    (hlaw : ∀ (z : UpperHalfPlane) (φ : DiskFamily → ℝ≥0∞), Measurable φ →
      (∫⁻ f, (‖halfPlaneQ f z‖₊ : ℝ≥0∞) * φ (rebase f z) ∂(μ : Measure DiskFamily)) =
        ENNReal.ofReal (z.im ^ (-β)) * ∫⁻ f, φ f ∂(μ : Measure DiskFamily)) :
    ∀ᵐ f ∂(μ : Measure DiskFamily), weightedAreaTail β f < ∞ := by
  have hb (f : DiskFamily) : (∫⁻ z in outsideCenter, conformalAreaCube f (halfPlaneProjection z)) ≤
      ∫⁻ w : ℂ in {w : ℂ | 1 / 4 ≤ ‖w‖}, ENNReal.ofReal (‖w‖⁻¹ ^ 3) := by
    convert halfPlane_area_tail_uniform f using 1
    apply setLIntegral_congr_fun measurableSet_outsideCenter
    intro z hz
    dsimp only
    rw [halfPlaneProjection_of_pos hz.1]
    rfl
  apply ae_lt_top (measurable_weightedAreaTail β)
  apply ne_of_lt
  rw [expected_area_tail μ β hlaw]
  refine lt_of_le_of_lt (lintegral_mono (μ := (μ : Measure DiskFamily)) hb) ?_
  simpa only [lintegral_const, measure_univ, mul_one] using
    inverse_cube_tail_finite (show (0 : ℝ) < 1 / 4 by norm_num)

end
end StrictInverseFirstPower

end

end OAI
