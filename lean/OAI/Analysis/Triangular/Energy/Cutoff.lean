import OAI.Analysis.Triangular.Energy.Spectral

namespace OAI

noncomputable section
open scoped BigOperators Topology ENNReal NNReal RealInnerProductSpace FourierTransform
open Classical Filter MeasureTheory Complex ComplexConjugate FourierTransform
namespace TriangularUniversal
/-- A comparison density, equal to one on the competitor disk. It adds no
spacing or local-count hypothesis to the density-only LP argument. -/
def radialCutoff (R T : ℝ) (x : Plane) : ℝ :=
  max 0 (min 1 ((R + T - ‖x‖) / T))

lemma radialCutoff_nonneg (R T : ℝ) (x : Plane) : 0 ≤ radialCutoff R T x := le_max_left _ _
lemma radialCutoff_le_one (R T : ℝ) (x : Plane) : radialCutoff R T x ≤ 1 :=
  max_le zero_le_one (min_le_left _ _)
lemma radialCutoff_continuous (R T : ℝ) : Continuous (radialCutoff R T) := by
  unfold radialCutoff
  fun_prop
lemma radialCutoff_eq_one {R T : ℝ} (hT : 0 < T) {x : Plane} (hx : ‖x‖ ≤ R) :
    radialCutoff R T x = 1 := by
  have h : 1 ≤ (R+T-‖x‖)/T := (le_div_iff₀ hT).mpr (by linarith)
  simp [radialCutoff, min_eq_left h]
lemma radialCutoff_eq_zero {R T : ℝ} (hT : 0 < T) {x : Plane} (hx : R+T ≤ ‖x‖) :
    radialCutoff R T x = 0 := by
  have h : (R+T-‖x‖)/T ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hT.le
  exact max_eq_left ((min_le_right _ _).trans h)

lemma radialCutoff_compactSupport {R T : ℝ} (hT : 0 < T) :
    HasCompactSupport (radialCutoff R T) := by
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : Plane) (R+T))
  intro x hx
  simp only [Metric.mem_closedBall, dist_zero_right]
  by_contra h
  exact hx (radialCutoff_eq_zero hT (le_of_not_ge h))

lemma radialCutoff_integrable {R T : ℝ} (hT : 0 < T) : Integrable (radialCutoff R T) :=
  (radialCutoff_continuous R T).integrable_of_hasCompactSupport (radialCutoff_compactSupport hT)

lemma clip_lipschitz : LipschitzWith 1 (fun x : ℝ => max 0 (min 1 x)) := by
  simpa using (LipschitzWith.const (0 : ℝ)).max
    ((LipschitzWith.const (1 : ℝ)).min LipschitzWith.id)

lemma radialCutoff_lipschitz {R T : ℝ} (hT : 0 < T) :
    LipschitzWith (T⁻¹).toNNReal (radialCutoff R T) := by
  have h : LipschitzWith (T⁻¹).toNNReal (fun x : Plane => (R+T-‖x‖)/T) := by
    apply LipschitzWith.of_dist_le'
    intro x y
    rw [Real.dist_eq, dist_eq_norm]
    calc
      |(R+T-‖x‖)/T - (R+T-‖y‖)/T| = |‖y‖-‖x‖|/T := by
        rw [← sub_div, abs_div, abs_of_pos hT]
        congr 2
        ring
      _ ≤ ‖x-y‖/T := by
        apply div_le_div_of_nonneg_right _ hT.le
        simpa [norm_sub_rev] using abs_norm_sub_norm_le y x
      _ = T⁻¹ * ‖x-y‖ := by ring
  change LipschitzWith (T⁻¹).toNNReal (fun x : Plane => max 0 (min 1 ((R+T-‖x‖)/T)))
  simpa only [one_mul, Function.comp_def] using clip_lipschitz.comp h

lemma radialCutoff_sub_bound {R T : ℝ} (hT : 0 < T) (x z : Plane) :
    |radialCutoff R T (x-z) - radialCutoff R T x| ≤ ‖z‖/T := by
  have H := (radialCutoff_lipschitz (R := R) hT).norm_sub_le (x-z) x
  simpa [Real.norm_eq_abs, Real.coe_toNNReal _ (inv_nonneg.mpr hT.le),
    sub_sub_cancel_left, div_eq_mul_inv, mul_comm] using H

lemma plane_disk_volume {R : ℝ} (hR : 0 ≤ R) :
    volume.real (Metric.closedBall (0 : Plane) R) = Real.pi * R^2 := by
  rw [measureReal_def, EuclideanSpace.volume_closedBall_fin_two]
  simp [Real.pi_pos.le, hR, mul_comm]

lemma radialCutoff_integral_bound {R T : ℝ} (hR : 0 ≤ R) (hT : 0 < T) :
    (∫ x, radialCutoff R T x) ≤ Real.pi*(R+T)^2 := by
  have hs := measurableSet_closedBall (x := (0 : Plane)) (ε := R+T)
  calc
    _ ≤ ∫ x, (Metric.closedBall (0 : Plane) (R+T)).indicator (fun _ => (1 : ℝ)) x := by
      apply integral_mono (radialCutoff_integrable hT)
        ((integrable_indicator_iff hs).mpr (integrableOn_const (by rw [EuclideanSpace.volume_closedBall_fin_two]; finiteness)))
      intro x
      by_cases hx : x ∈ Metric.closedBall (0 : Plane) (R+T)
      · simpa [hx] using radialCutoff_le_one R T x
      · simp only [Set.indicator_of_notMem hx]
        have hx' : R+T ≤ ‖x‖ := le_of_lt (by
          simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using hx)
        rw [radialCutoff_eq_zero hT hx']
    _ = _ := by rw [integral_indicator_const 1 hs, smul_eq_mul, mul_one, plane_disk_volume (by linarith)]

def cutoffConvolution (f : Plane → ℂ) (R T : ℝ) (x : Plane) : ℂ :=
  ∫ z, radialCutoff R T (x-z) • f z

def firstMoment (f : Plane → ℂ) : ℝ := ∫ z, ‖z‖ * ‖f z‖

lemma cutoffConvolution_integrable {f : Plane → ℂ} (hf : Integrable f)
    (R T : ℝ) (x : Plane) :
    Integrable (fun z => radialCutoff R T (x-z) • f z) := by
  exact hf.bdd_smul 1 ((radialCutoff_continuous R T).comp
    (continuous_const.sub continuous_id)).aestronglyMeasurable
    (Eventually.of_forall fun z => by
      simpa [Real.norm_eq_abs, abs_of_nonneg (radialCutoff_nonneg R T (x-z))]
        using radialCutoff_le_one R T (x-z))

lemma cutoffConvolution_error {f : Plane → ℂ} (hf : Integrable f)
    (hm : Integrable (fun z => ‖z‖ * ‖f z‖))
    {R T : ℝ} (hT : 0 < T) (x : Plane) :
    ‖cutoffConvolution f R T x - radialCutoff R T x • (∫ z, f z)‖ ≤ firstMoment f / T := by
  have hi2 : Integrable (fun z => radialCutoff R T x • f z) := by
    simpa only [Pi.smul_def] using hf.smul (radialCutoff R T x)
  have hi := (cutoffConvolution_integrable hf R T x).sub hi2
  have he : cutoffConvolution f R T x - radialCutoff R T x • (∫ z, f z) =
      ∫ z, (radialCutoff R T (x-z) - radialCutoff R T x) • f z := by
    simp_rw [sub_smul]
    rw [integral_sub (cutoffConvolution_integrable hf R T x)
      hi2, integral_smul]
    rfl
  rw [he]
  calc
    _ ≤ ∫ z, ‖(radialCutoff R T (x-z) - radialCutoff R T x) • f z‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ z, (‖z‖ * ‖f z‖) / T := by
      apply integral_mono
      · simpa only [sub_smul, Pi.sub_apply] using hi.norm
      · exact hm.div_const T
      · intro z
        dsimp only
        rw [norm_smul, Real.norm_eq_abs]
        calc
          _ ≤ (‖z‖ / T) * ‖f z‖ := mul_le_mul_of_nonneg_right
            (radialCutoff_sub_bound hT x z) (norm_nonneg _)
          _ = _ := by ring
    _ = _ := by rw [integral_div]; rfl

lemma cutoffConvolution_re_bounds {f : Plane → ℂ} (hf : Integrable f)
    (hm : Integrable (fun z => ‖z‖ * ‖f z‖))
    {R T : ℝ} (hT : 0 < T) (x : Plane) :
    radialCutoff R T x * (∫ z, f z).re - firstMoment f / T ≤
      (cutoffConvolution f R T x).re ∧
    (cutoffConvolution f R T x).re ≤
      radialCutoff R T x * (∫ z, f z).re + firstMoment f / T := by
  have h := (Complex.abs_re_le_norm _).trans (cutoffConvolution_error hf hm (R := R) hT x)
  rw [Complex.sub_re, Complex.real_smul, Complex.mul_re] at h
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at h
  constructor <;> linarith [abs_le.mp h]



def cutoffMeasure (R T : ℝ) : Measure Plane :=
  volume.withDensity (fun x => ENNReal.ofReal (radialCutoff R T x))

lemma cutoffMeasure_finite {R T : ℝ} (hT : 0 < T) : IsFiniteMeasure (cutoffMeasure R T) := by
  apply isFiniteMeasure_withDensity
  rw [← ofReal_integral_eq_lintegral_ofReal (radialCutoff_integrable hT)
    (Eventually.of_forall (radialCutoff_nonneg R T))]
  exact ENNReal.ofReal_ne_top

lemma integral_cutoffMeasure (R T : ℝ) (f : Plane → ℂ) :
    (∫ x, f x ∂cutoffMeasure R T) = ∫ x, radialCutoff R T x • f x := by
  rw [cutoffMeasure, integral_withDensity_eq_integral_toReal_smul]
  · simp only [ENNReal.toReal_ofReal (radialCutoff_nonneg _ _ _)]
  · exact (radialCutoff_continuous R T).measurable.ennreal_ofReal
  · exact Eventually.of_forall fun _ => ENNReal.ofReal_lt_top

lemma cutoffMeasure_mass {R T : ℝ} (hT : 0 < T) :
    (cutoffMeasure R T).real Set.univ = ∫ x, radialCutoff R T x := by
  rw [measureReal_def, cutoffMeasure, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ, ← ofReal_integral_eq_lintegral_ofReal (radialCutoff_integrable hT)
      (Eventually.of_forall (radialCutoff_nonneg R T)), ENNReal.toReal_ofReal]
  exact integral_nonneg (radialCutoff_nonneg R T)

lemma cutoffConvolution_eq_integral (f : Plane → ℂ) (R T : ℝ) (x : Plane) :
    cutoffConvolution f R T x = ∫ y, f (x-y) ∂cutoffMeasure R T := by
  rw [integral_cutoffMeasure]
  have h := integral_sub_left_eq_self (fun y => radialCutoff R T y • f (x-y)) volume x
  simpa only [sub_sub_cancel, cutoffConvolution] using h
end TriangularUniversal
end

end OAI
