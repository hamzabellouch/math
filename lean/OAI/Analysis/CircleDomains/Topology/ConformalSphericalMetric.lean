import OAI.Analysis.CircleDomains.Sobolev.MetricComposition

namespace OAI

/-! Ordinary conformality supplies the metric-conformality predicate for
the unchanged spherical background, including the infinity chart. -/
open Set Function Filter
open scoped Topology Matrix.Norms.Elementwise
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

 theorem IsConformalAt.isMetricConformalAt_of_scalar
    {f : Sphere → Sphere} {p : Sphere} (hf : IsConformalAt f p)
    {g : (ℝ × ℝ) → PlanarMetric} {c : ℝ} (hc : 0 < c)
    (hg : sphereChartMetric g p = c • (1 : PlanarMetric)) :
    IsMetricConformalAt g f p := by
  obtain ⟨hcont, a, ha, had⟩ := hf
  have hd := had.hasFDerivAt.restrictScalars ℝ
  change HasFDerivAt (sphereLocalMap f p) _ (chart p p) at hd
  have h1 : fderiv ℝ (sphereLocalMap f p) (chart p p) 1 = a := by
    rw [hd.fderiv]
    simp
  have hI : fderiv ℝ (sphereLocalMap f p) (chart p p) Complex.I = Complex.I * a := by
    rw [hd.fderiv]
    simp [smul_eq_mul]
  refine ⟨hcont, hd.differentiableAt, (a.re ^ 2 + a.im ^ 2) / c,
    div_pos (complex_column_norm_pos ha) hc, ?_, ?_, ?_, ?_⟩
  · rw [h1, hg]
    norm_num [Matrix.smul_apply, Matrix.one_apply]
    exact (div_mul_cancel₀ _ hc.ne').symm
  · rw [hI, hg]
    norm_num [Matrix.smul_apply, Matrix.one_apply, Complex.mul_re, Complex.mul_im]
    rw [div_mul_cancel₀ _ hc.ne']
    ring
  · rw [h1, hI, hg]
    norm_num [Matrix.smul_apply, Matrix.one_apply, Complex.mul_re, Complex.mul_im]
    ring
  · rw [h1, hI]
    simpa only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
      zero_mul, one_mul, zero_sub, zero_add, neg_mul, sub_neg_eq_add, ← pow_two] using
      complex_column_norm_pos ha

 theorem IsConformalAt.isMetricConformalAt_spherical
    {f : Sphere → Sphere} {p : Sphere} (hf : IsConformalAt f p) :
    IsMetricConformalAt (fun z => sphericalMetricFactor z • 1) f p := by
  cases p using OnePoint.rec with
  | infty =>
    exact hf.isMetricConformalAt_of_scalar (by norm_num : (0 : ℝ) < 4)
      (by simp [sphereChartMetric])
  | coe z =>
    exact hf.isMetricConformalAt_of_scalar (sphericalMetricFactor_pos (Complex.equivRealProdCLM z))
      (by simp [sphereChartMetric, finiteCoord])

end CircleDomainRigidity

end

end OAI
