import OAI.Analysis.CircleDomains.Uniformization.ConformalComposition
import OAI.Analysis.CircleDomains.Uniformization.ConformalMetric

namespace OAI

/-!
# Metric conformality in the concrete sphere charts

Metric conformality records the pullback Gram matrix and positive
orientation of the actual real differential. When the source metric is
a positive scalar multiple of the Euclidean metric, these equations
imply the complex Cauchy--Riemann equation and a nonzero derivative.
-/

open Set Filter
open scoped Topology OnePoint Matrix.Norms.Elementwise

noncomputable section

namespace CircleDomainRigidity

open FiniteTransfer

def sphereLocalMap (f : Sphere → Sphere) (p : Sphere) : ℂ → ℂ :=
  fun z => chart (f p) (f (chartSymm p z))

def sphereChartMetric (g : (ℝ × ℝ) → PlanarMetric) (p : Sphere) : PlanarMetric := by
  classical
  exact if p = ∞ then (4 : ℝ) • (1 : PlanarMetric) else g (Complex.equivRealProdCLM (finiteCoord p))

def IsMetricConformalAt (g : (ℝ × ℝ) → PlanarMetric) (f : Sphere → Sphere) (p : Sphere) : Prop :=
  ContinuousAt f p ∧ DifferentiableAt ℝ (sphereLocalMap f p) (chart p p) ∧
    let A := fderiv ℝ (sphereLocalMap f p) (chart p p)
    ∃ scale : ℝ, 0 < scale ∧
      (A 1).re ^ 2 + (A 1).im ^ 2 = scale * sphereChartMetric g p 0 0 ∧
      (A Complex.I).re ^ 2 + (A Complex.I).im ^ 2 = scale * sphereChartMetric g p 1 1 ∧
      (A 1).re * (A Complex.I).re + (A 1).im * (A Complex.I).im = scale * sphereChartMetric g p 0 1 ∧
      0 < (A 1).re * (A Complex.I).im - (A Complex.I).re * (A 1).im

theorem complex_linear_of_positive_orthogonal_columns
    (A : ℂ →L[ℝ] ℂ) {q : ℝ} (hq : 0 < q)
    (hxx : (A 1).re ^ 2 + (A 1).im ^ 2 = q)
    (hyy : (A Complex.I).re ^ 2 + (A Complex.I).im ^ 2 = q)
    (hxy : (A 1).re * (A Complex.I).re + (A 1).im * (A Complex.I).im = 0)
    (hdet : 0 < (A 1).re * (A Complex.I).im - (A Complex.I).re * (A 1).im) :
    A Complex.I = Complex.I • A 1 ∧ A 1 ≠ 0 := by
  let a := (A 1).re
  let b := (A Complex.I).re
  let c := (A 1).im
  let d := (A Complex.I).im
  change a ^ 2 + c ^ 2 = q at hxx
  change b ^ 2 + d ^ 2 = q at hyy
  change a * b + c * d = 0 at hxy
  change 0 < a * d - b * c at hdet
  have hsquare : (a * d - b * c) ^ 2 = q ^ 2 := by
    calc
      _ = (a ^ 2 + c ^ 2) * (b ^ 2 + d ^ 2) - (a * b + c * d) ^ 2 := by ring
      _ = q ^ 2 := by rw [hxx, hyy, hxy]; ring
  have hdetq : a * d - b * c = q := (sq_eq_sq₀ hdet.le hq.le).mp hsquare
  have hsum : (a - d) ^ 2 + (b + c) ^ 2 = 0 := by nlinarith
  have had : a = d := by nlinarith [sq_nonneg (b + c)]
  have hbc : b = -c := by nlinarith [sq_nonneg (a - d)]
  constructor
  · apply Complex.ext
    · change b = (Complex.I * A 1).re
      simpa only [Complex.mul_re, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_sub] using hbc
    · change d = (Complex.I * A 1).im
      simpa only [Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_add] using had.symm
  · intro hzero
    have ha : a = 0 := congrArg Complex.re hzero
    have hc : c = 0 := congrArg Complex.im hzero
    nlinarith

theorem IsMetricConformalAt.isConformalAt
    {g : (ℝ × ℝ) → PlanarMetric} {f : Sphere → Sphere} {p : Sphere}
    (hf : IsMetricConformalAt g f p)
    (hscalar : ∃ c : ℝ, 0 < c ∧ sphereChartMetric g p = c • (1 : PlanarMetric)) :
    IsConformalAt f p := by
  obtain ⟨hc, hd, scale, hscale, hxx, hyy, hxy, hdet⟩ := hf
  obtain ⟨c, hpos, hmetric⟩ := hscalar
  rw [hmetric] at hxx hyy hxy
  norm_num [Matrix.smul_apply, Matrix.one_apply] at hxx hyy hxy
  obtain ⟨hCR, hnonzero⟩ := complex_linear_of_positive_orthogonal_columns
    (fderiv ℝ (sphereLocalMap f p) (chart p p)) (mul_pos hscale hpos) hxx hyy hxy hdet
  refine ⟨hc, fderiv ℝ (sphereLocalMap f p) (chart p p) 1, hnonzero, ?_⟩
  exact complexOfReal_hasDerivAt hd hCR

theorem metric_conformal_on_spherical_background
    {g : (ℝ × ℝ) → PlanarMetric} {f : Sphere → Sphere} {U : Set Sphere}
    (hf : ∀ p ∈ U, IsMetricConformalAt g f p)
    (hbackground : ∀ z : ℂ, (z : Sphere) ∈ U →
      g (Complex.equivRealProdCLM z) = sphericalMetricFactor (Complex.equivRealProdCLM z) • 1) :
    IsConformalOn f U := by
  intro p hp
  apply (hf p hp).isConformalAt
  cases p using OnePoint.rec with
  | infty =>
    refine ⟨4, by norm_num, ?_⟩
    rw [sphereChartMetric, ite_eq_left rfl]
  | coe z =>
    refine ⟨sphericalMetricFactor (Complex.equivRealProdCLM z), sphericalMetricFactor_pos _, ?_⟩
    simpa only [sphereChartMetric, OnePoint.coe_ne_infty, ite_false, finiteCoord, OnePoint.elim_some, id_eq] using hbackground z hp

end CircleDomainRigidity

end

end OAI
