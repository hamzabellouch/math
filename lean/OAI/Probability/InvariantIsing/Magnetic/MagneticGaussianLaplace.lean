import OAI.Probability.InvariantIsing.Magnetic.MagneticHeatContinuity
import Mathlib.Probability.Moments.MGFAnalytic

namespace OAI

/-! Positive weighted Gaussian Laplace transforms. This supplies spatial
smoothing of the finite field without assuming additional derivatives of
the terminal observable. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped NNReal Topology

namespace InvariantIsing

def magneticWeightedGaussian (F A : ℝ → ℝ) (ζ : ℝ) (v : ℝ≥0) : Measure ℝ :=
  (gaussianReal 0 v).withDensity (fun y => ENNReal.ofReal (Real.exp (ζ * F y) * A y))

lemma magneticWeightedGaussian_exp_integrable {F A : ℝ → ℝ}
    (hF : Measurable F) (hG : HasLinearGrowth F) (hA : Measurable A)
    {K : ℝ} (bA : ∀ y, |A y| ≤ K) (hA0 : ∀ y, 0 ≤ A y)
    (ζ t : ℝ) (v : ℝ≥0) :
    Integrable (fun y => Real.exp (t * y)) (magneticWeightedGaussian F A ζ v) := by
  have hm : Measurable (fun y => ENNReal.ofReal (Real.exp (ζ * F y) * A y)) :=
    ((hF.const_mul ζ).exp.mul hA).ennreal_ofReal
  unfold magneticWeightedGaussian
  apply (integrable_withDensity_iff_integrable_smul' hm
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)).mpr
  have hg : HasLinearGrowth (fun y => ζ * F y + t * y) := by
    obtain ⟨C, L, hC, hL, hB⟩ := hG
    refine ⟨|ζ| * C, |ζ| * L + |t|, by positivity, by positivity, fun y => ?_⟩
    have hb := hB y
    rw [Real.norm_eq_abs] at hb ⊢
    calc
      |ζ * F y + t * y| ≤ |ζ| * |F y| + |t| * |y| := by
        simpa only [abs_mul] using abs_add_le (ζ * F y) (t * y)
      _ ≤ |ζ| * (C + L * |y|) + |t| * |y| := by gcongr
      _ = _ := by ring
  have hi : Integrable (fun y => Real.exp (ζ * F y + t * y)) (gaussianReal 0 v) := by
    simpa only [one_mul, Pi.add_apply, Pi.mul_apply, id_eq] using integrable_exp_of_linearGrowth _
      (gaussianReal_exponentialNormMoments 0 v)
      ((hF.const_mul ζ).add (measurable_const.mul measurable_id)) hg 1
  have hh := hi.mul_bdd hA.aestronglyMeasurable
    (ae_of_all _ fun y => by simpa only [Real.norm_eq_abs] using bA y)
  convert hh using 1
  funext y
  rw [ENNReal.toReal_ofReal (mul_nonneg (Real.exp_pos _).le (hA0 y)), smul_eq_mul,
    Real.exp_add]
  ring

lemma magneticWeightedGaussian_mgf_analytic {F A : ℝ → ℝ}
    (hF : Measurable F) (hG : HasLinearGrowth F) (hA : Measurable A)
    {K : ℝ} (bA : ∀ y, |A y| ≤ K) (hA0 : ∀ y, 0 ≤ A y)
    (ζ : ℝ) (v : ℝ≥0) (t : ℝ) :
    AnalyticAt ℝ (mgf (fun y : ℝ => y) (magneticWeightedGaussian F A ζ v)) t := by
  have he : integrableExpSet (fun y : ℝ => y) (magneticWeightedGaussian F A ζ v) = univ := by
    ext u
    simp only [mem_univ, iff_true, integrableExpSet, mem_ofPred_eq]
    exact magneticWeightedGaussian_exp_integrable hF hG hA bA hA0 ζ u v
  apply analyticAt_mgf
  simp only [he, interior_univ, mem_univ]

lemma magneticGaussian_pdf_shift (v : ℝ≥0) (z y : ℝ) :
    gaussianPDFReal z v y = Real.exp (-(z ^ 2) / (2 * v)) *
      gaussianPDFReal 0 v y * Real.exp ((z / v) * y) := by
  by_cases hv : (v : ℝ) = 0
  · simp [gaussianPDFReal, hv]
  have he : -((y - z) ^ 2) / (2 * (v : ℝ)) =
      -(z ^ 2) / (2 * v) + -(y ^ 2) / (2 * v) + (z / v) * y := by
    field_simp [hv]
    ring
  simp only [gaussianPDFReal, sub_zero]
  rw [he, Real.exp_add, Real.exp_add]
  ring

lemma magneticGaussian_weighted_eq_laplace {F A : ℝ → ℝ}
    (hF : Measurable F) (hA : Measurable A) (hA0 : ∀ y, 0 ≤ A y)
    (ζ : ℝ) (v : ℝ≥0) (hv : v ≠ 0) (z : ℝ) :
    (∫ y, Real.exp (ζ * F y) * A y ∂gaussianReal z v) =
      Real.exp (-(z ^ 2) / (2 * v)) *
        mgf (fun y : ℝ => y) (magneticWeightedGaussian F A ζ v) (z / v) := by
  have hm : Measurable (fun y => ENNReal.ofReal (Real.exp (ζ * F y) * A y)) :=
    ((hF.const_mul ζ).exp.mul hA).ennreal_ofReal
  unfold mgf magneticWeightedGaussian
  rw [integral_withDensity_eq_integral_toReal_smul hm
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  simp_rw [ENNReal.toReal_ofReal (mul_nonneg (Real.exp_pos _).le (hA0 _)), smul_eq_mul]
  rw [integral_gaussianReal_eq_integral_smul hv, integral_gaussianReal_eq_integral_smul hv,
    ← integral_const_mul]
  apply integral_congr_ae
  apply ae_of_all
  intro y
  dsimp only
  rw [magneticGaussian_pdf_shift]
  simp only [smul_eq_mul]
  ring

lemma magneticGaussian_weighted_analytic {F A : ℝ → ℝ}
    (hF : Measurable F) (hG : HasLinearGrowth F) (hA : Measurable A)
    {K : ℝ} (bA : ∀ y, |A y| ≤ K) (hA0 : ∀ y, 0 ≤ A y)
    (ζ : ℝ) (v : ℝ≥0) (hv : v ≠ 0) (z : ℝ) :
    AnalyticAt ℝ (fun x => ∫ y, Real.exp (ζ * F y) * A y ∂gaussianReal x v) z := by
  have hM := magneticWeightedGaussian_mgf_analytic hF hG hA bA hA0 ζ v (z / v)
  have hc : AnalyticAt ℝ (fun x : ℝ => Real.exp (-(x ^ 2) / (2 * v))) z := by
    fun_prop
  have hl : AnalyticAt ℝ (fun x : ℝ => x / (v : ℝ)) z := by fun_prop
  have hh := hc.mul (hM.comp (f := fun x : ℝ => x / (v : ℝ)) hl)
  have he : (fun x => ∫ y, Real.exp (ζ * F y) * A y ∂gaussianReal x v) =
      fun x => Real.exp (-(x ^ 2) / (2 * v)) *
        mgf (fun y : ℝ => y) (magneticWeightedGaussian F A ζ v) (x / v) := by
    funext x
    exact magneticGaussian_weighted_eq_laplace hF hA hA0 ζ v hv x
  rwa [he]

end InvariantIsing

end

end OAI
