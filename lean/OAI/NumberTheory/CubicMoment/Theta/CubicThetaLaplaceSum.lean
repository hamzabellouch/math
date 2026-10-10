import OAI.NumberTheory.CubicMoment.Theta.CubicThetaFourierHeat

namespace OAI

/-! Absolute Laplace interchange for the Eisenstein lattice row. -/
noncomputable section
open MeasureTheory Set
namespace CubicFirstMoment

def cubicThetaLaplaceTerm (a : ℂ) (R : ℝ) (s : ℂ) (t : ℝ) : ℂ :=
  a*(t:ℂ)^(s-1)*(Real.exp (-R*t):ℂ)

lemma cubicThetaLaplaceTerm_norm (a : ℂ) (R : ℝ) (s : ℂ) {t : ℝ} (ht : 0 < t) :
    ‖cubicThetaLaplaceTerm a R s t‖ = ‖a‖*t^(s.re-1)*Real.exp (-R*t) := by
  simp only [cubicThetaLaplaceTerm, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht,
    Complex.sub_re, Complex.one_re, Complex.norm_real,
    Real.norm_of_nonneg (Real.exp_nonneg _)]

lemma cubicThetaLaplaceTerm_integrable (a : ℂ) {R : ℝ} (hR : 0 < R)
    {s : ℂ} (hs : 0 < s.re) : IntegrableOn (cubicThetaLaplaceTerm a R s) (Ioi 0) := by
  have hm : AEStronglyMeasurable (cubicThetaLaplaceTerm a R s)
      (volume.restrict (Ioi 0)) := by
    apply Measurable.aestronglyMeasurable
    unfold cubicThetaLaplaceTerm
    fun_prop
  apply ((integrable_laplace_rpow hs hR).const_mul ‖a‖).mono' hm
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [cubicThetaLaplaceTerm_norm a R s ht]
  simp only [mul_assoc, le_refl]

lemma cubicThetaLaplaceTerm_mass (a : ℂ) {R : ℝ} (hR : 0 < R)
    {s : ℂ} (hs : 0 < s.re) :
    (∫ t in Ioi (0:ℝ), ‖cubicThetaLaplaceTerm a R s t‖) =
      Real.Gamma s.re*(‖a‖*R^(-s.re)) := by
  calc
    _ = ‖a‖*(∫ t in Ioi (0:ℝ), t^(s.re-1)*Real.exp (-R*t)) := by
      rw [← integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      dsimp only
      rw [cubicThetaLaplaceTerm_norm a R s ht]
      ring
    _ = _ := by rw [laplace_rpow hs hR]; ring

lemma cubicThetaLaplaceTerm_integral (a : ℂ) {R : ℝ} (hR : 0 < R)
    {s : ℂ} (hs : 0 < s.re) :
    (∫ t in Ioi (0:ℝ), cubicThetaLaplaceTerm a R s t) =
      Complex.Gamma s*(a*(R:ℂ)^(-s)) := by
  unfold cubicThetaLaplaceTerm
  simp_rw [mul_assoc]
  rw [integral_const_mul]
  have he : (fun t : ℝ => (t:ℂ)^(s-1)*(Real.exp (-R*t):ℂ)) =
      fun t : ℝ => (t:ℂ)^(s-1)*Complex.exp (-((R:ℂ)*(t:ℂ))) := by
    funext t
    rw [Complex.ofReal_exp]
    push_cast
    rw [neg_mul]
  rw [he, Complex.integral_cpow_mul_exp_neg_mul_Ioi hs hR]
  simp only [one_div, Complex.inv_cpow_ofReal_nonneg hR.le, ← Complex.cpow_neg]
  ring

theorem cubicTheta_laplace_tsum (a : Eisenstein → ℂ) (R : Eisenstein → ℝ)
    (hR : ∀ d, 0 < R d) {s : ℂ} (hs : 0 < s.re)
    (hsum : Summable (fun d => ‖a d‖*(R d)^(-s.re))) :
    Complex.Gamma s*(∑' d : Eisenstein, a d*(R d:ℂ)^(-s)) =
      ∫ t in Ioi (0:ℝ), (t:ℂ)^(s-1)*
        ∑' d : Eisenstein, a d*(Real.exp (-R d*t):ℂ) := by
  let : Countable Eisenstein := coordinatesEquiv.symm.injective.countable
  have hm : Summable (fun d => ∫ t in Ioi (0:ℝ), ‖cubicThetaLaplaceTerm (a d) (R d) s t‖) := by
    simp_rw [cubicThetaLaplaceTerm_mass _ (hR _) hs]
    exact hsum.mul_left _
  have hi := integral_tsum_of_summable_integral_norm
    (fun d => cubicThetaLaplaceTerm_integrable (a d) (hR d) hs) hm
  calc
    _ = ∑' d : Eisenstein, ∫ t in Ioi (0:ℝ), cubicThetaLaplaceTerm (a d) (R d) s t := by
      simp_rw [cubicThetaLaplaceTerm_integral _ (hR _) hs]
      rw [tsum_mul_left]
    _ = ∫ t in Ioi (0:ℝ), ∑' d : Eisenstein, cubicThetaLaplaceTerm (a d) (R d) s t := hi
    _ = _ := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t _
      dsimp only
      rw [← tsum_mul_left]
      apply tsum_congr
      intro d
      unfold cubicThetaLaplaceTerm
      ring

end CubicFirstMoment

end

end OAI
