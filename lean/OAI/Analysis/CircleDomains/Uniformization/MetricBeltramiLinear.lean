import OAI.Analysis.CircleDomains.Uniformization.MetricBeltramiReconstruction

namespace OAI

/-! The exact positive metric-conformality equations for a real differential
solving the associated complex Beltrami equation. -/
open Matrix
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

lemma metric_gram_of_beltrami_linear {A : PlanarMetric} (hA : A.PosDef)
    (L : ℂ →L[ℝ] ℂ) (a : ℂ) (ha : a ≠ 0)
    (hL : ∀ z, L z = a * z + (metricBeltramiCoefficient A * a) * star z) :
    ∃ scale : ℝ, 0 < scale ∧
      (L 1).re^2 + (L 1).im^2 = scale * A 0 0 ∧
      (L Complex.I).re^2 + (L Complex.I).im^2 = scale * A 1 1 ∧
      (L 1).re * (L Complex.I).re + (L 1).im * (L Complex.I).im = scale * A 0 1 ∧
      0 < (L 1).re * (L Complex.I).im - (L Complex.I).re * (L 1).im := by
  let μ := metricBeltramiCoefficient A
  have h1 : L 1 = a * (1 + μ) := by rw [hL]; dsimp [μ]; simp; ring
  have hI : L Complex.I = a * (1 - μ) * Complex.I := by
    rw [hL]
    dsimp [μ]
    simp only [Complex.conj_I]
    ring
  have hxx : (L 1).re^2 + (L 1).im^2 =
      ‖a‖^2 * ((1 + μ.re)^2 + μ.im^2) := by
    rw [h1, Complex.sq_norm]
    simp only [Complex.normSq_apply, Complex.mul_re, Complex.mul_im,
      Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im, zero_add]
    ring
  have hyy : (L Complex.I).re^2 + (L Complex.I).im^2 =
      ‖a‖^2 * ((1 - μ.re)^2 + μ.im^2) := by
    rw [hI, Complex.sq_norm]
    simp only [Complex.normSq_apply, Complex.mul_re, Complex.mul_im,
      Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im,
      Complex.I_re, Complex.I_im]
    ring
  have hxy : (L 1).re * (L Complex.I).re + (L 1).im * (L Complex.I).im =
      ‖a‖^2 * (2 * μ.im) := by
    rw [h1, hI, Complex.sq_norm]
    simp only [Complex.normSq_apply, Complex.mul_re, Complex.mul_im,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
      Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im]
    ring
  have hdet : (L 1).re * (L Complex.I).im - (L Complex.I).re * (L 1).im =
      ‖a‖^2 * (1 - ‖μ‖^2) := by
    rw [h1, hI]
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.mul_re, Complex.mul_im,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
      Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im]
    ring
  have hd := metricBeltramiDenominator_pos hA
  have ha2 : 0 < ‖a‖^2 := sq_pos_of_pos (norm_pos_iff.mpr ha)
  have hr := metricBeltramiCoefficient_reconstruction hA
  change A 0 0 = _ ∧ A 1 1 = _ ∧ A 0 1 = _ at hr
  refine ⟨4 * ‖a‖^2 / metricBeltramiDenominator A, div_pos (by positivity) hd, ?_, ?_, ?_, ?_⟩
  · rw [hxx, hr.1]
    field_simp [hd.ne']
    ring
  · rw [hyy, hr.2.1]
    field_simp [hd.ne']
    ring
  · rw [hxy, hr.2.2]
    field_simp [hd.ne']
    ring
  · rw [hdet]
    apply mul_pos ha2
    have hm : ‖μ‖ < 1 := metricBeltramiCoefficient_norm_lt_one hA
    nlinarith [norm_nonneg μ]

end CircleDomainRigidity

end

end OAI
