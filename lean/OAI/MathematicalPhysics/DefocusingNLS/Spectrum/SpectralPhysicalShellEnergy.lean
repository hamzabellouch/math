import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralLiouvilleShellEnergy
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

namespace OAI

/-! Transfer the normalized physical H¹ shell bound to the Liouville
Cauchy energy used for selecting a good point. -/

open Set MeasureTheory
namespace DefocusingNLS

noncomputable def spectralPhysicalShellDensity (f g : ℝ → ℂ) (r : ℝ) : ℝ :=
  r^11*(‖f r‖^2+‖deriv f r‖^2+‖g r‖^2+‖deriv g r‖^2)

theorem spectralPhysicalLiouvillePair_shell_energy (R B r : ℝ)
    (hR : 0 < R) (hRr : R ≤ r) (hrB : r ≤ B) (f g : ℝ → ℂ) :
    let q := spectralPhysicalLiouvillePair f g
    ‖(q r).1.2‖^2+‖(q r).2.2‖^2 ≤
      2*(1+(11/(2*R)+B/4)^2)*spectralPhysicalShellDensity f g r := by
  have hp := spectralLiouvilleState_slope_energy 1 R B r (by norm_num) hR hRr hrB (f r) (deriv f r)
  have hm := spectralLiouvilleState_slope_energy (-1) R B r (by norm_num) hR hRr hrB (g r) (deriv g r)
  let S := 11/(2*R)+B/4
  have hpos : 0 ≤ 2*r^11 := by have := hR.trans_le hRr; positivity
  have hsum : ‖deriv f r‖^2+S^2*‖f r‖^2+(‖deriv g r‖^2+S^2*‖g r‖^2) ≤
      (1+S^2)*(‖f r‖^2+‖deriv f r‖^2+‖g r‖^2+‖deriv g r‖^2) := by
    nlinarith [sq_nonneg ‖f r‖,sq_nonneg ‖g r‖,
      mul_nonneg (sq_nonneg S) (sq_nonneg ‖deriv f r‖),
      mul_nonneg (sq_nonneg S) (sq_nonneg ‖deriv g r‖)]
  dsimp only [spectralPhysicalLiouvillePair,homogeneousSpectralLocalizationState]
  apply (add_le_add hp hm).trans
  have hs := mul_le_mul_of_nonneg_left hsum hpos
  dsimp only [spectralPhysicalShellDensity,S] at hs ⊢
  nlinarith only [hs]

theorem spectralPhysicalShellDensity_continuous (f g : ℝ → ℂ)
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) :
    Continuous (spectralPhysicalShellDensity f g) := by
  have hdf := hf.continuous_deriv (by norm_num)
  have hdg := hg.continuous_deriv (by norm_num)
  exact (continuous_id.pow 11).mul
    ((((hf.continuous.norm.pow 2).add (hdf.norm.pow 2)).add (hg.continuous.norm.pow 2)).add (hdg.norm.pow 2))

theorem spectralPhysicalLiouvillePair_continuous_shell (R B : ℝ) (hR : 0 < R)
    (f g : ℝ → ℂ) (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) :
    ContinuousOn (spectralPhysicalLiouvillePair f g) (Icc R B) := by
  have hf' := (hf.continuous_deriv (by norm_num)).continuousOn (s := Icc R B)
  have hg' := (hg.continuous_deriv (by norm_num)).continuousOn (s := Icc R B)
  have hA (h : ℝ) : ContinuousOn (homogeneousSpectralLocalizationFactor h) (Icc R B) :=
    fun r hr => (homogeneousSpectralLocalizationFactor_hasDerivAt h r (hR.trans_le hr.1)).continuousAt.continuousWithinAt
  have hS (h : ℝ) : ContinuousOn (homogeneousSpectralLocalizationSlope h) (Icc R B) :=
    fun r hr => (homogeneousSpectralLocalizationSlope_hasDerivAt h r (hR.trans_le hr.1)).continuousAt.continuousWithinAt
  exact (((hA 1).mul hf.continuous.continuousOn).prodMk
    ((hA 1).mul (hf'.add ((hS 1).mul hf.continuous.continuousOn)))).prodMk
      (((hA (-1)).mul hg.continuous.continuousOn).prodMk
        ((hA (-1)).mul (hg'.add ((hS (-1)).mul hg.continuous.continuousOn))))

theorem spectralPhysicalLiouvillePair_shell_integral (R B M : ℝ) (hR : 0 < R) (hRB : R ≤ B)
    (f g : ℝ → ℂ) (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (hbound : (∫ r in R..B, spectralPhysicalShellDensity f g r) ≤ M) :
    (∫ r in R..B, ‖(spectralPhysicalLiouvillePair f g r).1.2‖^2+
      ‖(spectralPhysicalLiouvillePair f g r).2.2‖^2) ≤ 2*(1+(11/(2*R)+B/4)^2)*M := by
  let C := 2*(1+(11/(2*R)+B/4)^2)
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hq := spectralPhysicalLiouvillePair_continuous_shell R B hR f g hf hg
  have hqc := (hq.fst.snd.norm.pow 2).add (hq.snd.snd.norm.pow 2)
  have hfc := (spectralPhysicalShellDensity_continuous f g hf hg).continuousOn (s := Icc R B)
  have hi := intervalIntegral.integral_mono_on (μ := volume) hRB
    (hqc.intervalIntegrable_of_Icc hRB) ((hfc.const_mul C).intervalIntegrable_of_Icc hRB)
    (fun r hr => spectralPhysicalLiouvillePair_shell_energy R B r hR hr.1 hr.2 f g)
  rw [intervalIntegral.integral_const_mul] at hi
  exact hi.trans (mul_le_mul_of_nonneg_left hbound hC)

end DefocusingNLS

end OAI
