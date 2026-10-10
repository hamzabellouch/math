import OAI.NumberTheory.Ostmann.ZeroDensity.DensityMollifierBound
import OAI.NumberTheory.Ostmann.ZeroDensity.DensityDetectorKernelLeft

namespace OAI

/-! # Integrability at the critical-line side of the actual detector -/

namespace Ostmann

open Complex MeasureTheory

 theorem densityDetectorIntegrand_line_continuous (χ : PrimitiveComplexCharacter) (X : ℕ)
    (s : ℂ) (Y : ℝ) (hY : 0 < Y) (x : ℝ) (hx : -1 < x) (hx0 : x ≠ 0) :
    Continuous (fun u : ℝ => densityDetectorIntegrand χ X s Y ((x : ℂ) + u * I)) := by
  apply continuous_iff_continuousAt.mpr
  intro u
  have hw : (x : ℂ) + u * I ≠ 0 := by
    intro h
    have hr := congrArg Complex.re h
    exact hx0 (by simpa using hr)
  have ha : AnalyticAt ℂ (fun w => densityDetectorFactor χ X s Y w / w) ((x : ℂ) + u * I) :=
    (densityDetectorFactor_analytic χ X s Y hY _ (by simpa using hx)).div analyticAt_id hw
  have he : densityDetectorIntegrand χ X s Y = fun w => densityDetectorFactor χ X s Y w / w :=
    funext (densityDetectorIntegrand_eq χ X s Y)
  rw [he]
  exact ContinuousAt.comp (g := fun w : ℂ => densityDetectorFactor χ X s Y w / w)
    (f := fun v : ℝ => (x : ℂ) + v * I) ha.continuousAt (by fun_prop)

 theorem densityDetector_left_bound (χ : PrimitiveComplexCharacter) (X : ℕ)
    (s : ℂ) (hs : 1 / 2 < s.re) (hs1 : s.re ≤ 1) (Y : ℝ) (hY : 1 ≤ Y) (u : ℝ) :
    ‖densityDetectorIntegrand χ X s Y (((1 / 2 - s.re : ℝ) : ℂ) + u * I)‖ ≤
      (2 * ((χ.modulus : ℝ) + 1) * X * Y ^ 2 * (3 + |s.im|)) *
        (16 / (s.re - 1 / 2)) * (1 + |u|) ^ (-(2 : ℝ)) := by
  have hn := densityDetector_numerator_bound χ X s hs.le hs1 Y hY (1 / 2 - s.re) u le_rfl (by linarith)
  have hk := densityDetectorKernel_left_bound (s.re - 1 / 2) u (by linarith) (by linarith)
  have hx : (-(s.re - 1 / 2) : ℝ) = 1 / 2 - s.re := by ring
  rw [← Complex.ofReal_neg, hx] at hk
  rw [densityDetectorIntegrand, norm_mul]
  apply (mul_le_mul hn hk (norm_nonneg _) (by positivity)).trans_eq
  have he : (1 + |u|) * (1 + |u|) ^ (-(3 : ℝ)) = (1 + |u|) ^ (-(2 : ℝ)) := by
    rw [show -(2 : ℝ) = 1 + -(3 : ℝ) by ring,
      Real.rpow_add (by positivity : 0 < 1 + |u|), Real.rpow_one]
  calc
    _ = (2 * ((χ.modulus : ℝ) + 1) * X * Y ^ 2 * (3 + |s.im|)) *
        (16 / (s.re - 1 / 2)) * ((1 + |u|) * (1 + |u|) ^ (-(3 : ℝ))) := by ring
    _ = _ := by rw [he]

 theorem densityDetector_left_integrable (χ : PrimitiveComplexCharacter) (X : ℕ)
    (s : ℂ) (hs : 1 / 2 < s.re) (hs1 : s.re ≤ 1) (Y : ℝ) (hY : 1 ≤ Y) :
    Integrable (fun u : ℝ => densityDetectorIntegrand χ X s Y
      (((1 / 2 - s.re : ℝ) : ℂ) + u * I)) := by
  have hg : Integrable (fun u : ℝ => (1 + |u|) ^ (-(2 : ℝ))) := by
    simpa only [Real.norm_eq_abs] using
      (integrable_one_add_norm (E := ℝ) (by norm_num : (Module.finrank ℝ ℝ : ℝ) < 2))
  apply (hg.const_mul ((2 * ((χ.modulus : ℝ) + 1) * X * Y ^ 2 * (3 + |s.im|)) *
    (16 / (s.re - 1 / 2)))).mono'
  · exact (densityDetectorIntegrand_line_continuous χ X s Y (by linarith) _
      (by linarith) (by linarith)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (densityDetector_left_bound χ X s hs hs1 Y hY)

end Ostmann

end OAI
