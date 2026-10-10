import OAI.NumberTheory.Ostmann.ZeroDensity.DensityDetectorIntegral
import OAI.NumberTheory.Ostmann.ZeroDensity.RectangleAnalyticPole

namespace OAI

/-! # Cancellation of the detector contour pole at an actual L-function zero -/

namespace Ostmann

open Complex Set
open scoped BigOperators

noncomputable def densityDetectorFactor (χ : PrimitiveComplexCharacter) (X : ℕ)
    (s : ℂ) (Y : ℝ) (w : ℂ) : ℂ :=
  χ.L (s + w) * densityMollifier X χ.character (s + w) * (Y : ℂ) ^ w /
    ((w + 1) * (w + 2))

noncomputable def densityDetectorIntegrand (χ : PrimitiveComplexCharacter) (X : ℕ)
    (s : ℂ) (Y : ℝ) (w : ℂ) : ℂ :=
  χ.L (s + w) * densityMollifier X χ.character (s + w) * (Y : ℂ) ^ w *
    densityDetectorKernel w

 theorem densityMollifier_shift_analytic (χ : PrimitiveComplexCharacter) (X : ℕ)
    (s w : ℂ) : AnalyticAt ℂ (fun z => densityMollifier X χ.character (s + z)) w := by
  unfold densityMollifier
  apply Finset.analyticAt_fun_sum
  intro n hn
  have hnp : 0 < n := (Finset.mem_Icc.mp hn).1
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hnp.ne'
  have hp := ((differentiable_id.const_cpow (Or.inl hnC)).analyticAt (s + w)).comp
    (analyticAt_const.add analyticAt_id : AnalyticAt ℂ (fun z : ℂ => s + z) w)
  exact analyticAt_const.div hp (Complex.cpow_ne_zero_iff.mpr (Or.inl hnC))

 theorem densityDetectorFactor_analytic (χ : PrimitiveComplexCharacter) (X : ℕ)
    (s : ℂ) (Y : ℝ) (hY : 0 < Y) (w : ℂ) (hw : -1 < w.re) :
    AnalyticAt ℂ (densityDetectorFactor χ X s Y) w := by
  have hy : (Y : ℂ) ≠ 0 := by exact_mod_cast hY.ne'
  have h1 : w + 1 ≠ 0 := by
    intro h
    have hr := congrArg Complex.re h
    norm_num at hr
    linarith
  have h2 : w + 2 ≠ 0 := by
    intro h
    have hr := congrArg Complex.re h
    norm_num at hr
    linarith
  exact ((((χ.L_analytic (s + w)).comp (analyticAt_const.add analyticAt_id)).mul
    (densityMollifier_shift_analytic χ X s w)).mul
      ((differentiable_id.const_cpow (Or.inl hy)).analyticAt w)).div
        ((analyticAt_id.add analyticAt_const).mul (analyticAt_id.add analyticAt_const))
        (mul_ne_zero h1 h2)

 theorem densityDetectorIntegrand_eq (χ : PrimitiveComplexCharacter) (X : ℕ)
    (s : ℂ) (Y : ℝ) (w : ℂ) :
    densityDetectorIntegrand χ X s Y w = densityDetectorFactor χ X s Y w / w := by
  unfold densityDetectorIntegrand densityDetectorFactor densityDetectorKernel
  simp only [div_eq_mul_inv, mul_inv_rev, one_mul]
  ring

 theorem densityDetector_rectangle_zero (χ : PrimitiveComplexCharacter) (X : ℕ)
    (s : ℂ) (hz : χ.L s = 0) (Y : ℝ) (hY : 0 < Y)
    (a b c d : ℝ) (ha0 : a < 0) (ha : -1 < a) (hb : 0 < b) (hc : c < 0) (hd : 0 < d) :
    rectangleBoundaryIntegral (densityDetectorIntegrand χ X s Y) a b c d = 0 := by
  have hf : ∀ w ∈ uIcc a b ×ℂ uIcc c d,
      AnalyticAt ℂ (densityDetectorFactor χ X s Y) w := by
    intro w hw
    have hr : a ≤ w.re := by
      have h := hw.1
      exact (show w.re ∈ Icc a b from by simpa only [uIcc_of_le (ha0.trans hb).le, mem_preimage] using h).1
    exact densityDetectorFactor_analytic χ X s Y hY w (ha.trans_le hr)
  have h := rectangle_analytic_pole (densityDetectorFactor χ X s Y) a b c d ha0 hb hc hd hf
  have he : densityDetectorFactor χ X s Y 0 = 0 := by simp [densityDetectorFactor, hz]
  simp only [he, mul_zero] at h
  convert h using 1
  exact congrArg (fun f => rectangleBoundaryIntegral f a b c d)
    (funext (densityDetectorIntegrand_eq χ X s Y))

end Ostmann

end OAI
