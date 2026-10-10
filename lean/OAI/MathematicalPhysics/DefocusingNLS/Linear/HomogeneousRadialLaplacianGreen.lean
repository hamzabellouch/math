import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousRadialMeasure
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.ContDiff.Deriv

namespace OAI

/-! # The one-dimensional radial Green identity in dimension twelve -/

open Set MeasureTheory
open scoped SchwartzMap

namespace DefocusingNLS

private theorem compactScalarTest_integrable (φ : 𝓢(ℝ, ℂ))
    (hc : HasCompactSupport φ) (g : ℝ → ℂ) (hg : Continuous g) :
    Integrable (fun r => φ r * g r) :=
  (φ.continuous.mul hg).integrable_of_hasCompactSupport hc.mul_right

theorem compactScalarTest_first_green (φ : 𝓢(ℝ, ℂ))
    (hc : HasCompactSupport φ) (g g' : ℝ → ℂ)
    (hg : ∀ r, HasDerivAt g (g' r) r) (hg' : Continuous g') :
    (∫ r, φ r * g' r) = -(∫ r, deriv φ r * g r) := by
  let φ' := SchwartzMap.derivCLM ℂ ℂ φ
  have hc' : HasCompactSupport φ' := hc.of_isClosed_subset isClosed_closure
    (SchwartzMap.tsupport_derivCLM_subset ℂ φ)
  have hgc : Continuous g := continuous_iff_continuousAt.mpr fun r => (hg r).continuousAt
  exact integral_bilinear_hasDerivAt_right_eq_neg_left_of_integrable
    (L := ContinuousLinearMap.mul ℝ ℂ)
    (fun r _ => φ.hasDerivAt r) (fun r _ => hg r)
    (compactScalarTest_integrable φ hc g' hg')
    (compactScalarTest_integrable φ' hc' g hgc)
    (compactScalarTest_integrable φ hc g hgc)

private theorem deriv_radialWeighted_firstTest (φ : 𝓢(ℝ, ℂ)) (r : ℝ) :
    deriv (radialWeightedSchwartzTest (SchwartzMap.derivCLM ℂ ℂ φ)) r =
      11 * (r : ℂ) ^ 10 * deriv φ r + (r : ℂ) ^ 11 * deriv (deriv φ) r := by
  have hp : HasDerivAt (fun s : ℝ => (s : ℂ) ^ 11) (11 * (r : ℂ) ^ 10) r := by
    convert! ((hasDerivAt_id r).ofReal_comp.pow 11) using 1
    simp
  have hφ : HasDerivAt (deriv φ) (deriv (deriv φ) r) r :=
    ((φ.smooth 2).differentiable_deriv_two r).hasDerivAt
  have he : (radialWeightedSchwartzTest (SchwartzMap.derivCLM ℂ ℂ φ) : ℝ → ℂ) =
      fun s : ℝ => (s : ℂ) ^ 11 * deriv φ s := by
    funext s
    rw [radialWeightedSchwartzTest_apply, SchwartzMap.derivCLM_apply]
  rw [he]
  exact (hp.mul hφ).deriv

/-- The radial divergence operator is symmetric against a compact smooth
test. The function being tested only needs two continuous derivatives. -/
theorem radial_divergence_green (φ : 𝓢(ℝ, ℂ)) (hc : HasCompactSupport φ)
    (A : ℝ → ℂ) (hA : ContDiff ℝ 2 A) :
    (∫ r : ℝ, ((r : ℂ) ^ 11 * deriv (deriv φ) r +
      11 * (r : ℂ) ^ 10 * deriv φ r) * A r) =
    ∫ r : ℝ, φ r * ((r : ℂ) ^ 11 * deriv (deriv A) r +
      11 * (r : ℂ) ^ 10 * deriv A r) := by
  let φ' := SchwartzMap.derivCLM ℂ ℂ φ
  let W := radialWeightedSchwartzTest φ'
  let g : ℝ → ℂ := fun r => (r : ℂ) ^ 11 * deriv A r
  let gd : ℝ → ℂ := fun r => 11 * (r : ℂ) ^ 10 * deriv A r +
    (r : ℂ) ^ 11 * deriv (deriv A) r
  have hAd : ContDiff ℝ 1 (deriv A) := hA.deriv'
  have hAc := hA.continuous_deriv (by norm_num)
  have hAddc := hAd.continuous_deriv (by norm_num)
  have hWc : HasCompactSupport W := hc.of_isClosed_subset isClosed_closure
    ((tsupport_radialWeightedSchwartzTest_subset φ').trans
      (SchwartzMap.tsupport_derivCLM_subset ℂ φ))
  have hg (r : ℝ) : HasDerivAt g (gd r) r := by
    have hp : HasDerivAt (fun s : ℝ => (s : ℂ) ^ 11) (11 * (r : ℂ) ^ 10) r := by
      convert! ((hasDerivAt_id r).ofReal_comp.pow 11) using 1
      simp
    exact hp.mul (hAd.differentiable one_ne_zero r).hasDerivAt
  have hgdc : Continuous gd := by
    exact ((continuous_const.mul (Complex.continuous_ofReal.pow 10)).mul hAc).add
      ((Complex.continuous_ofReal.pow 11).mul hAddc)
  have hfirst := compactScalarTest_first_green W hWc A (deriv A)
    (fun r => (hA.differentiable (by norm_num) r).hasDerivAt) hAc
  have hsecond := compactScalarTest_first_green φ hc g gd hg hgdc
  calc
    _ = ∫ r : ℝ, deriv W r * A r := by
      apply integral_congr_ae
      filter_upwards [] with r
      rw [deriv_radialWeighted_firstTest]
      ring
    _ = -(∫ r : ℝ, W r * deriv A r) := by
      simpa only [neg_neg] using congrArg Neg.neg hfirst.symm
    _ = -(∫ r : ℝ, deriv φ r * g r) := by
      congr 1
      apply integral_congr_ae
      filter_upwards [] with r
      simp only [W, φ', radialWeightedSchwartzTest_apply, SchwartzMap.derivCLM_apply, g]
      ring
    _ = ∫ r : ℝ, φ r * gd r := hsecond.symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with r
      dsimp only [gd]
      ring

theorem radial_laplacian_green (φ : 𝓢(ℝ, ℂ)) (hc : HasCompactSupport φ)
    (A : ℝ → ℂ) (hA : ContDiff ℝ 2 A) (lam : ℂ) :
    (∫ r : ℝ, ((r : ℂ) ^ 11 * deriv (deriv φ) r +
      11 * (r : ℂ) ^ 10 * deriv φ r - lam * (r : ℂ) ^ 9 * φ r) * A r) =
    ∫ r : ℝ, φ r * ((r : ℂ) ^ 11 * deriv (deriv A) r +
      11 * (r : ℂ) ^ 10 * deriv A r - lam * (r : ℂ) ^ 9 * A r) := by
  let φ' := SchwartzMap.derivCLM ℂ ℂ φ
  let φ'' := SchwartzMap.derivCLM ℂ ℂ φ'
  have hc' : HasCompactSupport φ' := hc.of_isClosed_subset isClosed_closure
    (SchwartzMap.tsupport_derivCLM_subset ℂ φ)
  have hc'' : HasCompactSupport φ'' := hc'.of_isClosed_subset isClosed_closure
    (SchwartzMap.tsupport_derivCLM_subset ℂ φ')
  have hiL : Integrable (fun r : ℝ =>
      ((r : ℂ) ^ 11 * deriv (deriv φ) r + 11 * (r : ℂ) ^ 10 * deriv φ r) * A r) := by
    convert (compactScalarTest_integrable φ'' hc''
      (fun r => (r : ℂ) ^ 11 * A r)
      ((Complex.continuous_ofReal.pow 11).mul hA.continuous)).add
      (compactScalarTest_integrable φ' hc' (fun r => 11 * (r : ℂ) ^ 10 * A r)
        ((continuous_const.mul (Complex.continuous_ofReal.pow 10)).mul hA.continuous)) using 1
    ext r
    simp only [Pi.add_apply, φ'', φ', SchwartzMap.derivCLM_apply]
    change _ = deriv (deriv φ) r * ((r : ℂ) ^ 11 * A r) +
      deriv φ r * (11 * (r : ℂ) ^ 10 * A r)
    ring
  have hiR := compactScalarTest_integrable φ hc
    (fun r : ℝ => (r : ℂ) ^ 11 * deriv (deriv A) r +
      11 * (r : ℂ) ^ 10 * deriv A r)
    (((Complex.continuous_ofReal.pow 11).mul
      ((hA.deriv' : ContDiff ℝ 1 (deriv A)).continuous_deriv (by norm_num))).add
      ((continuous_const.mul (Complex.continuous_ofReal.pow 10)).mul
        (hA.continuous_deriv (by norm_num))))
  have hiH := compactScalarTest_integrable φ hc
    (fun r : ℝ => lam * (r : ℂ) ^ 9 * A r)
    ((continuous_const.mul (Complex.continuous_ofReal.pow 9)).mul hA.continuous)
  calc
    _ = (∫ r : ℝ, ((r : ℂ) ^ 11 * deriv (deriv φ) r +
        11 * (r : ℂ) ^ 10 * deriv φ r) * A r) -
        ∫ r : ℝ, φ r * (lam * (r : ℂ) ^ 9 * A r) := by
      rw [← integral_sub hiL hiH]
      apply integral_congr_ae
      filter_upwards [] with r
      ring
    _ = (∫ r : ℝ, φ r * ((r : ℂ) ^ 11 * deriv (deriv A) r +
        11 * (r : ℂ) ^ 10 * deriv A r)) -
        ∫ r : ℝ, φ r * (lam * (r : ℂ) ^ 9 * A r) := by
      rw [radial_divergence_green φ hc A hA]
    _ = _ := by
      rw [← integral_sub hiR hiH]
      apply integral_congr_ae
      filter_upwards [] with r
      ring

end DefocusingNLS

end OAI
