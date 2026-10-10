import OAI.MathematicalPhysics.DefocusingNLS.Certificates.RectangleBoundaryLinear
import OAI.MathematicalPhysics.DefocusingNLS.Certificates.RectangleRatioSlit
import Mathlib.Analysis.Calculus.LogDeriv

namespace OAI

/-! # Boundary logarithms compare logarithmic-derivative integrals -/

open Set
namespace DefocusingNLS

theorem countingBoundaryIntegral_logDeriv_eq_of_ratio (V : ℝ) (hV : 0 < V)
    (f g : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f (countingRectangleBoundary V))
    (hg : AnalyticOnNhd ℂ g (countingRectangleBoundary V))
    (hnf : ∀ z ∈ countingRectangleBoundary V, f z ≠ 0)
    (hng : ∀ z ∈ countingRectangleBoundary V, g z ≠ 0)
    (hs : ∀ z ∈ countingRectangleBoundary V, f z / g z ∈ Complex.slitPlane) :
    countingBoundaryIntegral V (logDeriv f) = countingBoundaryIntegral V (logDeriv g) := by
  have hr : AnalyticOnNhd ℂ (fun z => f z / g z) (countingRectangleBoundary V) :=
    fun z hz => (hf z hz).div (hg z hz) (hng z hz)
  have hl := hr.clog hs
  have he : EqOn (deriv (fun z => Complex.log (f z / g z)))
      (fun z => logDeriv f z - logDeriv g z) (countingRectangleBoundary V) := by
    intro z hz
    change deriv (Complex.log ∘ (fun z => f z / g z)) z = _
    rw [Complex.deriv_log_comp_eq_logDeriv (hr z hz).differentiableAt (hs z hz)]
    exact logDeriv_fun_div z (hnf z hz) (hng z hz)
      (hf z hz).differentiableAt (hg z hz).differentiableAt
  have hlf : ContinuousOn (logDeriv f) (countingRectangleBoundary V) :=
    (hf.deriv.div hf hnf).continuousOn
  have hlg : ContinuousOn (logDeriv g) (countingRectangleBoundary V) :=
    (hg.deriv.div hg hng).continuousOn
  have hi := countingBoundaryIntegral_deriv V hV _ hl
  rw [countingBoundaryIntegral_congr V hV he,
    countingBoundaryIntegral_sub V hV _ _ hlf hlg] at hi
  exact sub_eq_zero.mp hi

theorem countingBoundaryIntegral_rouche (V : ℝ) (hV : 0 < V) (f g : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f (closedCountingRectangle V))
    (hg : AnalyticOnNhd ℂ g (closedCountingRectangle V))
    (hn : ∀ z ∈ countingRectangleBoundary V, ‖g z - f z‖ < ‖f z‖) :
    countingBoundaryIntegral V (logDeriv f) = countingBoundaryIntegral V (logDeriv g) := by
  have hnf (z : ℂ) (hz : z ∈ countingRectangleBoundary V) : f z ≠ 0 :=
    norm_pos_iff.mp ((norm_nonneg _).trans_lt (hn z hz))
  have hng (z : ℂ) (hz : z ∈ countingRectangleBoundary V) : g z ≠ 0 := by
    intro he
    have hi := hn z hz
    simp [he] at hi
  symm
  apply countingBoundaryIntegral_logDeriv_eq_of_ratio V hV g f
    (fun z hz => hg z hz.1) (fun z hz => hf z hz.1) hng hnf
  intro z hz
  have he : g z / f z = 1 + (g z - f z) / f z := by field_simp [hnf z hz]; ring
  rw [he]
  apply Complex.mem_slitPlane_of_norm_lt_one
  rw [norm_div]
  exact (div_lt_one (norm_pos_iff.mpr (hnf z hz))).mpr (hn z hz)

theorem countingBoundaryIntegral_inv_sub_eq (V : ℝ) (hV : 0 < V) (a b : ℂ)
    (ha : a ∈ countingRectangle V) (hb : b ∈ countingRectangle V) :
    countingBoundaryIntegral V (fun z => (z - a)⁻¹) =
      countingBoundaryIntegral V (fun z => (z - b)⁻¹) := by
  have hi := countingBoundaryIntegral_logDeriv_eq_of_ratio V hV
    (fun z => z - a) (fun z => z - b) (by fun_prop) (by fun_prop)
    (fun z hz => sub_ne_zero.mpr (countingBoundary_ne_interior hz ha))
    (fun z hz => sub_ne_zero.mpr (countingBoundary_ne_interior hz hb))
    (fun z hz => countingBoundary_ratio_mem_slitPlane hz ha hb)
  have he (c : ℂ) : logDeriv (fun z : ℂ => z - c) = fun z => (z - c)⁻¹ := by
    funext z
    simp [logDeriv_apply]
  simpa only [he a, he b] using hi

end DefocusingNLS

end OAI
