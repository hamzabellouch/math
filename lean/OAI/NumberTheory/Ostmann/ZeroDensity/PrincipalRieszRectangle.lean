import OAI.NumberTheory.Ostmann.ZeroDensity.PrincipalRieszIntegral
import OAI.NumberTheory.Ostmann.ZeroDensity.RieszPoleRectangle
import OAI.NumberTheory.Ostmann.ZeroDensity.RegularizedZeta

namespace OAI

/-! # The principal Riesz rectangle, including zeta's actual pole -/

namespace Ostmann

open Complex Filter Set
open scoped Topology Interval

theorem regularizedZeta_logDeriv_off_one (s : ℂ) (hs : s ≠ 1) (hz : riemannZeta s ≠ 0) :
    logDeriv regularizedZeta s = (s - 1)⁻¹ + logDeriv riemannZeta s := by
  have he : regularizedZeta =ᶠ[𝓝 s] ((fun z : ℂ => z - 1) * riemannZeta) := by
    filter_upwards [isOpen_ne.mem_nhds hs] with z hz
    exact regularizedZeta_eq z hz
  rw [(logDeriv_congr_nhds he).self_of_nhds,
    logDeriv_mul (f := fun z : ℂ => z - 1) (g := riemannZeta) s
      (sub_ne_zero.mpr hs) hz (differentiableAt_id.sub_const _) (differentiableAt_riemannZeta hs)]
  simp [logDeriv_apply]

noncomputable def principalRieszContour (X : ℝ) (s : ℂ) : ℂ :=
  -logDeriv riemannZeta s * rieszContourWeight X s

theorem principalRieszContour_rectangle (X : ℝ) (hX : 0 < X) (a b c d : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hb : 1 < b) (hc : c < 0) (hd : 0 < d)
    (hne : ∀ s ∈ uIcc a b ×ℂ uIcc c d, regularizedZeta s ≠ 0) :
    rectangleBoundaryIntegral (principalRieszContour X) a b c d =
      (2 * (Real.pi : ℂ) * I) * (X / 2 : ℝ) := by
  let g : ℂ → ℂ := fun s => -logDeriv regularizedZeta s * rieszContourWeight X s
  let p : ℂ → ℂ := fun s => rieszContourWeight X s / (s - 1)
  have hspos (s : ℂ) (hs : s ∈ uIcc a b ×ℂ uIcc c d) : 0 < s.re :=
    ha.trans_le ((uIcc_of_le (ha1.trans hb).le) ▸ hs.1).1
  have hg : ∀ s ∈ uIcc a b ×ℂ uIcc c d, AnalyticAt ℂ g s := by
    intro s hs
    exact (((regularizedZeta_analytic s).deriv.div (regularizedZeta_analytic s)
      (hne s hs)).neg).mul (rieszContourWeight_analyticAt X hX s (hspos s hs))
  have hnot (s : ℂ) (hs : s ∈ contourRectangleBoundary a b c d) : s ≠ 1 :=
    contourBoundary_ne_interior ⟨ha1, hb, hc, hd⟩ hs
  have hgI : RectangleIntegrable g a b c d := rectangleIntegrable_of_continuousOn
    (fun s hs => (hg s ⟨hs.1, hs.2.1⟩).continuousAt.continuousWithinAt)
  have hpI : RectangleIntegrable p a b c d := by
    apply rectangleIntegrable_of_continuousOn
    intro s hs
    exact ((rieszContourWeight_analyticAt X hX s (hspos s ⟨hs.1, hs.2.1⟩)).div
      (analyticAt_id.sub analyticAt_const) (sub_ne_zero.mpr (hnot s hs))).continuousAt.continuousWithinAt
  have heq : rectangleBoundaryIntegral (principalRieszContour X) a b c d =
      rectangleBoundaryIntegral (fun s => g s + p s) a b c d := by
    apply rectangleBoundaryIntegral_congr
    intro s hs
    have hz : riemannZeta s ≠ 0 := by
      intro he
      apply hne s ⟨hs.1, hs.2.1⟩
      rw [regularizedZeta_eq s (hnot s hs), he, mul_zero]
    have hh := regularizedZeta_logDeriv_off_one s (hnot s hs) hz
    dsimp [principalRieszContour, g, p]
    rw [hh]
    ring
  rw [heq, rectangleBoundaryIntegral_add hgI hpI, rectangleBoundaryIntegral_eq_zero hg, zero_add]
  have hp := riesz_pole_rectangle X hX 1 a b c d ha ha1 hb hc hd
  change rectangleBoundaryIntegral (fun s => rieszContourWeight X s / (s - 1)) a b c d = _ at hp
  have hweight : rieszContourWeight X (1 : ℂ) = (X / 2 : ℝ) := by
    simp [rieszContourWeight, rieszMellinKernel]
    ring
  simpa only [p, Complex.ofReal_one, hweight] using hp

end Ostmann

end OAI
