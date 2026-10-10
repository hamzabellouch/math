import OAI.NumberTheory.Ostmann.ZeroDensity.RieszPoleRectangle

namespace OAI

/-! # A single pole under an analytic rectangle integral -/

namespace Ostmann

open Complex Filter Set
open scoped Topology

 theorem analytic_dslope_of_analytic (f : ℂ → ℂ) (z s : ℂ)
    (hz : AnalyticAt ℂ f z) (hs : AnalyticAt ℂ f s) : AnalyticAt ℂ (dslope f z) s := by
  by_cases he : s = z
  · subst s
    obtain ⟨p, hp⟩ := hz
    exact ⟨p.fslope, hp.has_fpower_series_dslope_fslope⟩
  · have hh : dslope f z =ᶠ[𝓝 s] fun w => (w - z)⁻¹ * (f w - f z) := by
      filter_upwards [isOpen_ne.mem_nhds he] with w hw
      rw [dslope_of_ne f hw]
      rfl
    exact (((analyticAt_id.sub analyticAt_const).inv (sub_ne_zero.mpr he)).mul
      (hs.sub analyticAt_const)).congr hh.symm

 theorem rectangle_analytic_pole (f : ℂ → ℂ) (a b c d : ℝ)
    (ha : a < 0) (hb : 0 < b) (hc : c < 0) (hd : 0 < d)
    (hf : ∀ z ∈ uIcc a b ×ℂ uIcc c d, AnalyticAt ℂ f z) :
    rectangleBoundaryIntegral (fun z => f z / z) a b c d =
      (2 * (Real.pi : ℂ) * I) * f 0 := by
  have hz : (0 : ℂ) ∈ uIcc a b ×ℂ uIcc c d := by
    simp only [mem_reProdIm, zero_re, zero_im, uIcc_of_le (ha.trans hb).le,
      uIcc_of_le (hc.trans hd).le, mem_Icc]
    exact ⟨⟨ha.le, hb.le⟩, hc.le, hd.le⟩
  let g := dslope f 0
  have hg : ∀ z ∈ uIcc a b ×ℂ uIcc c d, AnalyticAt ℂ g z :=
    fun z hz' => analytic_dslope_of_analytic f 0 z (hf 0 hz) (hf z hz')
  have hn (z : ℂ) (hz' : z ∈ contourRectangleBoundary a b c d) : z ≠ 0 :=
    contourBoundary_ne_interior ⟨ha, hb, hc, hd⟩ hz'
  have hgI : RectangleIntegrable g a b c d := rectangleIntegrable_of_continuousOn
    (fun z hz' => (hg z ⟨hz'.1, hz'.2.1⟩).continuousAt.continuousWithinAt)
  have hpI : RectangleIntegrable (fun z => f 0 * (z - 0)⁻¹) a b c d :=
    (rectangleIntegrable_sub_inv ⟨ha, hb, hc, hd⟩).const_mul _
  have he : rectangleBoundaryIntegral (fun z => f z / z) a b c d =
      rectangleBoundaryIntegral (fun z => g z + f 0 * (z - 0)⁻¹) a b c d := by
    apply rectangleBoundaryIntegral_congr
    intro z hz'
    dsimp [g]
    rw [dslope_of_ne f (hn z hz')]
    simp only [slope, smul_eq_mul, vsub_eq_sub, sub_zero]
    ring
  rw [he, rectangleBoundaryIntegral_add hgI hpI, rectangleBoundaryIntegral_eq_zero hg,
    zero_add, rectangleBoundaryIntegral_const_mul,
    rectangleBoundaryIntegral_sub_inv 0 a b c d ha hb hc hd]
  ring

end Ostmann

end OAI
