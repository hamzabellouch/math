import OAI.NumberTheory.Ostmann.ZeroDensity.RieszContourRectangle
import OAI.NumberTheory.Ostmann.ZeroDensity.SmoothContourRegularPart

namespace OAI

/-! # The exact contribution of a real pole to the Riesz rectangle -/

namespace Ostmann

open Complex Filter Set
open scoped Topology Interval

theorem rieszWeight_dslope_analytic (X : ℝ) (hX : 0 < X) (β : ℂ) (hβ : 0 < β.re)
    (s : ℂ) (hs : 0 < s.re) : AnalyticAt ℂ (dslope (rieszContourWeight X) β) s := by
  by_cases he : s = β
  · subst s
    obtain ⟨p, hp⟩ := rieszContourWeight_analyticAt X hX β hβ
    exact ⟨p.fslope, hp.has_fpower_series_dslope_fslope⟩
  · have hh : dslope (rieszContourWeight X) β =ᶠ[𝓝 s]
        (fun z => (z - β)⁻¹ * (rieszContourWeight X z - rieszContourWeight X β)) := by
      filter_upwards [isOpen_ne.mem_nhds he] with z hz
      rw [dslope_of_ne _ hz]
      rfl
    exact (((analyticAt_id.sub analyticAt_const).inv (sub_ne_zero.mpr he)).mul
      ((rieszContourWeight_analyticAt X hX s hs).sub analyticAt_const)).congr hh.symm

theorem riesz_pole_rectangle (X : ℝ) (hX : 0 < X) (β a b c d : ℝ)
    (ha : 0 < a) (hab : a < β) (hβb : β < b) (hc : c < 0) (hd : 0 < d) :
    rectangleBoundaryIntegral (fun s => rieszContourWeight X s / (s - (β : ℂ))) a b c d =
      (2 * (Real.pi : ℂ) * I) * rieszContourWeight X (β : ℂ) := by
  let W := rieszContourWeight X
  let g := dslope W (β : ℂ)
  have hg : ∀ s ∈ uIcc a b ×ℂ uIcc c d, AnalyticAt ℂ g s := by
    intro s hs
    apply rieszWeight_dslope_analytic X hX (β : ℂ) (by simpa using ha.trans hab) s
    exact ha.trans_le ((uIcc_of_le (hab.trans hβb).le) ▸ hs.1).1
  have hnot (s : ℂ) (hs : s ∈ contourRectangleBoundary a b c d) : s ≠ (β : ℂ) :=
    contourBoundary_ne_interior ⟨hab, hβb, hc, hd⟩ hs
  have hgI : RectangleIntegrable g a b c d := rectangleIntegrable_of_continuousOn
    (fun s hs => (hg s ⟨hs.1, hs.2.1⟩).continuousAt.continuousWithinAt)
  have hpI : RectangleIntegrable (fun s => W (β : ℂ) * (s - (β : ℂ))⁻¹) a b c d :=
    (rectangleIntegrable_sub_inv ⟨hab, hβb, hc, hd⟩).const_mul _
  have heq : rectangleBoundaryIntegral (fun s => W s / (s - (β : ℂ))) a b c d =
      rectangleBoundaryIntegral (fun s => g s + W (β : ℂ) * (s - (β : ℂ))⁻¹) a b c d := by
    apply rectangleBoundaryIntegral_congr
    intro s hs
    dsimp [g]
    rw [dslope_of_ne _ (hnot s hs)]
    simp only [slope, smul_eq_mul, vsub_eq_sub]
    ring
  rw [heq, rectangleBoundaryIntegral_add hgI hpI,
    rectangleBoundaryIntegral_eq_zero hg, zero_add, rectangleBoundaryIntegral_const_mul,
    rectangleBoundaryIntegral_sub_inv (β : ℂ) a b c d hab hβb hc hd]
  ring

end Ostmann

end OAI
