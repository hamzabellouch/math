import OAI.Analysis.CircleDomains.Selection.PrincipalInversionGerm
import OAI.Analysis.CircleDomains.Sobolev.SmoothSphereCharts
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic

namespace OAI

/-! The actual charts of a principally normalized plane homeomorphism.
The analytic inverse chart follows from its local inverse identity. -/
open Set Filter Function
open scoped Topology ContDiff OnePoint
noncomputable section
namespace CircleDomainRigidity

lemma sphereLocalMap_onePointCongr_infty (F : ℂ ≃ₜ ℂ) :
    sphereLocalMap F.onePointCongr OnePoint.infty = principalInversionGerm F := by
  funext w
  by_cases hw : w = 0
  · subst w
    simp [sphereLocalMap, principalInversionGerm, Homeomorph.onePointCongr_apply,
      chart, chartSymm, sphereInv, finiteCoord]
  · simp only [principalInversionGerm, Function.update_of_ne hw]
    simp only [sphereLocalMap, Homeomorph.onePointCongr_apply, OnePoint.map_infty, OnePoint.map_some, chart_infty_apply,
      chartSymm, ite_true, sphereInv, OnePoint.elim_some, hw, ite_false]
    exact finiteCoord_sphereInv_coe _

lemma analyticAt_inverse_sphereLocalMap_infty
    (e : Sphere ≃ₜ Sphere) (he : e OnePoint.infty = OnePoint.infty)
    (ha : AnalyticAt ℂ (sphereLocalMap e OnePoint.infty) 0)
    (hd : deriv (sphereLocalMap e OnePoint.infty) 0 ≠ 0) :
    AnalyticAt ℂ (sphereLocalMap e.symm OnePoint.infty) 0 := by
  have hei : e.symm OnePoint.infty = OnePoint.infty := by
    apply e.injective
    rw [e.apply_symm_apply, he]
  have hzero : sphereLocalMap e OnePoint.infty 0 = 0 := by
    simp [sphereLocalMap, he, chartSymm, sphereInv, finiteCoord]
  have ht : Tendsto (fun z : ℂ => e (chartSymm OnePoint.infty z)) (𝓝 0) (𝓝 (OnePoint.infty : Sphere)) := by
    have hc : ContinuousAt (fun z : ℂ => e (chartSymm OnePoint.infty z)) 0 :=
      e.continuous.continuousAt.comp (continuous_chartSymm OnePoint.infty).continuousAt
    simpa [chartSymm, sphereInv, he] using hc.tendsto
  have hinv : (sphereLocalMap e.symm OnePoint.infty ∘ sphereLocalMap e OnePoint.infty) =ᶠ[𝓝 0] id := by
    filter_upwards [ht.eventually (eventually_chartSymm_chart OnePoint.infty)] with z hz
    change chart (e.symm OnePoint.infty) (e.symm (chartSymm OnePoint.infty
      (chart (e OnePoint.infty) (e (chartSymm OnePoint.infty z))))) = z
    rw [he, hz, e.symm_apply_apply, hei, chart_chartSymm]
  have hcomp : AnalyticAt ℂ (sphereLocalMap e.symm OnePoint.infty ∘ sphereLocalMap e OnePoint.infty) 0 :=
    analyticAt_id.congr hinv.symm
  simpa only [hzero] using (analyticAt_comp_iff_of_deriv_ne_zero ha hd).mp hcomp

end CircleDomainRigidity

end

end OAI
