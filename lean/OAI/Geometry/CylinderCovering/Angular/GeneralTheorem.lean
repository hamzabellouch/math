import OAI.Geometry.CylinderCovering.Angular.GeneralCoverage
import OAI.Geometry.CylinderCovering.Angular.GeneralCost
import OAI.Geometry.CylinderCovering.Angular.GeneralVolume
import OAI.Geometry.CylinderCovering.Angular.GeneralTriangles

namespace OAI

noncomputable section

namespace CylinderCovering.AngularGeneral

theorem general_cap : Statement := by
  intro η hη0 hη1 E hE
  obtain ⟨δ, hδ, hsmall⟩ := GeneralCapArea.exists_uniform_smallness hη0 hη1 hE
  refine ⟨δ, 2*(3*E+1), hδ, by positivity, ?_⟩
  intro τ hτ hτδ D hD
  obtain ⟨hτhalf, hcover, hτsq, hEsq, hsave⟩ := hsmall τ hτ hτδ
  have harea := totalArea_div_H_eq_integralCost hD
  have hunit : ∀ j < D.count,
      ‖lowerAxis τ D j‖ = 1 ∧ ‖upperAxis τ D j‖ = 1 :=
    fun j _ => ⟨lowerAxis_norm τ D j, upperAxis_norm τ D j⟩
  have hcost := cost_conclusions hD hτ hη0.le (by linarith) hE
    hτsq hEsq hsave hunit harea
  refine ⟨covers_of_admissible hτ hτhalf hE hη0 hη1.le hcover hD,
    ?_, harea, hcost.1, hcost.2.1, hcost.2.2, ?_⟩
  · intro j hj
    exact base_properties τ (hD.2.2.2.2.2.2.1 j hj)
      (fun q hq => (hD.2.2.2.2.2.2.2.1 j hj q hq).le)
  · intro j hj hc
    exact constant_cap_triangular hD hj hc

end CylinderCovering.AngularGeneral

end

end OAI
