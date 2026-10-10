import OAI.Geometry.CylinderCovering.Angular.GeneralDefinitions
import OAI.Geometry.CylinderCovering.Convexity.GeneralCapArea

namespace OAI

open Set MeasureTheory
namespace CylinderCovering.AngularGeneral

theorem integralCost_expansion_from_uniform_errors {τ η E : ℝ} {D : Data}
    (hD : Admissible τ η E D) (hη0 : 0 ≤ η) (hη1 : η ≤ 1 / 8)
    (hE : 0 ≤ E) (hτ : τ ^ 2 ≤ 1) (hsmall : E * τ ^ 2 ≤ 1 / 16) :
    |integralCost τ D - (1 / 2 + (2 * η - 1 / 240) * τ ^ 2)| ≤
      2 * (3 * E + 1) * τ ^ 4 := by
  rcases hD with ⟨hN, h0, hN', hnode, hbound, hboundary, hcont, hpos, herr⟩
  have h := GeneralCapArea.general_cap_area_expansion h0 hN'
    (fun j hj => (hnode j hj).le) hcont hη0 hη1 hE hτ hsmall
    (fun j hj q hq => (herr j hj q hq).1)
    (fun j hj q hq => (herr j hj q hq).2.1)
    (fun j hj q hq => (herr j hj q hq).2.2)
  unfold integralCost
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ =>
    ∫ q in D.node j..D.node (j+1),
      (D.radius j q)^2 / Real.sqrt (1+τ^2*((D.alpha j)^2+2*(D.beta j)^2))) D.count]
  exact h

end CylinderCovering.AngularGeneral

end OAI
