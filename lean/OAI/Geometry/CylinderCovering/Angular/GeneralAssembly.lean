import OAI.Geometry.CylinderCovering.Angular.GeneralDefinitions
import OAI.Geometry.CylinderCovering.Convexity.GeneralCapCoverage
import OAI.Geometry.CylinderCovering.Convexity.GeneralCapArea

namespace OAI

noncomputable section
open Set MeasureTheory

namespace CylinderCovering.AngularGeneral

theorem coordinate_cover {τ η E : ℝ} {D : Data}
    (hD : Admissible τ η E D) (hτ : 0 < τ) (hτ1 : τ ≤ 1/2)
    (hE : 0 ≤ E) (hη : 0 < η) (hη1 : η ≤ 1/480)
    (hsmall : (10+4*E)*τ ≤ η)
    {x y t : ℝ} (hx : |x| ≤ 1-t) (hy : |y| ≤ t) :
    (∃ j < D.count, ∃ q ∈ interval D j,
      0 ≤ t-τ*x*D.beta j ∧ t-τ*x*D.beta j ≤ D.radius j q ∧
      y = (t-τ*x*D.beta j)*q+τ*x*D.alpha j) ∨
    (∃ j < D.count, ∃ q ∈ interval D j,
      0 ≤ 1-t+τ*y*D.beta j ∧ 1-t+τ*y*D.beta j ≤ D.radius j q ∧
      x = (1-t+τ*y*D.beta j)*q-τ*y*D.alpha j) := by
  rcases hD with ⟨hn,hnode0,hnoden,hstep,hbound,hL,hcont,hpositive,herror⟩
  obtain ⟨L,hLc,hL0,hL1,hcompat⟩ := hL
  let boundary := fun j => L (D.node j)
  have hb0 : boundary 0 = 0 := by simp [boundary,hnode0,hL0]
  have hbn : boundary D.count = 0 := by simp [boundary,hnoden,hL1]
  have hleft : ∀ j < D.count, D.alpha j-D.node j*D.beta j = boundary j := by
    intro j hj
    exact hcompat j hj (D.node j) ⟨le_rfl,(hstep j hj).le⟩
  have hright : ∀ j < D.count, D.alpha j-D.node (j+1)*D.beta j = boundary (j+1) := by
    intro j hj
    exact hcompat j hj (D.node (j+1)) ⟨(hstep j hj).le,le_rfl⟩
  apply GeneralCap.coordinate_coverage hn D.node D.alpha D.beta boundary D.radius
    hnode0 hnoden hbound hb0 hbn hstep hleft hright hτ hτ1 hE hη hη1 hsmall
  · intro j hj q hq
    exact ⟨(herror j hj q hq).1,(herror j hj q hq).2.1⟩
  · intro j hj q hq
    have hh := (abs_le.mp (herror j hj q hq).2.2).1
    dsimp [profile] at hh
    linarith only [hh]
  · exact hx
  · exact hy

theorem integralCost_expansion {τ η E : ℝ} {D : Data}
    (hD : Admissible τ η E D) (hη : 0 ≤ η) (hη1 : η ≤ 1/8)
    (hE : 0 ≤ E) (hτ : τ^2 ≤ 1) (hsmall : E*τ^2 ≤ 1/16) :
    |integralCost τ D-(1/2+(2*η-1/240)*τ^2)| ≤ 2*(3*E+1)*τ^4 := by
  rcases hD with ⟨hn,hnode0,hnoden,hstep,hbound,hL,hcont,hpositive,herror⟩
  have hh := GeneralCapArea.general_cap_area_expansion hnode0 hnoden
    (fun j hj => (hstep j hj).le) hcont hη hη1 hE hτ hsmall
    (fun j hj q hq => (herror j hj q hq).1)
    (fun j hj q hq => (herror j hj q hq).2.1)
    (fun j hj q hq => (herror j hj q hq).2.2)
  rw [← Fin.sum_univ_eq_sum_range (fun j : ℕ =>
    ∫ q in D.node j..D.node (j+1),
      GeneralCapArea.capDensity τ (D.alpha j) (D.beta j) (D.radius j) q) D.count] at hh
  exact hh

end CylinderCovering.AngularGeneral

end

end OAI
