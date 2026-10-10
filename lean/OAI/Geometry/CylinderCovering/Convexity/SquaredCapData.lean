import OAI.Geometry.CylinderCovering.Convexity.SquaredCapDataDefinitions
import OAI.Geometry.CylinderCovering.Angular.Caps

namespace OAI

open Set

noncomputable section

namespace AngularCaps

open CylinderCovering.AngularGeneral

theorem withSquaredCaps_admissible {τ η E : ℝ} {D : Data}
    (hη : 0 ≤ η) (hD : Admissible τ η E D) :
    Admissible τ η (max E ((1 / 8 + η) ^ 2)) (withSquaredCaps τ η D) := by
  rcases hD with ⟨hcount, hleft, hright, hinc, hnodes, hboundary, hcont, hpos, herr⟩
  refine ⟨hcount, hleft, hright, hinc, hnodes, hboundary, ?_, ?_, ?_⟩
  · intro j hj
    exact (continuous_squaredRadius τ η).continuousOn
  · intro j hj q hq
    exact squaredRadius_pos hη
  · intro j hj q hq
    have hq' : q ∈ interval D j := hq
    have hqabs : |q| ≤ 1 := abs_le.mpr
      ⟨(abs_le.mp (hnodes j hj.le)).1.trans hq'.1,
        hq'.2.trans (abs_le.mp (hnodes (j + 1) hj)).2⟩
    have hcoeff := herr j hj q hq'
    have hE : E * τ ^ 2 ≤ max E ((1 / 8 + η) ^ 2) * τ ^ 2 :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg τ)
    refine ⟨hcoeff.1.trans hE, hcoeff.2.1.trans hE, ?_⟩
    have hcap := squaredRadius_expansion (τ := τ) hη hqabs
    change |squaredRadius τ η q - (1 / 2 + τ ^ 2 * (d q + η))| ≤ _
    exact hcap.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))

end AngularCaps

end

end OAI
